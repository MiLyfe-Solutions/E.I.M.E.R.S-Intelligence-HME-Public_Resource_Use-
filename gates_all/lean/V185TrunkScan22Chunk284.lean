import V185TrunkScan22Chunk283

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2534505 : List Nat := [1, 2, 1, 1, 1, 6, 4, 6]
def baseStart_2534505 : Nat := 118140960795 + 2534505 * 2 ^ 59
def prefixEnd_2534505 : Nat := 4983230072969 + 3 ^ 40 * 2534505 * 2
def baseEnd_2534505 : Nat := 96401428609163812683817

theorem tailTrace_2534505 : CollatzResearch.WordTrace tailWord_2534505 prefixEnd_2534505 96401428609163812683817 := by
  unfold tailWord_2534505
  simp only [CollatzResearch.WordTrace]
  refine ⟨92440991682928718837444969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61627327788619145891629979 92440991682928718837444969)
  ·
    refine ⟨69330743762196539128083727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92440991682928718837444969 69330743762196539128083727)
    ·
      refine ⟨103996115643294808692125591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69330743762196539128083727 103996115643294808692125591)
      ·
        refine ⟨155994173464942213038188387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103996115643294808692125591 155994173464942213038188387)
        ·
          refine ⟨233991260197413319557282581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155994173464942213038188387 233991260197413319557282581)
          ·
            refine ⟨10968340321753749354247621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 233991260197413319557282581 10968340321753749354247621)
            ·
              refine ⟨2056563810328828003921429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10968340321753749354247621 2056563810328828003921429)
              ·
                refine ⟨96401428609163812683817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2056563810328828003921429 96401428609163812683817)
                ·
                  rfl

theorem cell22_2534505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 6].length) (baseStart_2534505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534505 prefixEnd_2534505 := by exact prefixLift 2534505
  have htrace : WordTrace (prefixWord ++ tailWord_2534505) baseStart_2534505 baseEnd_2534505 := by
    simpa [prefixWord, tailWord_2534505, baseEnd_2534505] using wordTrace_append hprefix tailTrace_2534505
  have hstable : (prefixWord ++ tailWord_2534505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534505).length < 2 ^ (prefixWord ++ tailWord_2534505).sum := by decide
  have hdescent : baseEnd_2534505 < baseStart_2534505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534520 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 5, 3]
def baseStart_2534520 : Nat := 118140960795 + 2534520 * 2 ^ 59
def prefixEnd_2534520 : Nat := 4983230072969 + 3 ^ 40 * 2534520 * 2
def baseEnd_2534520 : Nat := 867617992289019275029307

theorem tailTrace_2534520 : CollatzResearch.WordTrace tailWord_2534520 prefixEnd_2534520 867617992289019275029307 := by
  unfold tailWord_2534520
  simp only [CollatzResearch.WordTrace]
  refine ⟨46220769388937188199620507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61627692518582917599494009 46220769388937188199620507)
  ·
    refine ⟨69331154083405782299430761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46220769388937188199620507 69331154083405782299430761)
    ·
      refine ⟨51998365562554336724573071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69331154083405782299430761 51998365562554336724573071)
      ·
        refine ⟨77997548343831505086859607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51998365562554336724573071 77997548343831505086859607)
        ·
          refine ⟨116996322515747257630289411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77997548343831505086859607 116996322515747257630289411)
          ·
            refine ⟨175494483773620886445434117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116996322515747257630289411 175494483773620886445434117)
            ·
              refine ⟨32905215707553916208518897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175494483773620886445434117 32905215707553916208518897)
              ·
                refine ⟨24678911780665437156389173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32905215707553916208518897 24678911780665437156389173)
                ·
                  refine ⟨2313647979437384733411485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24678911780665437156389173 2313647979437384733411485)
                  ·
                    refine ⟨867617992289019275029307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2313647979437384733411485 867617992289019275029307)
                    ·
                      rfl

theorem cell22_2534520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_2534520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534520 prefixEnd_2534520 := by exact prefixLift 2534520
  have htrace : WordTrace (prefixWord ++ tailWord_2534520) baseStart_2534520 baseEnd_2534520 := by
    simpa [prefixWord, tailWord_2534520, baseEnd_2534520] using wordTrace_append hprefix tailTrace_2534520
  have hstable : (prefixWord ++ tailWord_2534520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534520).length < 2 ^ (prefixWord ++ tailWord_2534520).sum := by decide
  have hdescent : baseEnd_2534520 < baseStart_2534520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534537 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 3, 3]
def baseStart_2534537 : Nat := 118140960795 + 2534537 * 2 ^ 59
def prefixEnd_2534537 : Nat := 4983230072969 + 3 ^ 40 * 2534537 * 2
def baseEnd_2534537 : Nat := 867623811736436897354255

theorem tailTrace_2534537 : CollatzResearch.WordTrace tailWord_2534537 prefixEnd_2534537 867623811736436897354255 := by
  unfold tailWord_2534537
  simp only [CollatzResearch.WordTrace]
  refine ⟨92442158818812788302609865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61628105879208525535073243 92442158818812788302609865)
  ·
    refine ⟨69331619114109591226957399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92442158818812788302609865 69331619114109591226957399)
    ·
      refine ⟨103997428671164386840436099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69331619114109591226957399 103997428671164386840436099)
      ·
        refine ⟨155996143006746580260654149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103997428671164386840436099 155996143006746580260654149)
        ·
          refine ⟨29249276813764983798872653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155996143006746580260654149 29249276813764983798872653)
          ·
            refine ⟨10968478805161868924577245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29249276813764983798872653 10968478805161868924577245)
            ·
              refine ⟨4113179551935700846716467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10968478805161868924577245 4113179551935700846716467)
              ·
                refine ⟨6169769327903551270074701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4113179551935700846716467 6169769327903551270074701)
                ·
                  refine ⟨2313663497963831726278013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6169769327903551270074701 2313663497963831726278013)
                  ·
                    refine ⟨867623811736436897354255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2313663497963831726278013 867623811736436897354255)
                    ·
                      rfl

theorem cell22_2534537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 3].length) (baseStart_2534537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534537 prefixEnd_2534537 := by exact prefixLift 2534537
  have htrace : WordTrace (prefixWord ++ tailWord_2534537) baseStart_2534537 baseEnd_2534537 := by
    simpa [prefixWord, tailWord_2534537, baseEnd_2534537] using wordTrace_append hprefix tailTrace_2534537
  have hstable : (prefixWord ++ tailWord_2534537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534537).length < 2 ^ (prefixWord ++ tailWord_2534537).sum := by decide
  have hdescent : baseEnd_2534537 < baseStart_2534537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534588 : List Nat := [2, 2, 2, 3, 2, 3, 2, 2, 1, 3]
def baseStart_2534588 : Nat := 118140960795 + 2534588 * 2 ^ 59
def prefixEnd_2534588 : Nat := 4983230072969 + 3 ^ 40 * 2534588 * 2
def baseEnd_2534588 : Nat := 867641270078689764329099

theorem tailTrace_2534588 : CollatzResearch.WordTrace tailWord_2534588 prefixEnd_2534588 867641270078689764329099 := by
  unfold tailWord_2534588
  simp only [CollatzResearch.WordTrace]
  refine ⟨46222009470814012006358209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61629345961085349341810945 46222009470814012006358209)
  ·
    refine ⟨34666507103110509004768657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46222009470814012006358209 34666507103110509004768657)
    ·
      refine ⟨25999880327332881753576493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34666507103110509004768657 25999880327332881753576493)
      ·
        refine ⟨9749955122749830657591185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25999880327332881753576493 9749955122749830657591185)
        ·
          refine ⟨7312466342062372993193389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9749955122749830657591185 7312466342062372993193389)
          ·
            refine ⟨2742174878273389872447521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7312466342062372993193389 2742174878273389872447521)
            ·
              refine ⟨2056631158705042404335641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742174878273389872447521 2056631158705042404335641)
              ·
                refine ⟨1542473369028781803251731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2056631158705042404335641 1542473369028781803251731)
                ·
                  refine ⟨2313710053543172704877597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542473369028781803251731 2313710053543172704877597)
                  ·
                    refine ⟨867641270078689764329099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2313710053543172704877597 867641270078689764329099)
                    ·
                      rfl

theorem cell22_2534588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_2534588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534588 prefixEnd_2534588 := by exact prefixLift 2534588
  have htrace : WordTrace (prefixWord ++ tailWord_2534588) baseStart_2534588 baseEnd_2534588 := by
    simpa [prefixWord, tailWord_2534588, baseEnd_2534588] using wordTrace_append hprefix tailTrace_2534588
  have hstable : (prefixWord ++ tailWord_2534588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534588).length < 2 ^ (prefixWord ++ tailWord_2534588).sum := by decide
  have hdescent : baseEnd_2534588 < baseStart_2534588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534706 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_2534706 : Nat := 118140960795 + 2534706 * 2 ^ 59
def prefixEnd_2534706 : Nat := 4983230072969 + 3 ^ 40 * 2534706 * 2
def baseEnd_2534706 : Nat := 867681663890176789878737

theorem tailTrace_2534706 : CollatzResearch.WordTrace tailWord_2534706 prefixEnd_2534706 867681663890176789878737 := by
  unfold tailWord_2534706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23112080688800132541377993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61632215170133686777007981 23112080688800132541377993)
  ·
    refine ⟨17334060516600099406033495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23112080688800132541377993 17334060516600099406033495)
    ·
      refine ⟨26001090774900149109050243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17334060516600099406033495 26001090774900149109050243)
      ·
        refine ⟨39001636162350223663575365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26001090774900149109050243 39001636162350223663575365)
        ·
          refine ⟨7312806780440666936920381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39001636162350223663575365 7312806780440666936920381)
          ·
            refine ⟨2742302542665250101345143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7312806780440666936920381 2742302542665250101345143)
            ·
              refine ⟨4113453813997875152017715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2742302542665250101345143 4113453813997875152017715)
              ·
                refine ⟨6170180720996812728026573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4113453813997875152017715 6170180720996812728026573)
                ·
                  refine ⟨2313817770373804773009965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6170180720996812728026573 2313817770373804773009965)
                  ·
                    refine ⟨867681663890176789878737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2313817770373804773009965 867681663890176789878737)
                    ·
                      rfl

theorem cell22_2534706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_2534706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534706 prefixEnd_2534706 := by exact prefixLift 2534706
  have htrace : WordTrace (prefixWord ++ tailWord_2534706) baseStart_2534706 baseEnd_2534706 := by
    simpa [prefixWord, tailWord_2534706, baseEnd_2534706] using wordTrace_append hprefix tailTrace_2534706
  have hstable : (prefixWord ++ tailWord_2534706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534706).length < 2 ^ (prefixWord ++ tailWord_2534706).sum := by decide
  have hdescent : baseEnd_2534706 < baseStart_2534706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534719 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 5]
def baseStart_2534719 : Nat := 118140960795 + 2534719 * 2 ^ 59
def prefixEnd_2534719 : Nat := 4983230072969 + 3 ^ 40 * 2534719 * 2
def baseEnd_2534719 : Nat := 289228704685283029767899

theorem tailTrace_2534719 : CollatzResearch.WordTrace tailWord_2534719 prefixEnd_2534719 289228704685283029767899 := by
  unfold tailWord_2534719
  simp only [CollatzResearch.WordTrace]
  refine ⟨92448796904153433385735211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61632531269435622257156807 92448796904153433385735211)
  ·
    refine ⟨138673195356230150078602817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92448796904153433385735211 138673195356230150078602817)
    ·
      refine ⟨104004896517172612558952113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138673195356230150078602817 104004896517172612558952113)
      ·
        refine ⟨78003672387879459419214085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104004896517172612558952113 78003672387879459419214085)
        ·
          refine ⟨14625688572727398641102641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78003672387879459419214085 14625688572727398641102641)
          ·
            refine ⟨10969266429545548980826981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14625688572727398641102641 10969266429545548980826981)
            ·
              refine ⟨2056737455539790433905059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10969266429545548980826981 2056737455539790433905059)
              ·
                refine ⟨3085106183309685650857589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056737455539790433905059 3085106183309685650857589)
                ·
                  refine ⟨289228704685283029767899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3085106183309685650857589 289228704685283029767899)
                  ·
                    rfl

theorem cell22_2534719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 5].length) (baseStart_2534719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534719 prefixEnd_2534719 := by exact prefixLift 2534719
  have htrace : WordTrace (prefixWord ++ tailWord_2534719) baseStart_2534719 baseEnd_2534719 := by
    simpa [prefixWord, tailWord_2534719, baseEnd_2534719] using wordTrace_append hprefix tailTrace_2534719
  have hstable : (prefixWord ++ tailWord_2534719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534719).length < 2 ^ (prefixWord ++ tailWord_2534719).sum := by decide
  have hdescent : baseEnd_2534719 < baseStart_2534719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534777 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_2534777 : Nat := 118140960795 + 2534777 * 2 ^ 59
def prefixEnd_2534777 : Nat := 4983230072969 + 3 ^ 40 * 2534777 * 2
def baseEnd_2534777 : Nat := 867705968641156271353519

theorem tailTrace_2534777 : CollatzResearch.WordTrace tailWord_2534777 prefixEnd_2534777 867705968641156271353519 := by
  unfold tailWord_2534777
  simp only [CollatzResearch.WordTrace]
  refine ⟨92450912337943309291346585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61633941558628872860897723 92450912337943309291346585)
  ·
    refine ⟨69338184253457481968509939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92450912337943309291346585 69338184253457481968509939)
    ·
      refine ⟨104007276380186222952764909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69338184253457481968509939 104007276380186222952764909)
      ·
        refine ⟨39002728642569833607286841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104007276380186222952764909 39002728642569833607286841)
        ·
          refine ⟨29252046481927375205465131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39002728642569833607286841 29252046481927375205465131)
          ·
            refine ⟨43878069722891062808197697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29252046481927375205465131 43878069722891062808197697)
            ·
              refine ⟨32908552292168297106148273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43878069722891062808197697 32908552292168297106148273)
              ·
                refine ⟨24681414219126222829611205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32908552292168297106148273 24681414219126222829611205)
                ·
                  refine ⟨4627765166086166780552101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24681414219126222829611205 4627765166086166780552101)
                  ·
                    refine ⟨867705968641156271353519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4627765166086166780552101 867705968641156271353519)
                    ·
                      rfl

theorem cell22_2534777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_2534777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534777 prefixEnd_2534777 := by exact prefixLift 2534777
  have htrace : WordTrace (prefixWord ++ tailWord_2534777) baseStart_2534777 baseEnd_2534777 := by
    simpa [prefixWord, tailWord_2534777, baseEnd_2534777] using wordTrace_append hprefix tailTrace_2534777
  have hstable : (prefixWord ++ tailWord_2534777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534777).length < 2 ^ (prefixWord ++ tailWord_2534777).sum := by decide
  have hdescent : baseEnd_2534777 < baseStart_2534777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534779 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 2, 3]
def baseStart_2534779 : Nat := 118140960795 + 2534779 * 2 ^ 59
def prefixEnd_2534779 : Nat := 4983230072969 + 3 ^ 40 * 2534779 * 2
def baseEnd_2534779 : Nat := 867706653282028932803513

theorem tailTrace_2534779 : CollatzResearch.WordTrace tailWord_2534779 prefixEnd_2534779 867706653282028932803513 := by
  unfold tailWord_2534779
  simp only [CollatzResearch.WordTrace]
  refine ⟨92450985283936063632919391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61633990189290709088612927 92450985283936063632919391)
  ·
    refine ⟨138676477925904095449379087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92450985283936063632919391 138676477925904095449379087)
    ·
      refine ⟨208014716888856143174068631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138676477925904095449379087 208014716888856143174068631)
      ·
        refine ⟨312022075333284214761102947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208014716888856143174068631 312022075333284214761102947)
        ·
          refine ⟨468033112999926322141654421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312022075333284214761102947 468033112999926322141654421)
          ·
            refine ⟨21939052171871546350390051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 468033112999926322141654421 21939052171871546350390051)
            ·
              refine ⟨32908578257807319525585077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21939052171871546350390051 32908578257807319525585077)
              ·
                refine ⟨3085179211669436205523601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32908578257807319525585077 3085179211669436205523601)
                ·
                  refine ⟨2313884408752077154142701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3085179211669436205523601 2313884408752077154142701)
                  ·
                    refine ⟨867706653282028932803513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2313884408752077154142701 867706653282028932803513)
                    ·
                      rfl

theorem cell22_2534779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 3].length) (baseStart_2534779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534779 prefixEnd_2534779 := by exact prefixLift 2534779
  have htrace : WordTrace (prefixWord ++ tailWord_2534779) baseStart_2534779 baseEnd_2534779 := by
    simpa [prefixWord, tailWord_2534779, baseEnd_2534779] using wordTrace_append hprefix tailTrace_2534779
  have hstable : (prefixWord ++ tailWord_2534779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534779).length < 2 ^ (prefixWord ++ tailWord_2534779).sum := by decide
  have hdescent : baseEnd_2534779 < baseStart_2534779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534798 : List Nat := [4, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_2534798 : Nat := 118140960795 + 2534798 * 2 ^ 59
def prefixEnd_2534798 : Nat := 4983230072969 + 3 ^ 40 * 2534798 * 2
def baseEnd_2534798 : Nat := 289237719123439738859485

theorem tailTrace_2534798 : CollatzResearch.WordTrace tailWord_2534798 prefixEnd_2534798 289237719123439738859485 := by
  unfold tailWord_2534798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11556459783858403734732631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61634452180578153251907365 11556459783858403734732631)
  ·
    refine ⟨17334689675787605602098947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11556459783858403734732631 17334689675787605602098947)
    ·
      refine ⟨26002034513681408403148421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17334689675787605602098947 26002034513681408403148421)
      ·
        refine ⟨4875381471315264075590329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26002034513681408403148421 4875381471315264075590329)
        ·
          refine ⟨3656536103486448056692747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4875381471315264075590329 3656536103486448056692747)
          ·
            refine ⟨5484804155229672085039121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3656536103486448056692747 5484804155229672085039121)
            ·
              refine ⟨4113603116422254063779341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5484804155229672085039121 4113603116422254063779341)
              ·
                refine ⟨1542601168658345273917253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4113603116422254063779341 1542601168658345273917253)
                ·
                  refine ⟨289237719123439738859485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542601168658345273917253 289237719123439738859485)
                  ·
                    rfl

theorem cell22_2534798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_2534798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534798 prefixEnd_2534798 := by exact prefixLift 2534798
  have htrace : WordTrace (prefixWord ++ tailWord_2534798) baseStart_2534798 baseEnd_2534798 := by
    simpa [prefixWord, tailWord_2534798, baseEnd_2534798] using wordTrace_append hprefix tailTrace_2534798
  have hstable : (prefixWord ++ tailWord_2534798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534798).length < 2 ^ (prefixWord ++ tailWord_2534798).sum := by decide
  have hdescent : baseEnd_2534798 < baseStart_2534798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534813 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_2534813 : Nat := 118140960795 + 2534813 * 2 ^ 59
def prefixEnd_2534813 : Nat := 4983230072969 + 3 ^ 40 * 2534813 * 2
def baseEnd_2534813 : Nat := 867718292176864177453409

theorem tailTrace_2534813 : CollatzResearch.WordTrace tailWord_2534813 prefixEnd_2534813 867718292176864177453409 := by
  unfold tailWord_2534813
  simp only [CollatzResearch.WordTrace]
  refine ⟨92452225365812887439657093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61634816910541924959771395 92452225365812887439657093)
  ·
    refine ⟨17334792256089916394935705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92452225365812887439657093 17334792256089916394935705)
    ·
      refine ⟨13001094192067437296201779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17334792256089916394935705 13001094192067437296201779)
      ·
        refine ⟨19501641288101155944302669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13001094192067437296201779 19501641288101155944302669)
        ·
          refine ⟨7313115483037933479113501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19501641288101155944302669 7313115483037933479113501)
          ·
            refine ⟨2742418306139225054667563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7313115483037933479113501 2742418306139225054667563)
            ·
              refine ⟨4113627459208837582001345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2742418306139225054667563 4113627459208837582001345)
              ·
                refine ⟨3085220594406628186501009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4113627459208837582001345 3085220594406628186501009)
                ·
                  refine ⟨2313915445804971139875757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3085220594406628186501009 2313915445804971139875757)
                  ·
                    refine ⟨867718292176864177453409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2313915445804971139875757 867718292176864177453409)
                    ·
                      rfl

theorem cell22_2534813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_2534813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534813 prefixEnd_2534813 := by exact prefixLift 2534813
  have htrace : WordTrace (prefixWord ++ tailWord_2534813) baseStart_2534813 baseEnd_2534813 := by
    simpa [prefixWord, tailWord_2534813, baseEnd_2534813] using wordTrace_append hprefix tailTrace_2534813
  have hstable : (prefixWord ++ tailWord_2534813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534813).length < 2 ^ (prefixWord ++ tailWord_2534813).sum := by decide
  have hdescent : baseEnd_2534813 < baseStart_2534813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534858 : List Nat := [3, 1, 2, 1, 2, 3, 3, 3, 1, 3]
def baseStart_2534858 : Nat := 118140960795 + 2534858 * 2 ^ 59
def prefixEnd_2534858 : Nat := 4983230072969 + 3 ^ 40 * 2534858 * 2
def baseEnd_2534858 : Nat := 867733696596499060078271

theorem tailTrace_2534858 : CollatzResearch.WordTrace tailWord_2534858 prefixEnd_2534858 867733696596499060078271 := by
  unfold tailWord_2534858
  simp only [CollatzResearch.WordTrace]
  refine ⟨23113466662662465031261307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61635911100433240083363485 23113466662662465031261307)
  ·
    refine ⟨34670199993993697546891961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23113466662662465031261307 34670199993993697546891961)
    ·
      refine ⟨26002649995495273160168971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34670199993993697546891961 26002649995495273160168971)
      ·
        refine ⟨39003974993242909740253457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26002649995495273160168971 39003974993242909740253457)
        ·
          refine ⟨29252981244932182305190093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39003974993242909740253457 29252981244932182305190093)
          ·
            refine ⟨10969867966849568364446285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29252981244932182305190093 10969867966849568364446285)
            ·
              refine ⟨4113700487568588136667357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10969867966849568364446285 4113700487568588136667357)
              ·
                refine ⟨1542637682838220551250259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4113700487568588136667357 1542637682838220551250259)
                ·
                  refine ⟨2313956524257330826875389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542637682838220551250259 2313956524257330826875389)
                  ·
                    refine ⟨867733696596499060078271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2313956524257330826875389 867733696596499060078271)
                    ·
                      rfl

theorem cell22_2534858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_2534858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534858 prefixEnd_2534858 := by exact prefixLift 2534858
  have htrace : WordTrace (prefixWord ++ tailWord_2534858) baseStart_2534858 baseEnd_2534858 := by
    simpa [prefixWord, tailWord_2534858, baseEnd_2534858] using wordTrace_append hprefix tailTrace_2534858
  have hstable : (prefixWord ++ tailWord_2534858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534858).length < 2 ^ (prefixWord ++ tailWord_2534858).sum := by decide
  have hdescent : baseEnd_2534858 < baseStart_2534858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534929 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_2534929 : Nat := 118140960795 + 2534929 * 2 ^ 59
def prefixEnd_2534929 : Nat := 4983230072969 + 3 ^ 40 * 2534929 * 2
def baseEnd_2534929 : Nat := 867758001347478541553053

theorem tailTrace_2534929 : CollatzResearch.WordTrace tailWord_2534929 prefixEnd_2534929 867758001347478541553053 := by
  unfold tailWord_2534929
  simp only [CollatzResearch.WordTrace]
  refine ⟨92456456233392639250879841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61637637488928426167253227 92456456233392639250879841)
  ·
    refine ⟨69342342175044479438159881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92456456233392639250879841 69342342175044479438159881)
    ·
      refine ⟨52006756631283359578619911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69342342175044479438159881 52006756631283359578619911)
      ·
        refine ⟨78010134946925039367929867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52006756631283359578619911 78010134946925039367929867)
        ·
          refine ⟨117015202420387559051894801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78010134946925039367929867 117015202420387559051894801)
          ·
            refine ⟨87761401815290669288921101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117015202420387559051894801 87761401815290669288921101)
            ·
              refine ⟨32910525680734000983345413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87761401815290669288921101 32910525680734000983345413)
              ·
                refine ⟨6170723565137625184377265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32910525680734000983345413 6170723565137625184377265)
                ·
                  refine ⟨4628042673853218888282949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6170723565137625184377265 4628042673853218888282949)
                  ·
                    refine ⟨867758001347478541553053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628042673853218888282949 867758001347478541553053)
                    ·
                      rfl

theorem cell22_2534929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_2534929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534929 prefixEnd_2534929 := by exact prefixLift 2534929
  have htrace : WordTrace (prefixWord ++ tailWord_2534929) baseStart_2534929 baseEnd_2534929 := by
    simpa [prefixWord, tailWord_2534929, baseEnd_2534929] using wordTrace_append hprefix tailTrace_2534929
  have hstable : (prefixWord ++ tailWord_2534929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534929).length < 2 ^ (prefixWord ++ tailWord_2534929).sum := by decide
  have hdescent : baseEnd_2534929 < baseStart_2534929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534931 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 2, 3]
def baseStart_2534931 : Nat := 118140960795 + 2534931 * 2 ^ 59
def prefixEnd_2534931 : Nat := 4983230072969 + 3 ^ 40 * 2534931 * 2
def baseEnd_2534931 : Nat := 867758685988351203003047

theorem tailTrace_2534931 : CollatzResearch.WordTrace tailWord_2534931 prefixEnd_2534931 867758685988351203003047 := by
  unfold tailWord_2534931
  simp only [CollatzResearch.WordTrace]
  refine ⟨92456529179385393592452647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61637686119590262394968431 92456529179385393592452647)
  ·
    refine ⟨138684793769078090388678971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92456529179385393592452647 138684793769078090388678971)
    ·
      refine ⟨208027190653617135583018457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138684793769078090388678971 208027190653617135583018457)
      ·
        refine ⟨156020392990212851687263843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208027190653617135583018457 156020392990212851687263843)
        ·
          refine ⟨234030589485319277530895765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156020392990212851687263843 234030589485319277530895765)
          ·
            refine ⟨10970183882124341134260739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 234030589485319277530895765 10970183882124341134260739)
            ·
              refine ⟨16455275823186511701391109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10970183882124341134260739 16455275823186511701391109)
              ·
                refine ⟨3085364216847470944010833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16455275823186511701391109 3085364216847470944010833)
                ·
                  refine ⟨2314023162635603208008125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3085364216847470944010833 2314023162635603208008125)
                  ·
                    refine ⟨867758685988351203003047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314023162635603208008125 867758685988351203003047)
                    ·
                      rfl

theorem cell22_2534931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 3].length) (baseStart_2534931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534931 prefixEnd_2534931 := by exact prefixLift 2534931
  have htrace : WordTrace (prefixWord ++ tailWord_2534931) baseStart_2534931 baseEnd_2534931 := by
    simpa [prefixWord, tailWord_2534931, baseEnd_2534931] using wordTrace_append hprefix tailTrace_2534931
  have hstable : (prefixWord ++ tailWord_2534931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534931).length < 2 ^ (prefixWord ++ tailWord_2534931).sum := by decide
  have hdescent : baseEnd_2534931 < baseStart_2534931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534933 : List Nat := [1, 3, 2, 1, 3, 2, 4, 2, 4]
def baseStart_2534933 : Nat := 118140960795 + 2534933 * 2 ^ 59
def prefixEnd_2534933 : Nat := 4983230072969 + 3 ^ 40 * 2534933 * 2
def baseEnd_2534933 : Nat := 289253123543074621484347

theorem tailTrace_2534933 : CollatzResearch.WordTrace tailWord_2534933 prefixEnd_2534933 289253123543074621484347 := by
  unfold tailWord_2534933
  simp only [CollatzResearch.WordTrace]
  refine ⟨92456602125378147934025453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61637734750252098622683635 92456602125378147934025453)
  ·
    refine ⟨34671225797016805475259545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92456602125378147934025453 34671225797016805475259545)
    ·
      refine ⟨26003419347762604106444659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34671225797016805475259545 26003419347762604106444659)
      ·
        refine ⟨39005129021643906159666989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26003419347762604106444659 39005129021643906159666989)
        ·
          refine ⟨14626923383116464809875121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39005129021643906159666989 14626923383116464809875121)
          ·
            refine ⟨10970192537337348607406341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14626923383116464809875121 10970192537337348607406341)
            ·
              refine ⟨2056911100750752863888689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10970192537337348607406341 2056911100750752863888689)
              ·
                refine ⟨1542683325563064647916517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2056911100750752863888689 1542683325563064647916517)
                ·
                  refine ⟨289253123543074621484347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542683325563064647916517 289253123543074621484347)
                  ·
                    rfl

theorem cell22_2534933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_2534933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534933 prefixEnd_2534933 := by exact prefixLift 2534933
  have htrace : WordTrace (prefixWord ++ tailWord_2534933) baseStart_2534933 baseEnd_2534933 := by
    simpa [prefixWord, tailWord_2534933, baseEnd_2534933] using wordTrace_append hprefix tailTrace_2534933
  have hstable : (prefixWord ++ tailWord_2534933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534933).length < 2 ^ (prefixWord ++ tailWord_2534933).sum := by decide
  have hdescent : baseEnd_2534933 < baseStart_2534933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534993 : List Nat := [1, 2, 2, 1, 3, 2, 1, 6, 1, 3]
def baseStart_2534993 : Nat := 118140960795 + 2534993 * 2 ^ 59
def prefixEnd_2534993 : Nat := 4983230072969 + 3 ^ 40 * 2534993 * 2
def baseEnd_2534993 : Nat := 867779909855403707952857

theorem tailTrace_2534993 : CollatzResearch.WordTrace tailWord_2534993 prefixEnd_2534993 867779909855403707952857 := by
  unfold tailWord_2534993
  simp only [CollatzResearch.WordTrace]
  refine ⟨92458790505160778181209633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61639193670107185454139755 92458790505160778181209633)
  ·
    refine ⟨69344092878870583635907225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92458790505160778181209633 69344092878870583635907225)
    ·
      refine ⟨52008069659152937726930419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69344092878870583635907225 52008069659152937726930419)
      ·
        refine ⟨78012104488729406590395629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52008069659152937726930419 78012104488729406590395629)
        ·
          refine ⟨29254539183273527471398361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78012104488729406590395629 29254539183273527471398361)
          ·
            refine ⟨21940904387455145603548771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29254539183273527471398361 21940904387455145603548771)
            ·
              refine ⟨32911356581182718405323157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21940904387455145603548771 32911356581182718405323157)
              ·
                refine ⟨1542719839742939925249523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32911356581182718405323157 1542719839742939925249523)
                ·
                  refine ⟨2314079759614409887874285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542719839742939925249523 2314079759614409887874285)
                  ·
                    refine ⟨867779909855403707952857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314079759614409887874285 867779909855403707952857)
                    ·
                      rfl

theorem cell22_2534993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_2534993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534993 prefixEnd_2534993 := by exact prefixLift 2534993
  have htrace : WordTrace (prefixWord ++ tailWord_2534993) baseStart_2534993 baseEnd_2534993 := by
    simpa [prefixWord, tailWord_2534993, baseEnd_2534993] using wordTrace_append hprefix tailTrace_2534993
  have hstable : (prefixWord ++ tailWord_2534993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534993).length < 2 ^ (prefixWord ++ tailWord_2534993).sum := by decide
  have hdescent : baseEnd_2534993 < baseStart_2534993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535019 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 7, 4]
def baseStart_2535019 : Nat := 118140960795 + 2535019 * 2 ^ 59
def prefixEnd_2535019 : Nat := 4983230072969 + 3 ^ 40 * 2535019 * 2
def baseEnd_2535019 : Nat := 867788810186748306802777

theorem tailTrace_2535019 : CollatzResearch.WordTrace tailWord_2535019 prefixEnd_2535019 867788810186748306802777 := by
  unfold tailWord_2535019
  simp only [CollatzResearch.WordTrace]
  refine ⟨92459738803066584621656111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61639825868711056414437407 92459738803066584621656111)
  ·
    refine ⟨138689608204599876932484167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92459738803066584621656111 138689608204599876932484167)
    ·
      refine ⟨208034412306899815398726251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138689608204599876932484167 208034412306899815398726251)
      ·
        refine ⟨312051618460349723098089377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208034412306899815398726251 312051618460349723098089377)
        ·
          refine ⟨234038713845262292323567033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312051618460349723098089377 234038713845262292323567033)
          ·
            refine ⟨175529035383946719242675275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234038713845262292323567033 175529035383946719242675275)
            ·
              refine ⟨263293553075920078864012913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175529035383946719242675275 263293553075920078864012913)
              ·
                refine ⟨197470164806940059148009685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263293553075920078864012913 197470164806940059148009685)
                ·
                  refine ⟨4628206987662657636281477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 197470164806940059148009685 4628206987662657636281477)
                  ·
                    refine ⟨867788810186748306802777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628206987662657636281477 867788810186748306802777)
                    ·
                      rfl

theorem cell22_2535019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 4].length) (baseStart_2535019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535019 prefixEnd_2535019 := by exact prefixLift 2535019
  have htrace : WordTrace (prefixWord ++ tailWord_2535019) baseStart_2535019 baseEnd_2535019 := by
    simpa [prefixWord, tailWord_2535019, baseEnd_2535019] using wordTrace_append hprefix tailTrace_2535019
  have hstable : (prefixWord ++ tailWord_2535019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535019).length < 2 ^ (prefixWord ++ tailWord_2535019).sum := by decide
  have hdescent : baseEnd_2535019 < baseStart_2535019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535070 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2535070 : Nat := 118140960795 + 2535070 * 2 ^ 59
def prefixEnd_2535070 : Nat := 4983230072969 + 3 ^ 40 * 2535070 * 2
def baseEnd_2535070 : Nat := 867806268529001173777621

theorem tailTrace_2535070 : CollatzResearch.WordTrace tailWord_2535070 prefixEnd_2535070 867806268529001173777621 := by
  unfold tailWord_2535070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11557699865735227541470333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61641065950587880221175109 11557699865735227541470333)
  ·
    refine ⟨4334137449650710328051375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11557699865735227541470333 4334137449650710328051375)
    ·
      refine ⟨6501206174476065492077063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4334137449650710328051375 6501206174476065492077063)
      ·
        refine ⟨9751809261714098238115595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6501206174476065492077063 9751809261714098238115595)
        ·
          refine ⟨14627713892571147357173393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9751809261714098238115595 14627713892571147357173393)
          ·
            refine ⟨10970785419428360517880045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14627713892571147357173393 10970785419428360517880045)
            ·
              refine ⟨4114044532285635194205017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10970785419428360517880045 4114044532285635194205017)
              ·
                refine ⟨3085533399214226395653763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4114044532285635194205017 3085533399214226395653763)
                ·
                  refine ⟨4628300098821339593480645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085533399214226395653763 4628300098821339593480645)
                  ·
                    refine ⟨867806268529001173777621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628300098821339593480645 867806268529001173777621)
                    ·
                      rfl

theorem cell22_2535070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2535070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535070 prefixEnd_2535070 := by exact prefixLift 2535070
  have htrace : WordTrace (prefixWord ++ tailWord_2535070) baseStart_2535070 baseEnd_2535070 := by
    simpa [prefixWord, tailWord_2535070, baseEnd_2535070] using wordTrace_append hprefix tailTrace_2535070
  have hstable : (prefixWord ++ tailWord_2535070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535070).length < 2 ^ (prefixWord ++ tailWord_2535070).sum := by decide
  have hdescent : baseEnd_2535070 < baseStart_2535070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535100 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 2, 3]
def baseStart_2535100 : Nat := 118140960795 + 2535100 * 2 ^ 59
def prefixEnd_2535100 : Nat := 4983230072969 + 3 ^ 40 * 2535100 * 2
def baseEnd_2535100 : Nat := 867816538142091095527529

theorem tailTrace_2535100 : CollatzResearch.WordTrace tailWord_2535100 prefixEnd_2535100 867816538142091095527529 := by
  unfold tailWord_2535100
  simp only [CollatzResearch.WordTrace]
  refine ⟨46231346557886567727677377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61641795410515423636903169 46231346557886567727677377)
  ·
    refine ⟨34673509918414925795758033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46231346557886567727677377 34673509918414925795758033)
    ·
      refine ⟨26005132438811194346818525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34673509918414925795758033 26005132438811194346818525)
      ·
        refine ⟨9751924664554197880056947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26005132438811194346818525 9751924664554197880056947)
        ·
          refine ⟨14627886996831296820085421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9751924664554197880056947 14627886996831296820085421)
          ·
            refine ⟨5485457623811736307532033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14627886996831296820085421 5485457623811736307532033)
            ·
              refine ⟨4114093217858802230649025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5485457623811736307532033 4114093217858802230649025)
              ·
                refine ⟨3085569913394101672986769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4114093217858802230649025 3085569913394101672986769)
                ·
                  refine ⟨2314177435045576254740077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3085569913394101672986769 2314177435045576254740077)
                  ·
                    refine ⟨867816538142091095527529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314177435045576254740077 867816538142091095527529)
                    ·
                      rfl

theorem cell22_2535100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_2535100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535100 prefixEnd_2535100 := by exact prefixLift 2535100
  have htrace : WordTrace (prefixWord ++ tailWord_2535100) baseStart_2535100 baseEnd_2535100 := by
    simpa [prefixWord, tailWord_2535100, baseEnd_2535100] using wordTrace_append hprefix tailTrace_2535100
  have hstable : (prefixWord ++ tailWord_2535100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535100).length < 2 ^ (prefixWord ++ tailWord_2535100).sum := by decide
  have hdescent : baseEnd_2535100 < baseStart_2535100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535102 : List Nat := [4, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_2535102 : Nat := 118140960795 + 2535102 * 2 ^ 59
def prefixEnd_2535102 : Nat := 4983230072969 + 3 ^ 40 * 2535102 * 2
def baseEnd_2535102 : Nat := 289272407594321252325841

theorem tailTrace_2535102 : CollatzResearch.WordTrace tailWord_2535102 prefixEnd_2535102 289272407594321252325841 := by
  unfold tailWord_2535102
  simp only [CollatzResearch.WordTrace]
  refine ⟨11557845757720736224615945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61641844041177259864618373 11557845757720736224615945)
  ·
    refine ⟨8668384318290552168461959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11557845757720736224615945 8668384318290552168461959)
    ·
      refine ⟨13002576477435828252692939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8668384318290552168461959 13002576477435828252692939)
      ·
        refine ⟨19503864716153742379039409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13002576477435828252692939 19503864716153742379039409)
        ·
          refine ⟨14627898537115306784279557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19503864716153742379039409 14627898537115306784279557)
          ·
            refine ⟨2742730975709120022052417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14627898537115306784279557 2742730975709120022052417)
            ·
              refine ⟨2057048231781840016539313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742730975709120022052417 2057048231781840016539313)
              ·
                refine ⟨1542786173836380012404485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057048231781840016539313 1542786173836380012404485)
                ·
                  refine ⟨289272407594321252325841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542786173836380012404485 289272407594321252325841)
                  ·
                    rfl

theorem cell22_2535102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_2535102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535102 prefixEnd_2535102 := by exact prefixLift 2535102
  have htrace : WordTrace (prefixWord ++ tailWord_2535102) baseStart_2535102 baseEnd_2535102 := by
    simpa [prefixWord, tailWord_2535102, baseEnd_2535102] using wordTrace_append hprefix tailTrace_2535102
  have hstable : (prefixWord ++ tailWord_2535102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535102).length < 2 ^ (prefixWord ++ tailWord_2535102).sum := by decide
  have hdescent : baseEnd_2535102 < baseStart_2535102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535117 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2535117 : Nat := 118140960795 + 2535117 * 2 ^ 59
def prefixEnd_2535117 : Nat := 4983230072969 + 3 ^ 40 * 2535117 * 2
def baseEnd_2535117 : Nat := 867822357589508717852477

theorem tailTrace_2535117 : CollatzResearch.WordTrace tailWord_2535117 prefixEnd_2535117 867822357589508717852477 := by
  unfold tailWord_2535117
  simp only [CollatzResearch.WordTrace]
  refine ⟨92463313156711547358723605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61642208771141031572482403 92463313156711547358723605)
  ·
    refine ⟨4334217804220853782440169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92463313156711547358723605 4334217804220853782440169)
    ·
      refine ⟨3250663353165640336830127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4334217804220853782440169 3250663353165640336830127)
      ·
        refine ⟨4875995029748460505245191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250663353165640336830127 4875995029748460505245191)
        ·
          refine ⟨7313992544622690757867787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4875995029748460505245191 7313992544622690757867787)
          ·
            refine ⟨10970988816934036136801681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7313992544622690757867787 10970988816934036136801681)
            ·
              refine ⟨8228241612700527102601261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10970988816934036136801681 8228241612700527102601261)
              ·
                refine ⟨3085590604762697663475473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8228241612700527102601261 3085590604762697663475473)
                ·
                  refine ⟨2314192953572023247606605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3085590604762697663475473 2314192953572023247606605)
                  ·
                    refine ⟨867822357589508717852477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314192953572023247606605 867822357589508717852477)
                    ·
                      rfl

theorem cell22_2535117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2535117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535117 prefixEnd_2535117 := by exact prefixLift 2535117
  have htrace : WordTrace (prefixWord ++ tailWord_2535117) baseStart_2535117 baseEnd_2535117 := by
    simpa [prefixWord, tailWord_2535117, baseEnd_2535117] using wordTrace_append hprefix tailTrace_2535117
  have hstable : (prefixWord ++ tailWord_2535117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535117).length < 2 ^ (prefixWord ++ tailWord_2535117).sum := by decide
  have hdescent : baseEnd_2535117 < baseStart_2535117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535128 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 3, 3]
def baseStart_2535128 : Nat := 118140960795 + 2535128 * 2 ^ 59
def prefixEnd_2535128 : Nat := 4983230072969 + 3 ^ 40 * 2535128 * 2
def baseEnd_2535128 : Nat := 867826123114308355827443

theorem tailTrace_2535128 : CollatzResearch.WordTrace tailWord_2535128 prefixEnd_2535128 867826123114308355827443 := by
  unfold tailWord_2535128
  simp only [CollatzResearch.WordTrace]
  refine ⟨46231857179835848118687019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61642476239781130824916025 46231857179835848118687019)
  ·
    refine ⟨69347785769753772178030529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46231857179835848118687019 69347785769753772178030529)
    ·
      refine ⟨52010839327315329133522897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69347785769753772178030529 52010839327315329133522897)
      ·
        refine ⟨39008129495486496850142173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52010839327315329133522897 39008129495486496850142173)
        ·
          refine ⟨14628048560807436318803315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39008129495486496850142173 14628048560807436318803315)
          ·
            refine ⟨21942072841211154478204973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14628048560807436318803315 21942072841211154478204973)
            ·
              refine ⟨8228277315454182929326865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21942072841211154478204973 8228277315454182929326865)
              ·
                refine ⟨6171207986590637196995149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8228277315454182929326865 6171207986590637196995149)
                ·
                  refine ⟨2314202994971488948873181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6171207986590637196995149 2314202994971488948873181)
                  ·
                    refine ⟨867826123114308355827443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314202994971488948873181 867826123114308355827443)
                    ·
                      rfl

theorem cell22_2535128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_2535128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535128 prefixEnd_2535128 := by exact prefixLift 2535128
  have htrace : WordTrace (prefixWord ++ tailWord_2535128) baseStart_2535128 baseEnd_2535128 := by
    simpa [prefixWord, tailWord_2535128, baseEnd_2535128] using wordTrace_append hprefix tailTrace_2535128
  have hstable : (prefixWord ++ tailWord_2535128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535128).length < 2 ^ (prefixWord ++ tailWord_2535128).sum := by decide
  have hdescent : baseEnd_2535128 < baseStart_2535128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535132 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2535132 : Nat := 118140960795 + 2535132 * 2 ^ 59
def prefixEnd_2535132 : Nat := 4983230072969 + 3 ^ 40 * 2535132 * 2
def baseEnd_2535132 : Nat := 867827492396053678727431

theorem tailTrace_2535132 : CollatzResearch.WordTrace tailWord_2535132 prefixEnd_2535132 867827492396053678727431 := by
  unfold tailWord_2535132
  simp only [CollatzResearch.WordTrace]
  refine ⟨46231930125828602460259825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61642573501104803280346433 46231930125828602460259825)
  ·
    refine ⟨34673947594371451845194869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46231930125828602460259825 34673947594371451845194869)
    ·
      refine ⟨3250682586972323610487019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34673947594371451845194869 3250682586972323610487019)
      ·
        refine ⟨4876023880458485415730529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250682586972323610487019 4876023880458485415730529)
        ·
          refine ⟨3657017910343864061797897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4876023880458485415730529 3657017910343864061797897)
          ·
            refine ⟨2742763432757898046348423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3657017910343864061797897 2742763432757898046348423)
            ·
              refine ⟨4114145149136847069522635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2742763432757898046348423 4114145149136847069522635)
              ·
                refine ⟨6171217723705270604283953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114145149136847069522635 6171217723705270604283953)
                ·
                  refine ⟨4628413292778952953212965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6171217723705270604283953 4628413292778952953212965)
                  ·
                    refine ⟨867827492396053678727431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628413292778952953212965 867827492396053678727431)
                    ·
                      rfl

theorem cell22_2535132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2535132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535132 prefixEnd_2535132 := by exact prefixLift 2535132
  have htrace : WordTrace (prefixWord ++ tailWord_2535132) baseStart_2535132 baseEnd_2535132 := by
    simpa [prefixWord, tailWord_2535132, baseEnd_2535132] using wordTrace_append hprefix tailTrace_2535132
  have hstable : (prefixWord ++ tailWord_2535132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535132).length < 2 ^ (prefixWord ++ tailWord_2535132).sum := by decide
  have hdescent : baseEnd_2535132 < baseStart_2535132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535141 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 7]
def baseStart_2535141 : Nat := 118140960795 + 2535141 * 2 ^ 59
def prefixEnd_2535141 : Nat := 4983230072969 + 3 ^ 40 * 2535141 * 2
def baseEnd_2535141 : Nat := 289276857759993551750801

theorem tailTrace_2535141 : CollatzResearch.WordTrace tailWord_2535141 prefixEnd_2535141 289276857759993551750801 := by
  unfold tailWord_2535141
  simp only [CollatzResearch.WordTrace]
  refine ⟨92464188508624599457597277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61642792339083066305064851 92464188508624599457597277)
  ·
    refine ⟨34674070690734224796598979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92464188508624599457597277 34674070690734224796598979)
    ·
      refine ⟨52011106036101337194898469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34674070690734224796598979 52011106036101337194898469)
      ·
        refine ⟨9752082381769000724043463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52011106036101337194898469 9752082381769000724043463)
        ·
          refine ⟨14628123572653501086065195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9752082381769000724043463 14628123572653501086065195)
          ·
            refine ⟨21942185358980251629097793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14628123572653501086065195 21942185358980251629097793)
            ·
              refine ⟨16456639019235188721823345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21942185358980251629097793 16456639019235188721823345)
              ·
                refine ⟨12342479264426391541367509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16456639019235188721823345 12342479264426391541367509)
                ·
                  refine ⟨289276857759993551750801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12342479264426391541367509 289276857759993551750801)
                  ·
                    rfl

theorem cell22_2535141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_2535141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535141 prefixEnd_2535141 := by exact prefixLift 2535141
  have htrace : WordTrace (prefixWord ++ tailWord_2535141) baseStart_2535141 baseEnd_2535141 := by
    simpa [prefixWord, tailWord_2535141, baseEnd_2535141] using wordTrace_append hprefix tailTrace_2535141
  have hstable : (prefixWord ++ tailWord_2535141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535141).length < 2 ^ (prefixWord ++ tailWord_2535141).sum := by decide
  have hdescent : baseEnd_2535141 < baseStart_2535141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535158 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_2535158 : Nat := 118140960795 + 2535158 * 2 ^ 59
def prefixEnd_2535158 : Nat := 4983230072969 + 3 ^ 40 * 2535158 * 2
def baseEnd_2535158 : Nat := 289278797575799425859117

theorem tailTrace_2535158 : CollatzResearch.WordTrace tailWord_2535158 prefixEnd_2535158 289278797575799425859117 := by
  unfold tailWord_2535158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779050534347688210060383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61643205699708674240644085 5779050534347688210060383)
  ·
    refine ⟨8668575801521532315090575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5779050534347688210060383 8668575801521532315090575)
    ·
      refine ⟨13002863702282298472635863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8668575801521532315090575 13002863702282298472635863)
      ·
        refine ⟨19504295553423447708953795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13002863702282298472635863 19504295553423447708953795)
        ·
          refine ⟨29256443330135171563430693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19504295553423447708953795 29256443330135171563430693)
          ·
            refine ⟨5485583124400344668143255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29256443330135171563430693 5485583124400344668143255)
            ·
              refine ⟨8228374686600517002214883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5485583124400344668143255 8228374686600517002214883)
              ·
                refine ⟨12342562029900775503322325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8228374686600517002214883 12342562029900775503322325)
                ·
                  refine ⟨289278797575799425859117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12342562029900775503322325 289278797575799425859117)
                  ·
                    rfl

theorem cell22_2535158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_2535158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535158 prefixEnd_2535158 := by exact prefixLift 2535158
  have htrace : WordTrace (prefixWord ++ tailWord_2535158) baseStart_2535158 baseEnd_2535158 := by
    simpa [prefixWord, tailWord_2535158, baseEnd_2535158] using wordTrace_append hprefix tailTrace_2535158
  have hstable : (prefixWord ++ tailWord_2535158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535158).length < 2 ^ (prefixWord ++ tailWord_2535158).sum := by decide
  have hdescent : baseEnd_2535158 < baseStart_2535158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535171 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 5, 4]
def baseStart_2535171 : Nat := 118140960795 + 2535171 * 2 ^ 59
def prefixEnd_2535171 : Nat := 4983230072969 + 3 ^ 40 * 2535171 * 2
def baseEnd_2535171 : Nat := 867840842893070577002311

theorem tailTrace_2535171 : CollatzResearch.WordTrace tailWord_2535171 prefixEnd_2535171 867840842893070577002311 := by
  unfold tailWord_2535171
  simp only [CollatzResearch.WordTrace]
  refine ⟨92465282698515914581189367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61643521799010609720792911 92465282698515914581189367)
  ·
    refine ⟨138697924047773871871784051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92465282698515914581189367 138697924047773871871784051)
    ·
      refine ⟨208046886071660807807676077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138697924047773871871784051 208046886071660807807676077)
      ·
        refine ⟨78017582276872802927878529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208046886071660807807676077 78017582276872802927878529)
        ·
          refine ⟨58513186707654602195908897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78017582276872802927878529 58513186707654602195908897)
          ·
            refine ⟨43884890030740951646931673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58513186707654602195908897 43884890030740951646931673)
            ·
              refine ⟨32913667523055713735198755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43884890030740951646931673 32913667523055713735198755)
              ·
                refine ⟨49370501284583570602798133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32913667523055713735198755 49370501284583570602798133)
                ·
                  refine ⟨4628484495429709744012325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49370501284583570602798133 4628484495429709744012325)
                  ·
                    refine ⟨867840842893070577002311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628484495429709744012325 867840842893070577002311)
                    ·
                      rfl

theorem cell22_2535171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 4].length) (baseStart_2535171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535171 prefixEnd_2535171 := by exact prefixLift 2535171
  have htrace : WordTrace (prefixWord ++ tailWord_2535171) baseStart_2535171 baseEnd_2535171 := by
    simpa [prefixWord, tailWord_2535171, baseEnd_2535171] using wordTrace_append hprefix tailTrace_2535171
  have hstable : (prefixWord ++ tailWord_2535171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535171).length < 2 ^ (prefixWord ++ tailWord_2535171).sum := by decide
  have hdescent : baseEnd_2535171 < baseStart_2535171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535181 : List Nat := [1, 7, 2, 1, 1, 2, 2, 6]
def baseStart_2535181 : Nat := 118140960795 + 2535181 * 2 ^ 59
def prefixEnd_2535181 : Nat := 4983230072969 + 3 ^ 40 * 2535181 * 2
def baseEnd_2535181 : Nat := 96427140677492653805809

theorem tailTrace_2535181 : CollatzResearch.WordTrace tailWord_2535181 prefixEnd_2535181 96427140677492653805809 := by
  unfold tailWord_2535181
  simp only [CollatzResearch.WordTrace]
  refine ⟨92465647428479686289053397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61643764952319790859368931 92465647428479686289053397)
  ·
    refine ⟨2167163611604992647399689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 92465647428479686289053397 2167163611604992647399689)
    ·
      refine ⟨1625372708703744485549767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2167163611604992647399689 1625372708703744485549767)
      ·
        refine ⟨2438059063055616728324651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625372708703744485549767 2438059063055616728324651)
        ·
          refine ⟨3657088594583425092486977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438059063055616728324651 3657088594583425092486977)
          ·
            refine ⟨2742816445937568819365233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3657088594583425092486977 2742816445937568819365233)
            ·
              refine ⟨2057112334453176614523925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742816445937568819365233 2057112334453176614523925)
              ·
                refine ⟨96427140677492653805809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2057112334453176614523925 96427140677492653805809)
                ·
                  rfl

theorem cell22_2535181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 6].length) (baseStart_2535181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535181 prefixEnd_2535181 := by exact prefixLift 2535181
  have htrace : WordTrace (prefixWord ++ tailWord_2535181) baseStart_2535181 baseEnd_2535181 := by
    simpa [prefixWord, tailWord_2535181, baseEnd_2535181] using wordTrace_append hprefix tailTrace_2535181
  have hstable : (prefixWord ++ tailWord_2535181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535181).length < 2 ^ (prefixWord ++ tailWord_2535181).sum := by decide
  have hdescent : baseEnd_2535181 < baseStart_2535181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535220 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 6]
def baseStart_2535220 : Nat := 118140960795 + 2535220 * 2 ^ 59
def prefixEnd_2535220 : Nat := 4983230072969 + 3 ^ 40 * 2535220 * 2
def baseEnd_2535220 : Nat := 289285872198150260842387

theorem tailTrace_2535220 : CollatzResearch.WordTrace tailWord_2535220 prefixEnd_2535220 289285872198150260842387 := by
  unfold tailWord_2535220
  simp only [CollatzResearch.WordTrace]
  refine ⟨46233534937669197974861557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61644713250225597299815409 46233534937669197974861557)
  ·
    refine ⟨4334393900406487310143271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46233534937669197974861557 4334393900406487310143271)
    ·
      refine ⟨6501590850609730965214907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4334393900406487310143271 6501590850609730965214907)
      ·
        refine ⟨9752386275914596447822361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6501590850609730965214907 9752386275914596447822361)
        ·
          refine ⟨7314289706935947335866771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9752386275914596447822361 7314289706935947335866771)
          ·
            refine ⟨10971434560403921003800157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7314289706935947335866771 10971434560403921003800157)
            ·
              refine ⟨4114287960151470376425059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10971434560403921003800157 4114287960151470376425059)
              ·
                refine ⟨6171431940227205564637589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114287960151470376425059 6171431940227205564637589)
                ·
                  refine ⟨289285872198150260842387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6171431940227205564637589 289285872198150260842387)
                  ·
                    rfl

theorem cell22_2535220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_2535220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535220 prefixEnd_2535220 := by exact prefixLift 2535220
  have htrace : WordTrace (prefixWord ++ tailWord_2535220) baseStart_2535220 baseEnd_2535220 := by
    simpa [prefixWord, tailWord_2535220, baseEnd_2535220] using wordTrace_append hprefix tailTrace_2535220
  have hstable : (prefixWord ++ tailWord_2535220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535220).length < 2 ^ (prefixWord ++ tailWord_2535220).sum := by decide
  have hdescent : baseEnd_2535220 < baseStart_2535220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535235 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 2, 3]
def baseStart_2535235 : Nat := 118140960795 + 2535235 * 2 ^ 59
def prefixEnd_2535235 : Nat := 4983230072969 + 3 ^ 40 * 2535235 * 2
def baseEnd_2535235 : Nat := 867862751400995743402115

theorem tailTrace_2535235 : CollatzResearch.WordTrace tailWord_2535235 prefixEnd_2535235 867862751400995743402115 := by
  unfold tailWord_2535235
  simp only [CollatzResearch.WordTrace]
  refine ⟨92467616970284053511519159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61645077980189369007679439 92467616970284053511519159)
  ·
    refine ⟨138701425455426080267278739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92467616970284053511519159 138701425455426080267278739)
    ·
      refine ⟨208052138183139120400918109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138701425455426080267278739 208052138183139120400918109)
      ·
        refine ⟨78019551818677170150344291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208052138183139120400918109 78019551818677170150344291)
        ·
          refine ⟨117029327728015755225516437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78019551818677170150344291 117029327728015755225516437)
          ·
            refine ⟨5485749737250738526196083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117029327728015755225516437 5485749737250738526196083)
            ·
              refine ⟨8228624605876107789294125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5485749737250738526196083 8228624605876107789294125)
              ·
                refine ⟨3085734227203540420985297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8228624605876107789294125 3085734227203540420985297)
                ·
                  refine ⟨2314300670402655315738973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3085734227203540420985297 2314300670402655315738973)
                  ·
                    refine ⟨867862751400995743402115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314300670402655315738973 867862751400995743402115)
                    ·
                      rfl

theorem cell22_2535235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 3].length) (baseStart_2535235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535235 prefixEnd_2535235 := by exact prefixLift 2535235
  have htrace : WordTrace (prefixWord ++ tailWord_2535235) baseStart_2535235 baseEnd_2535235 := by
    simpa [prefixWord, tailWord_2535235, baseEnd_2535235] using wordTrace_append hprefix tailTrace_2535235
  have hstable : (prefixWord ++ tailWord_2535235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535235).length < 2 ^ (prefixWord ++ tailWord_2535235).sum := by decide
  have hdescent : baseEnd_2535235 < baseStart_2535235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535250 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_2535250 : Nat := 118140960795 + 2535250 * 2 ^ 59
def prefixEnd_2535250 : Nat := 4983230072969 + 3 ^ 40 * 2535250 * 2
def baseEnd_2535250 : Nat := 867867886207540704277069

theorem tailTrace_2535250 : CollatzResearch.WordTrace tailWord_2535250 prefixEnd_2535250 867867886207540704277069 := by
  unfold tailWord_2535250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23117041016307427768328801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61645442710153140715543469 23117041016307427768328801)
  ·
    refine ⟨17337780762230570826246601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23117041016307427768328801 17337780762230570826246601)
    ·
      refine ⟨13003335571672928119684951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17337780762230570826246601 13003335571672928119684951)
      ·
        refine ⟨19505003357509392179527427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13003335571672928119684951 19505003357509392179527427)
        ·
          refine ⟨29257505036264088269291141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19505003357509392179527427 29257505036264088269291141)
          ·
            refine ⟨5485782194299516550492089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29257505036264088269291141 5485782194299516550492089)
            ·
              refine ⟨4114336645724637412869067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5485782194299516550492089 4114336645724637412869067)
              ·
                refine ⟨6171504968586956119303601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114336645724637412869067 6171504968586956119303601)
                ·
                  refine ⟨4628628726440217089477701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6171504968586956119303601 4628628726440217089477701)
                  ·
                    refine ⟨867867886207540704277069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628628726440217089477701 867867886207540704277069)
                    ·
                      rfl

theorem cell22_2535250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_2535250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535250 prefixEnd_2535250 := by exact prefixLift 2535250
  have htrace : WordTrace (prefixWord ++ tailWord_2535250) baseStart_2535250 baseEnd_2535250 := by
    simpa [prefixWord, tailWord_2535250, baseEnd_2535250] using wordTrace_append hprefix tailTrace_2535250
  have hstable : (prefixWord ++ tailWord_2535250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535250).length < 2 ^ (prefixWord ++ tailWord_2535250).sum := by decide
  have hdescent : baseEnd_2535250 < baseStart_2535250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535314 : List Nat := [3, 2, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2535314 : Nat := 118140960795 + 2535314 * 2 ^ 59
def prefixEnd_2535314 : Nat := 4983230072969 + 3 ^ 40 * 2535314 * 2
def baseEnd_2535314 : Nat := 867889794715465870676873

theorem tailTrace_2535314 : CollatzResearch.WordTrace tailWord_2535314 prefixEnd_2535314 867889794715465870676873 := by
  unfold tailWord_2535314
  simp only [CollatzResearch.WordTrace]
  refine ⟨23117624584249462500911249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61646998891331900002429997 23117624584249462500911249)
  ·
    refine ⟨17338218438187096875683437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23117624584249462500911249 17338218438187096875683437)
    ·
      refine ⟨6501831914320161328381289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17338218438187096875683437 6501831914320161328381289)
      ·
        refine ⟨4876373935740120996285967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6501831914320161328381289 4876373935740120996285967)
        ·
          refine ⟨7314560903610181494428951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876373935740120996285967 7314560903610181494428951)
          ·
            refine ⟨10971841355415272241643427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7314560903610181494428951 10971841355415272241643427)
            ·
              refine ⟨16457762033122908362465141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10971841355415272241643427 16457762033122908362465141)
              ·
                refine ⟨1542915190605272658981107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16457762033122908362465141 1542915190605272658981107)
                ·
                  refine ⟨2314372785907908988471661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542915190605272658981107 2314372785907908988471661)
                  ·
                    refine ⟨867889794715465870676873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314372785907908988471661 867889794715465870676873)
                    ·
                      rfl

theorem cell22_2535314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2535314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535314 prefixEnd_2535314 := by exact prefixLift 2535314
  have htrace : WordTrace (prefixWord ++ tailWord_2535314) baseStart_2535314 baseEnd_2535314 := by
    simpa [prefixWord, tailWord_2535314, baseEnd_2535314] using wordTrace_append hprefix tailTrace_2535314
  have hstable : (prefixWord ++ tailWord_2535314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535314).length < 2 ^ (prefixWord ++ tailWord_2535314).sum := by decide
  have hdescent : baseEnd_2535314 < baseStart_2535314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535327 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 5]
def baseStart_2535327 : Nat := 118140960795 + 2535327 * 2 ^ 59
def prefixEnd_2535327 : Nat := 4983230072969 + 3 ^ 40 * 2535327 * 2
def baseEnd_2535327 : Nat := 289298081627046056700611

theorem tailTrace_2535327 : CollatzResearch.WordTrace tailWord_2535327 prefixEnd_2535327 289298081627046056700611 := by
  unfold tailWord_2535327
  simp only [CollatzResearch.WordTrace]
  refine ⟨92470972485950753223868235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61647314990633835482578823 92470972485950753223868235)
  ·
    refine ⟨138706458728926129835802353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92470972485950753223868235 138706458728926129835802353)
    ·
      refine ⟨104029844046694597376851765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138706458728926129835802353 104029844046694597376851765)
      ·
        refine ⟨9752797879377618504079853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104029844046694597376851765 9752797879377618504079853)
        ·
          refine ⟨3657299204766606939029945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9752797879377618504079853 3657299204766606939029945)
          ·
            refine ⟨2742974403574955204272459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3657299204766606939029945 2742974403574955204272459)
            ·
              refine ⟨4114461605362432806408689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2742974403574955204272459 4114461605362432806408689)
              ·
                refine ⟨3085846204021824604806517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4114461605362432806408689 3085846204021824604806517)
                ·
                  refine ⟨289298081627046056700611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3085846204021824604806517 289298081627046056700611)
                  ·
                    rfl

theorem cell22_2535327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 5].length) (baseStart_2535327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535327 prefixEnd_2535327 := by exact prefixLift 2535327
  have htrace : WordTrace (prefixWord ++ tailWord_2535327) baseStart_2535327 baseEnd_2535327 := by
    simpa [prefixWord, tailWord_2535327, baseEnd_2535327] using wordTrace_append hprefix tailTrace_2535327
  have hstable : (prefixWord ++ tailWord_2535327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535327).length < 2 ^ (prefixWord ++ tailWord_2535327).sum := by decide
  have hdescent : baseEnd_2535327 < baseStart_2535327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535357 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_2535357 : Nat := 118140960795 + 2535357 * 2 ^ 59
def prefixEnd_2535357 : Nat := 4983230072969 + 3 ^ 40 * 2535357 * 2
def baseEnd_2535357 : Nat := 867904514494228091851741

theorem tailTrace_2535357 : CollatzResearch.WordTrace tailWord_2535357 prefixEnd_2535357 867904514494228091851741 := by
  unfold tailWord_2535357
  simp only [CollatzResearch.WordTrace]
  refine ⟨92472066675842068347460325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61648044450561378898306883 92472066675842068347460325)
  ·
    refine ⟨17338512501720387815148811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92472066675842068347460325 17338512501720387815148811)
    ·
      refine ⟨26007768752580581722723217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17338512501720387815148811 26007768752580581722723217)
      ·
        refine ⟨19505826564435436292042413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26007768752580581722723217 19505826564435436292042413)
        ·
          refine ⟨7314684961663288609515905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19505826564435436292042413 7314684961663288609515905)
          ·
            refine ⟨5486013721247466457136929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7314684961663288609515905 5486013721247466457136929)
            ·
              refine ⟨4114510290935599842852697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5486013721247466457136929 4114510290935599842852697)
              ·
                refine ⟨3085882718201699882139523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4114510290935599842852697 3085882718201699882139523)
                ·
                  refine ⟨4628824077302549823209285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085882718201699882139523 4628824077302549823209285)
                  ·
                    refine ⟨867904514494228091851741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628824077302549823209285 867904514494228091851741)
                    ·
                      rfl

theorem cell22_2535357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_2535357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535357 prefixEnd_2535357 := by exact prefixLift 2535357
  have htrace : WordTrace (prefixWord ++ tailWord_2535357) baseStart_2535357 baseEnd_2535357 := by
    simpa [prefixWord, tailWord_2535357, baseEnd_2535357] using wordTrace_append hprefix tailTrace_2535357
  have hstable : (prefixWord ++ tailWord_2535357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535357).length < 2 ^ (prefixWord ++ tailWord_2535357).sum := by decide
  have hdescent : baseEnd_2535357 < baseStart_2535357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535370 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 4, 3]
def baseStart_2535370 : Nat := 118140960795 + 2535370 * 2 ^ 59
def prefixEnd_2535370 : Nat := 4983230072969 + 3 ^ 40 * 2535370 * 2
def baseEnd_2535370 : Nat := 867908964659900391276701

theorem tailTrace_2535370 : CollatzResearch.WordTrace tailWord_2535370 prefixEnd_2535370 867908964659900391276701 := by
  unfold tailWord_2535370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23118135206198742891920891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61648360549863314378455709 23118135206198742891920891)
  ·
    refine ⟨34677202809298114337881337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23118135206198742891920891 34677202809298114337881337)
    ·
      refine ⟨26007902106973585753411003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34677202809298114337881337 26007902106973585753411003)
      ·
        refine ⟨39011853160460378630116505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26007902106973585753411003 39011853160460378630116505)
        ·
          refine ⟨29258889870345283972587379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39011853160460378630116505 29258889870345283972587379)
          ·
            refine ⟨43888334805517925958881069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29258889870345283972587379 43888334805517925958881069)
            ·
              refine ⟨16458125552069222234580401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43888334805517925958881069 16458125552069222234580401)
              ·
                refine ⟨12343594164051916675935301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16458125552069222234580401 12343594164051916675935301)
                ·
                  refine ⟨2314423905759734376737869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12343594164051916675935301 2314423905759734376737869)
                  ·
                    refine ⟨867908964659900391276701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314423905759734376737869 867908964659900391276701)
                    ·
                      rfl

theorem cell22_2535370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_2535370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535370 prefixEnd_2535370 := by exact prefixLift 2535370
  have htrace : WordTrace (prefixWord ++ tailWord_2535370) baseStart_2535370 baseEnd_2535370 := by
    simpa [prefixWord, tailWord_2535370, baseEnd_2535370] using wordTrace_append hprefix tailTrace_2535370
  have hstable : (prefixWord ++ tailWord_2535370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535370).length < 2 ^ (prefixWord ++ tailWord_2535370).sum := by decide
  have hdescent : baseEnd_2535370 < baseStart_2535370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535372 : List Nat := [2, 2, 1, 4, 1, 2, 3, 3, 4]
def baseStart_2535372 : Nat := 118140960795 + 2535372 * 2 ^ 59
def prefixEnd_2535372 : Nat := 4983230072969 + 3 ^ 40 * 2535372 * 2
def baseEnd_2535372 : Nat := 289303216433591017575565

theorem tailTrace_2535372 : CollatzResearch.WordTrace tailWord_2535372 prefixEnd_2535372 289303216433591017575565 := by
  unfold tailWord_2535372
  simp only [CollatzResearch.WordTrace]
  refine ⟨46236306885393862954628185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61648409180525150606170913 46236306885393862954628185)
  ·
    refine ⟨34677230164045397215971139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46236306885393862954628185 34677230164045397215971139)
    ·
      refine ⟨52015845246068095823956709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34677230164045397215971139 52015845246068095823956709)
      ·
        refine ⟨9752970983637767966991883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52015845246068095823956709 9752970983637767966991883)
        ·
          refine ⟨14629456475456651950487825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9752970983637767966991883 14629456475456651950487825)
          ·
            refine ⟨10972092356592488962865869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14629456475456651950487825 10972092356592488962865869)
            ·
              refine ⟨4114534633722183361074701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10972092356592488962865869 4114534633722183361074701)
              ·
                refine ⟨1542950487645818760403013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4114534633722183361074701 1542950487645818760403013)
                ·
                  refine ⟨289303216433591017575565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542950487645818760403013 289303216433591017575565)
                  ·
                    rfl

theorem cell22_2535372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_2535372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535372 prefixEnd_2535372 := by exact prefixLift 2535372
  have htrace : WordTrace (prefixWord ++ tailWord_2535372) baseStart_2535372 baseEnd_2535372 := by
    simpa [prefixWord, tailWord_2535372, baseEnd_2535372] using wordTrace_append hprefix tailTrace_2535372
  have hstable : (prefixWord ++ tailWord_2535372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535372).length < 2 ^ (prefixWord ++ tailWord_2535372).sum := by decide
  have hdescent : baseEnd_2535372 < baseStart_2535372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535389 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 6]
def baseStart_2535389 : Nat := 118140960795 + 2535389 * 2 ^ 59
def prefixEnd_2535389 : Nat := 4983230072969 + 3 ^ 40 * 2535389 * 2
def baseEnd_2535389 : Nat := 289305156249396891683881

theorem tailTrace_2535389 : CollatzResearch.WordTrace tailWord_2535389 prefixEnd_2535389 289305156249396891683881 := by
  unfold tailWord_2535389
  simp only [CollatzResearch.WordTrace]
  refine ⟨92473233811726137812625221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61648822541150758541750147 92473233811726137812625221)
  ·
    refine ⟨17338731339698650839867229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92473233811726137812625221 17338731339698650839867229)
    ·
      refine ⟨6502024252386994064950211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17338731339698650839867229 6502024252386994064950211)
      ·
        refine ⟨9753036378580491097425317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6502024252386994064950211 9753036378580491097425317)
        ·
          refine ⟨1828694320983842080767247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9753036378580491097425317 1828694320983842080767247)
          ·
            refine ⟨2743041481475763121150871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828694320983842080767247 2743041481475763121150871)
            ·
              refine ⟨4114562222213644681726307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743041481475763121150871 4114562222213644681726307)
              ·
                refine ⟨6171843333320467022589461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114562222213644681726307 6171843333320467022589461)
                ·
                  refine ⟨289305156249396891683881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6171843333320467022589461 289305156249396891683881)
                  ·
                    rfl

theorem cell22_2535389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_2535389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535389 prefixEnd_2535389 := by exact prefixLift 2535389
  have htrace : WordTrace (prefixWord ++ tailWord_2535389) baseStart_2535389 baseEnd_2535389 := by
    simpa [prefixWord, tailWord_2535389, baseEnd_2535389] using wordTrace_append hprefix tailTrace_2535389
  have hstable : (prefixWord ++ tailWord_2535389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535389).length < 2 ^ (prefixWord ++ tailWord_2535389).sum := by decide
  have hdescent : baseEnd_2535389 < baseStart_2535389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535475 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 3, 4]
def baseStart_2535475 : Nat := 118140960795 + 2535475 * 2 ^ 59
def prefixEnd_2535475 : Nat := 4983230072969 + 3 ^ 40 * 2535475 * 2
def baseEnd_2535475 : Nat := 867944908305715117401379

theorem tailTrace_2535475 : CollatzResearch.WordTrace tailWord_2535475 prefixEnd_2535475 867944908305715117401379 := by
  unfold tailWord_2535475
  simp only [CollatzResearch.WordTrace]
  refine ⟨92476370489414574500255879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61650913659609716333503919 92476370489414574500255879)
  ·
    refine ⟨138714555734121861750383819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92476370489414574500255879 138714555734121861750383819)
    ·
      refine ⟨208071833601182792625575729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138714555734121861750383819 208071833601182792625575729)
      ·
        refine ⟨156053875200887094469181797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208071833601182792625575729 156053875200887094469181797)
        ·
          refine ⟨29260101600166330212971587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156053875200887094469181797 29260101600166330212971587)
          ·
            refine ⟨43890152400249495319457381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29260101600166330212971587 43890152400249495319457381)
            ·
              refine ⟨8229403575046780372398259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43890152400249495319457381 8229403575046780372398259)
              ·
                refine ⟨12344105362570170558597389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8229403575046780372398259 12344105362570170558597389)
                ·
                  refine ⟨4629039510963813959474021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12344105362570170558597389 4629039510963813959474021)
                  ·
                    refine ⟨867944908305715117401379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4629039510963813959474021 867944908305715117401379)
                    ·
                      rfl

theorem cell22_2535475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 4].length) (baseStart_2535475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535475 prefixEnd_2535475 := by exact prefixLift 2535475
  have htrace : WordTrace (prefixWord ++ tailWord_2535475) baseStart_2535475 baseEnd_2535475 := by
    simpa [prefixWord, tailWord_2535475, baseEnd_2535475] using wordTrace_append hprefix tailTrace_2535475
  have hstable : (prefixWord ++ tailWord_2535475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535475).length < 2 ^ (prefixWord ++ tailWord_2535475).sum := by decide
  have hdescent : baseEnd_2535475 < baseStart_2535475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535520 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_2535520 : Nat := 118140960795 + 2535520 * 2 ^ 59
def prefixEnd_2535520 : Nat := 4983230072969 + 3 ^ 40 * 2535520 * 2
def baseEnd_2535520 : Nat := 867960312725350000026241

theorem tailTrace_2535520 : CollatzResearch.WordTrace tailWord_2535520 prefixEnd_2535520 867960312725350000026241 := by
  unfold tailWord_2535520
  simp only [CollatzResearch.WordTrace]
  refine ⟨46239005887125773592822007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61652007849501031457096009 46239005887125773592822007)
  ·
    refine ⟨69358508830688660389233011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46239005887125773592822007 69358508830688660389233011)
    ·
      refine ⟨104037763246032990583849517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69358508830688660389233011 104037763246032990583849517)
      ·
        refine ⟨39014161217262371468943569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104037763246032990583849517 39014161217262371468943569)
        ·
          refine ⟨29260620912946778601707677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39014161217262371468943569 29260620912946778601707677)
          ·
            refine ⟨10972732842355041975640379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29260620912946778601707677 10972732842355041975640379)
            ·
              refine ⟨16459099263532562963460569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10972732842355041975640379 16459099263532562963460569)
              ·
                refine ⟨12344324447649422222595427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16459099263532562963460569 12344324447649422222595427)
                ·
                  refine ⟨18516486671474133333893141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12344324447649422222595427 18516486671474133333893141)
                  ·
                    refine ⟨867960312725350000026241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18516486671474133333893141 867960312725350000026241)
                    ·
                      rfl

theorem cell22_2535520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_2535520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535520 prefixEnd_2535520 := by exact prefixLift 2535520
  have htrace : WordTrace (prefixWord ++ tailWord_2535520) baseStart_2535520 baseEnd_2535520 := by
    simpa [prefixWord, tailWord_2535520, baseEnd_2535520] using wordTrace_append hprefix tailTrace_2535520
  have hstable : (prefixWord ++ tailWord_2535520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535520).length < 2 ^ (prefixWord ++ tailWord_2535520).sum := by decide
  have hdescent : baseEnd_2535520 < baseStart_2535520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535535 : List Nat := [1, 1, 2, 1, 3, 5, 1, 8]
def baseStart_2535535 : Nat := 118140960795 + 2535535 * 2 ^ 59
def prefixEnd_2535535 : Nat := 4983230072969 + 3 ^ 40 * 2535535 * 2
def baseEnd_2535535 : Nat := 96440605281321662322355

theorem tailTrace_2535535 : CollatzResearch.WordTrace tailWord_2535535 prefixEnd_2535535 96440605281321662322355 := by
  unfold tailWord_2535535
  simp only [CollatzResearch.WordTrace]
  refine ⟨92478558869197204747440059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61652372579464803164960039 92478558869197204747440059)
  ·
    refine ⟨138717838303795807121160089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92478558869197204747440059 138717838303795807121160089)
    ·
      refine ⟨104038378727846855340870067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138717838303795807121160089 104038378727846855340870067)
      ·
        refine ⟨156057568091770283011305101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104038378727846855340870067 156057568091770283011305101)
        ·
          refine ⟨58521588034413856129239413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156057568091770283011305101 58521588034413856129239413)
          ·
            refine ⟨5486398878226299012116195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58521588034413856129239413 5486398878226299012116195)
            ·
              refine ⟨8229598317339448518174293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5486398878226299012116195 8229598317339448518174293)
              ·
                refine ⟨96440605281321662322355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8229598317339448518174293 96440605281321662322355)
                ·
                  rfl

theorem cell22_2535535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 8].length) (baseStart_2535535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535535 prefixEnd_2535535 := by exact prefixLift 2535535
  have htrace : WordTrace (prefixWord ++ tailWord_2535535) baseStart_2535535 baseEnd_2535535 := by
    simpa [prefixWord, tailWord_2535535, baseEnd_2535535] using wordTrace_append hprefix tailTrace_2535535
  have hstable : (prefixWord ++ tailWord_2535535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535535).length < 2 ^ (prefixWord ++ tailWord_2535535).sum := by decide
  have hdescent : baseEnd_2535535 < baseStart_2535535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535657 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 6, 3]
def baseStart_2535657 : Nat := 118140960795 + 2535657 * 2 ^ 59
def prefixEnd_2535657 : Nat := 4983230072969 + 3 ^ 40 * 2535657 * 2
def baseEnd_2535657 : Nat := 868007210625127309350821

theorem tailTrace_2535657 : CollatzResearch.WordTrace tailWord_2535657 prefixEnd_2535657 868007210625127309350821 := by
  unfold tailWord_2535657
  simp only [CollatzResearch.WordTrace]
  refine ⟨92483008574755219583381225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61655339049836813055587483 92483008574755219583381225)
  ·
    refine ⟨69362256431066414687535919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92483008574755219583381225 69362256431066414687535919)
    ·
      refine ⟨104043384646599622031303879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69362256431066414687535919 104043384646599622031303879)
      ·
        refine ⟨156065076969899433046955819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104043384646599622031303879 156065076969899433046955819)
        ·
          refine ⟨234097615454849149570433729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156065076969899433046955819 234097615454849149570433729)
          ·
            refine ⟨175573211591136862177825297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234097615454849149570433729 175573211591136862177825297)
            ·
              refine ⟨131679908693352646633368973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175573211591136862177825297 131679908693352646633368973)
              ·
                refine ⟨49379965760007242487513365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131679908693352646633368973 49379965760007242487513365)
                ·
                  refine ⟨2314685895000339491602189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49379965760007242487513365 2314685895000339491602189)
                  ·
                    refine ⟨868007210625127309350821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314685895000339491602189 868007210625127309350821)
                    ·
                      rfl

theorem cell22_2535657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 3].length) (baseStart_2535657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535657 prefixEnd_2535657 := by exact prefixLift 2535657
  have htrace : WordTrace (prefixWord ++ tailWord_2535657) baseStart_2535657 baseEnd_2535657 := by
    simpa [prefixWord, tailWord_2535657, baseEnd_2535657] using wordTrace_append hprefix tailTrace_2535657
  have hstable : (prefixWord ++ tailWord_2535657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535657).length < 2 ^ (prefixWord ++ tailWord_2535657).sum := by decide
  have hdescent : baseEnd_2535657 < baseStart_2535657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535659 : List Nat := [1, 1, 1, 1, 2, 5, 4, 3, 4]
def baseStart_2535659 : Nat := 118140960795 + 2535659 * 2 ^ 59
def prefixEnd_2535659 : Nat := 4983230072969 + 3 ^ 40 * 2535659 * 2
def baseEnd_2535659 : Nat := 289335965088666656933605

theorem tailTrace_2535659 : CollatzResearch.WordTrace tailWord_2535659 prefixEnd_2535659 289335965088666656933605 := by
  unfold tailWord_2535659
  simp only [CollatzResearch.WordTrace]
  refine ⟨92483081520747973924954031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61655387680498649283302687 92483081520747973924954031)
  ·
    refine ⟨138724622281121960887431047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92483081520747973924954031 138724622281121960887431047)
    ·
      refine ⟨208086933421682941331146571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138724622281121960887431047 208086933421682941331146571)
      ·
        refine ⟨312130400132524411996719857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208086933421682941331146571 312130400132524411996719857)
        ·
          refine ⟨234097800099393308997539893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312130400132524411996719857 234097800099393308997539893)
          ·
            refine ⟨21946668759318122718519365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 234097800099393308997539893 21946668759318122718519365)
            ·
              refine ⟨4115000392372148009722381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21946668759318122718519365 4115000392372148009722381)
              ·
                refine ⟨1543125147139555503645893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4115000392372148009722381 1543125147139555503645893)
                ·
                  refine ⟨289335965088666656933605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543125147139555503645893 289335965088666656933605)
                  ·
                    rfl

theorem cell22_2535659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 4].length) (baseStart_2535659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535659 prefixEnd_2535659 := by exact prefixLift 2535659
  have htrace : WordTrace (prefixWord ++ tailWord_2535659) baseStart_2535659 baseEnd_2535659 := by
    simpa [prefixWord, tailWord_2535659, baseEnd_2535659] using wordTrace_append hprefix tailTrace_2535659
  have hstable : (prefixWord ++ tailWord_2535659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535659).length < 2 ^ (prefixWord ++ tailWord_2535659).sum := by decide
  have hdescent : baseEnd_2535659 < baseStart_2535659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535661 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2535661 : Nat := 118140960795 + 2535661 * 2 ^ 59
def prefixEnd_2535661 : Nat := 4983230072969 + 3 ^ 40 * 2535661 * 2
def baseEnd_2535661 : Nat := 868008579906872632250809

theorem tailTrace_2535661 : CollatzResearch.WordTrace tailWord_2535661 prefixEnd_2535661 868008579906872632250809 := by
  unfold tailWord_2535661
  simp only [CollatzResearch.WordTrace]
  refine ⟨92483154466740728266526837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61655436311160485511017891 92483154466740728266526837)
  ·
    refine ⟨8670295731256943274986891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92483154466740728266526837 8670295731256943274986891)
    ·
      refine ⟨13005443596885414912480337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8670295731256943274986891 13005443596885414912480337)
      ·
        refine ⟨9754082697664061184360253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13005443596885414912480337 9754082697664061184360253)
        ·
          refine ⟨3657781011624022944135095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9754082697664061184360253 3657781011624022944135095)
          ·
            refine ⟨5486671517436034416202643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657781011624022944135095 5486671517436034416202643)
            ·
              refine ⟨8230007276154051624303965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5486671517436034416202643 8230007276154051624303965)
              ·
                refine ⟨3086252728557769359113987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8230007276154051624303965 3086252728557769359113987)
                ·
                  refine ⟨4629379092836654038670981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3086252728557769359113987 4629379092836654038670981)
                  ·
                    refine ⟨868008579906872632250809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4629379092836654038670981 868008579906872632250809)
                    ·
                      rfl

theorem cell22_2535661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2535661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535661 prefixEnd_2535661 := by exact prefixLift 2535661
  have htrace : WordTrace (prefixWord ++ tailWord_2535661) baseStart_2535661 baseEnd_2535661 := by
    simpa [prefixWord, tailWord_2535661, baseEnd_2535661] using wordTrace_append hprefix tailTrace_2535661
  have hstable : (prefixWord ++ tailWord_2535661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535661).length < 2 ^ (prefixWord ++ tailWord_2535661).sum := by decide
  have hdescent : baseEnd_2535661 < baseStart_2535661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535672 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_2535672 : Nat := 118140960795 + 2535672 * 2 ^ 59
def prefixEnd_2535672 : Nat := 4983230072969 + 3 ^ 40 * 2535672 * 2
def baseEnd_2535672 : Nat := 868012345431672270225775

theorem tailTrace_2535672 : CollatzResearch.WordTrace tailWord_2535672 prefixEnd_2535672 868012345431672270225775 := by
  unfold tailWord_2535672
  simp only [CollatzResearch.WordTrace]
  refine ⟨46241777834850438572588635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61655703779800584763451513 46241777834850438572588635)
  ·
    refine ⟨69362666752275657858882953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46241777834850438572588635 69362666752275657858882953)
    ·
      refine ⟨52022000064206743394162215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69362666752275657858882953 52022000064206743394162215)
      ·
        refine ⟨78033000096310115091243323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52022000064206743394162215 78033000096310115091243323)
        ·
          refine ⟨117049500144465172636864985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78033000096310115091243323 117049500144465172636864985)
          ·
            refine ⟨87787125108348879477648739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117049500144465172636864985 87787125108348879477648739)
            ·
              refine ⟨131680687662523319216473109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87787125108348879477648739 131680687662523319216473109)
              ·
                refine ⟨6172532234180780588272177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131680687662523319216473109 6172532234180780588272177)
                ·
                  refine ⟨4629399175635585441204133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6172532234180780588272177 4629399175635585441204133)
                  ·
                    refine ⟨868012345431672270225775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4629399175635585441204133 868012345431672270225775)
                    ·
                      rfl

theorem cell22_2535672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_2535672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535672 prefixEnd_2535672 := by exact prefixLift 2535672
  have htrace : WordTrace (prefixWord ++ tailWord_2535672) baseStart_2535672 baseEnd_2535672 := by
    simpa [prefixWord, tailWord_2535672, baseEnd_2535672] using wordTrace_append hprefix tailTrace_2535672
  have hstable : (prefixWord ++ tailWord_2535672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535672).length < 2 ^ (prefixWord ++ tailWord_2535672).sum := by decide
  have hdescent : baseEnd_2535672 < baseStart_2535672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535674 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 4, 3]
def baseStart_2535674 : Nat := 118140960795 + 2535674 * 2 ^ 59
def prefixEnd_2535674 : Nat := 4983230072969 + 3 ^ 40 * 2535674 * 2
def baseEnd_2535674 : Nat := 868013030072544931675769

theorem tailTrace_2535674 : CollatzResearch.WordTrace tailWord_2535674 prefixEnd_2535674 868013030072544931675769 := by
  unfold tailWord_2535674
  simp only [CollatzResearch.WordTrace]
  refine ⟨23120907153923407871687519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61655752410462420991166717 23120907153923407871687519)
  ·
    refine ⟨34681360730885111807531279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23120907153923407871687519 34681360730885111807531279)
    ·
      refine ⟨52022041096327667711296919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34681360730885111807531279 52022041096327667711296919)
      ·
        refine ⟨78033061644491501566945379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52022041096327667711296919 78033061644491501566945379)
        ·
          refine ⟨117049592466737252350418069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78033061644491501566945379 117049592466737252350418069)
          ·
            refine ⟨5486699646878308703925847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117049592466737252350418069 5486699646878308703925847)
            ·
              refine ⟨8230049470317463055888771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5486699646878308703925847 8230049470317463055888771)
              ·
                refine ⟨12345074205476194583833157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8230049470317463055888771 12345074205476194583833157)
                ·
                  refine ⟨2314701413526786484468717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12345074205476194583833157 2314701413526786484468717)
                  ·
                    refine ⟨868013030072544931675769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314701413526786484468717 868013030072544931675769)
                    ·
                      rfl

theorem cell22_2535674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_2535674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535674 prefixEnd_2535674 := by exact prefixLift 2535674
  have htrace : WordTrace (prefixWord ++ tailWord_2535674) baseStart_2535674 baseEnd_2535674 := by
    simpa [prefixWord, tailWord_2535674, baseEnd_2535674] using wordTrace_append hprefix tailTrace_2535674
  have hstable : (prefixWord ++ tailWord_2535674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535674).length < 2 ^ (prefixWord ++ tailWord_2535674).sum := by decide
  have hdescent : baseEnd_2535674 < baseStart_2535674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535691 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 2, 3]
def baseStart_2535691 : Nat := 118140960795 + 2535691 * 2 ^ 59
def prefixEnd_2535691 : Nat := 4983230072969 + 3 ^ 40 * 2535691 * 2
def baseEnd_2535691 : Nat := 868018849519962554000717

theorem tailTrace_2535691 : CollatzResearch.WordTrace tailWord_2535691 prefixEnd_2535691 868018849519962554000717 := by
  unfold tailWord_2535691
  simp only [CollatzResearch.WordTrace]
  refine ⟨92484248656632043390118927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61656165771088028926745951 92484248656632043390118927)
  ·
    refine ⟨138726372984948065085178391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92484248656632043390118927 138726372984948065085178391)
    ·
      refine ⟨208089559477422097627767587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138726372984948065085178391 208089559477422097627767587)
      ·
        refine ⟨312134339216133146441651381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208089559477422097627767587 312134339216133146441651381)
        ·
          refine ⟨29262594301512482478904817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 312134339216133146441651381 29262594301512482478904817)
          ·
            refine ⟨21946945726134361859178613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29262594301512482478904817 21946945726134361859178613)
            ·
              refine ⟨2057526161825096424297995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21946945726134361859178613 2057526161825096424297995)
              ·
                refine ⟨3086289242737644636446993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057526161825096424297995 3086289242737644636446993)
                ·
                  refine ⟨2314716932053233477335245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3086289242737644636446993 2314716932053233477335245)
                  ·
                    refine ⟨868018849519962554000717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314716932053233477335245 868018849519962554000717)
                    ·
                      rfl

theorem cell22_2535691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 2, 3].length) (baseStart_2535691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535691 prefixEnd_2535691 := by exact prefixLift 2535691
  have htrace : WordTrace (prefixWord ++ tailWord_2535691) baseStart_2535691 baseEnd_2535691 := by
    simpa [prefixWord, tailWord_2535691, baseEnd_2535691] using wordTrace_append hprefix tailTrace_2535691
  have hstable : (prefixWord ++ tailWord_2535691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535691).length < 2 ^ (prefixWord ++ tailWord_2535691).sum := by decide
  have hdescent : baseEnd_2535691 < baseStart_2535691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535710 : List Nat := [4, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2535710 : Nat := 118140960795 + 2535710 * 2 ^ 59
def prefixEnd_2535710 : Nat := 4983230072969 + 3 ^ 40 * 2535710 * 2
def baseEnd_2535710 : Nat := 289341784536084279258553

theorem tailTrace_2535710 : CollatzResearch.WordTrace tailWord_2535710 prefixEnd_2535710 289341784536084279258553 := by
  unfold tailWord_2535710
  simp only [CollatzResearch.WordTrace]
  refine ⟨11560617705445401204382573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61656627762375473090040389 11560617705445401204382573)
  ·
    refine ⟨4335231639542025451643465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11560617705445401204382573 4335231639542025451643465)
    ·
      refine ⟨3251423729656519088732599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4335231639542025451643465 3251423729656519088732599)
      ·
        refine ⟨4877135594484778633098899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3251423729656519088732599 4877135594484778633098899)
        ·
          refine ⟨7315703391727167949648349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4877135594484778633098899 7315703391727167949648349)
          ·
            refine ⟨2743388771897687981118131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7315703391727167949648349 2743388771897687981118131)
            ·
              refine ⟨4115083157846531971677197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743388771897687981118131 4115083157846531971677197)
              ·
                refine ⟨1543156184192449489378949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4115083157846531971677197 1543156184192449489378949)
                ·
                  refine ⟨289341784536084279258553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543156184192449489378949 289341784536084279258553)
                  ·
                    rfl

theorem cell22_2535710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2535710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535710 prefixEnd_2535710 := by exact prefixLift 2535710
  have htrace : WordTrace (prefixWord ++ tailWord_2535710) baseStart_2535710 baseEnd_2535710 := by
    simpa [prefixWord, tailWord_2535710, baseEnd_2535710] using wordTrace_append hprefix tailTrace_2535710
  have hstable : (prefixWord ++ tailWord_2535710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535710).length < 2 ^ (prefixWord ++ tailWord_2535710).sum := by decide
  have hdescent : baseEnd_2535710 < baseStart_2535710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535736 : List Nat := [2, 1, 2, 1, 3, 1, 2, 6, 1, 3]
def baseStart_2535736 : Nat := 118140960795 + 2535736 * 2 ^ 59
def prefixEnd_2535736 : Nat := 4983230072969 + 3 ^ 40 * 2535736 * 2
def baseEnd_2535736 : Nat := 868034253939597436625579

theorem tailTrace_2535736 : CollatzResearch.WordTrace tailWord_2535736 prefixEnd_2535736 868034253939597436625579 := by
  unfold tailWord_2535736
  simp only [CollatzResearch.WordTrace]
  refine ⟨46242944970734508037753531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61657259960979344050338041 46242944970734508037753531)
  ·
    refine ⟨69364417456101762056630297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46242944970734508037753531 69364417456101762056630297)
    ·
      refine ⟨52023313092076321542472723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69364417456101762056630297 52023313092076321542472723)
      ·
        refine ⟨78034969638114482313709085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52023313092076321542472723 78034969638114482313709085)
        ·
          refine ⟨29263113614292930867640907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78034969638114482313709085 29263113614292930867640907)
          ·
            refine ⟨43894670421439396301461361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29263113614292930867640907 43894670421439396301461361)
            ·
              refine ⟨32921002816079547226096021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43894670421439396301461361 32921002816079547226096021)
              ·
                refine ⟨1543172007003728776223251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32921002816079547226096021 1543172007003728776223251)
                ·
                  refine ⟨2314758010505593164334877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543172007003728776223251 2314758010505593164334877)
                  ·
                    refine ⟨868034253939597436625579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314758010505593164334877 868034253939597436625579)
                    ·
                      rfl

theorem cell22_2535736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_2535736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535736 prefixEnd_2535736 := by exact prefixLift 2535736
  have htrace : WordTrace (prefixWord ++ tailWord_2535736) baseStart_2535736 baseEnd_2535736 := by
    simpa [prefixWord, tailWord_2535736, baseEnd_2535736] using wordTrace_append hprefix tailTrace_2535736
  have hstable : (prefixWord ++ tailWord_2535736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535736).length < 2 ^ (prefixWord ++ tailWord_2535736).sum := by decide
  have hdescent : baseEnd_2535736 < baseStart_2535736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535747 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 2, 5]
def baseStart_2535747 : Nat := 118140960795 + 2535747 * 2 ^ 59
def prefixEnd_2535747 : Nat := 4983230072969 + 3 ^ 40 * 2535747 * 2
def baseEnd_2535747 : Nat := 868038019464397074600545

theorem tailTrace_2535747 : CollatzResearch.WordTrace tailWord_2535747 prefixEnd_2535747 868038019464397074600545 := by
  unfold tailWord_2535747
  simp only [CollatzResearch.WordTrace]
  refine ⟨92486291144429164954157495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61657527429619443302771663 92486291144429164954157495)
  ·
    refine ⟨138729436716643747431236243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92486291144429164954157495 138729436716643747431236243)
    ·
      refine ⟨208094155074965621146854365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138729436716643747431236243 208094155074965621146854365)
      ·
        refine ⟨78035308153112107930070387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208094155074965621146854365 78035308153112107930070387)
        ·
          refine ⟨117052962229668161895105581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78035308153112107930070387 117052962229668161895105581)
          ·
            refine ⟨43894860836125560710664593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117052962229668161895105581 43894860836125560710664593)
            ·
              refine ⟨32921145627094170532998445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43894860836125560710664593 32921145627094170532998445)
              ·
                refine ⟨12345429610160313949874417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32921145627094170532998445 12345429610160313949874417)
                ·
                  refine ⟨9259072207620235462405813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12345429610160313949874417 9259072207620235462405813)
                  ·
                    refine ⟨868038019464397074600545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9259072207620235462405813 868038019464397074600545)
                    ·
                      rfl

theorem cell22_2535747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_2535747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535747 prefixEnd_2535747 := by exact prefixLift 2535747
  have htrace : WordTrace (prefixWord ++ tailWord_2535747) baseStart_2535747 baseEnd_2535747 := by
    simpa [prefixWord, tailWord_2535747, baseEnd_2535747] using wordTrace_append hprefix tailTrace_2535747
  have hstable : (prefixWord ++ tailWord_2535747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535747).length < 2 ^ (prefixWord ++ tailWord_2535747).sum := by decide
  have hdescent : baseEnd_2535747 < baseStart_2535747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535798 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_2535798 : Nat := 118140960795 + 2535798 * 2 ^ 59
def prefixEnd_2535798 : Nat := 4983230072969 + 3 ^ 40 * 2535798 * 2
def baseEnd_2535798 : Nat := 868055477806649941575389

theorem tailTrace_2535798 : CollatzResearch.WordTrace tailWord_2535798 prefixEnd_2535798 868055477806649941575389 := by
  unfold tailWord_2535798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5780509454202775041516503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61658767511496267109509365 5780509454202775041516503)
  ·
    refine ⟨8670764181304162562274755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5780509454202775041516503 8670764181304162562274755)
    ·
      refine ⟨13006146271956243843412133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8670764181304162562274755 13006146271956243843412133)
      ·
        refine ⟨2438652425991795720639775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13006146271956243843412133 2438652425991795720639775)
        ·
          refine ⟨3657978638987693580959663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438652425991795720639775 3657978638987693580959663)
          ·
            refine ⟨5486967958481540371439495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657978638987693580959663 5486967958481540371439495)
            ·
              refine ⟨8230451937722310557159243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5486967958481540371439495 8230451937722310557159243)
              ·
                refine ⟨12345677906583465835738865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8230451937722310557159243 12345677906583465835738865)
                ·
                  refine ⟨9259258429937599376804149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12345677906583465835738865 9259258429937599376804149)
                  ·
                    refine ⟨868055477806649941575389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9259258429937599376804149 868055477806649941575389)
                    ·
                      rfl

theorem cell22_2535798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_2535798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535798 prefixEnd_2535798 := by exact prefixLift 2535798
  have htrace : WordTrace (prefixWord ++ tailWord_2535798) baseStart_2535798 baseEnd_2535798 := by
    simpa [prefixWord, tailWord_2535798, baseEnd_2535798] using wordTrace_append hprefix tailTrace_2535798
  have hstable : (prefixWord ++ tailWord_2535798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535798).length < 2 ^ (prefixWord ++ tailWord_2535798).sum := by decide
  have hdescent : baseEnd_2535798 < baseStart_2535798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535807 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 3, 6]
def baseStart_2535807 : Nat := 118140960795 + 2535807 * 2 ^ 59
def prefixEnd_2535807 : Nat := 4983230072969 + 3 ^ 40 * 2535807 * 2
def baseEnd_2535807 : Nat := 868058558690576918100361

theorem tailTrace_2535807 : CollatzResearch.WordTrace tailWord_2535807 prefixEnd_2535807 868058558690576918100361 := by
  unfold tailWord_2535807
  simp only [CollatzResearch.WordTrace]
  refine ⟨92488479524211795201341675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61658986349474530134227783 92488479524211795201341675)
  ·
    refine ⟨138732719286317692802012513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92488479524211795201341675 138732719286317692802012513)
    ·
      refine ⟨104049539464738269601509385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138732719286317692802012513 104049539464738269601509385)
      ·
        refine ⟨78037154598553702201132039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104049539464738269601509385 78037154598553702201132039)
        ·
          refine ⟨117055731897830553301698059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78037154598553702201132039 117055731897830553301698059)
          ·
            refine ⟨175583597846745829952547089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117055731897830553301698059 175583597846745829952547089)
            ·
              refine ⟨131687698385059372464410317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175583597846745829952547089 131687698385059372464410317)
              ·
                refine ⟨49382886894397264674153869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131687698385059372464410317 49382886894397264674153869)
                ·
                  refine ⟨18518582585398974252807701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49382886894397264674153869 18518582585398974252807701)
                  ·
                    refine ⟨868058558690576918100361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18518582585398974252807701 868058558690576918100361)
                    ·
                      rfl

theorem cell22_2535807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_2535807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535807 prefixEnd_2535807 := by exact prefixLift 2535807
  have htrace : WordTrace (prefixWord ++ tailWord_2535807) baseStart_2535807 baseEnd_2535807 := by
    simpa [prefixWord, tailWord_2535807, baseEnd_2535807] using wordTrace_append hprefix tailTrace_2535807
  have hstable : (prefixWord ++ tailWord_2535807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535807).length < 2 ^ (prefixWord ++ tailWord_2535807).sum := by decide
  have hdescent : baseEnd_2535807 < baseStart_2535807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535843 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 2, 3]
def baseStart_2535843 : Nat := 118140960795 + 2535843 * 2 ^ 59
def prefixEnd_2535843 : Nat := 4983230072969 + 3 ^ 40 * 2535843 * 2
def baseEnd_2535843 : Nat := 868070882226284824200251

theorem tailTrace_2535843 : CollatzResearch.WordTrace tailWord_2535843 prefixEnd_2535843 868070882226284824200251 := by
  unfold tailWord_2535843
  simp only [CollatzResearch.WordTrace]
  refine ⟨92489792552081373349652183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61659861701387582233101455 92489792552081373349652183)
  ·
    refine ⟨138734688828122060024478275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92489792552081373349652183 138734688828122060024478275)
    ·
      refine ⟨208102033242183090036717413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138734688828122060024478275 208102033242183090036717413)
      ·
        refine ⟨39019131232909329381884515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208102033242183090036717413 39019131232909329381884515)
        ·
          refine ⟨58528696849363994072826773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39019131232909329381884515 58528696849363994072826773)
          ·
            refine ⟨2743532664813937222163755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58528696849363994072826773 2743532664813937222163755)
            ·
              refine ⟨4115298997220905833245633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743532664813937222163755 4115298997220905833245633)
              ·
                refine ⟨3086474247915679374934225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4115298997220905833245633 3086474247915679374934225)
                ·
                  refine ⟨2314855685936759531200669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3086474247915679374934225 2314855685936759531200669)
                  ·
                    refine ⟨868070882226284824200251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314855685936759531200669 868070882226284824200251)
                    ·
                      rfl

theorem cell22_2535843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 3].length) (baseStart_2535843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535843 prefixEnd_2535843 := by exact prefixLift 2535843
  have htrace : WordTrace (prefixWord ++ tailWord_2535843) baseStart_2535843 baseEnd_2535843 := by
    simpa [prefixWord, tailWord_2535843, baseEnd_2535843] using wordTrace_append hprefix tailTrace_2535843
  have hstable : (prefixWord ++ tailWord_2535843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535843).length < 2 ^ (prefixWord ++ tailWord_2535843).sum := by decide
  have hdescent : baseEnd_2535843 < baseStart_2535843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535901 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 5]
def baseStart_2535901 : Nat := 118140960795 + 2535901 * 2 ^ 59
def prefixEnd_2535901 : Nat := 4983230072969 + 3 ^ 40 * 2535901 * 2
def baseEnd_2535901 : Nat := 289363578937197335416691

theorem tailTrace_2535901 : CollatzResearch.WordTrace tailWord_2535901 prefixEnd_2535901 289363578937197335416691 := by
  unfold tailWord_2535901
  simp only [CollatzResearch.WordTrace]
  refine ⟨92491907985871249255263557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61661271990580832836842371 92491907985871249255263557)
  ·
    refine ⟨17342232747350859235361917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92491907985871249255263557 17342232747350859235361917)
    ·
      refine ⟨6503337280256572213260719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17342232747350859235361917 6503337280256572213260719)
      ·
        refine ⟨9755005920384858319891079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6503337280256572213260719 9755005920384858319891079)
        ·
          refine ⟨14632508880577287479836619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9755005920384858319891079 14632508880577287479836619)
          ·
            refine ⟨21948763320865931219754929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14632508880577287479836619 21948763320865931219754929)
            ·
              refine ⟨16461572490649448414816197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21948763320865931219754929 16461572490649448414816197)
              ·
                refine ⟨3086544841996771577778037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16461572490649448414816197 3086544841996771577778037)
                ·
                  refine ⟨289363578937197335416691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3086544841996771577778037 289363578937197335416691)
                  ·
                    rfl

theorem cell22_2535901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_2535901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535901 prefixEnd_2535901 := by exact prefixLift 2535901
  have htrace : WordTrace (prefixWord ++ tailWord_2535901) baseStart_2535901 baseEnd_2535901 := by
    simpa [prefixWord, tailWord_2535901, baseEnd_2535901] using wordTrace_append hprefix tailTrace_2535901
  have hstable : (prefixWord ++ tailWord_2535901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535901).length < 2 ^ (prefixWord ++ tailWord_2535901).sum := by decide
  have hdescent : baseEnd_2535901 < baseStart_2535901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535905 : List Nat := [1, 2, 3, 1, 2, 2, 5, 2, 1, 3]
def baseStart_2535905 : Nat := 118140960795 + 2535905 * 2 ^ 59
def prefixEnd_2535905 : Nat := 4983230072969 + 3 ^ 40 * 2535905 * 2
def baseEnd_2535905 : Nat := 868092106093337329150061

theorem tailTrace_2535905 : CollatzResearch.WordTrace tailWord_2535905 prefixEnd_2535905 868092106093337329150061 := by
  unfold tailWord_2535905
  simp only [CollatzResearch.WordTrace]
  refine ⟨92492053877856757938409169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61661369251904505292272779 92492053877856757938409169)
  ·
    refine ⟨69369040408392568453806877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92492053877856757938409169 69369040408392568453806877)
    ·
      refine ⟨26013390153147213170177579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69369040408392568453806877 26013390153147213170177579)
      ·
        refine ⟨39020085229720819755266369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26013390153147213170177579 39020085229720819755266369)
        ·
          refine ⟨29265063922290614816449777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39020085229720819755266369 29265063922290614816449777)
          ·
            refine ⟨21948797941717961112337333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29265063922290614816449777 21948797941717961112337333)
            ·
              refine ⟨2057699807036058854281625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21948797941717961112337333 2057699807036058854281625)
              ·
                refine ⟨1543274855277044140711219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057699807036058854281625 1543274855277044140711219)
                ·
                  refine ⟨2314912282915566211066829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543274855277044140711219 2314912282915566211066829)
                  ·
                    refine ⟨868092106093337329150061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314912282915566211066829 868092106093337329150061)
                    ·
                      rfl

theorem cell22_2535905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_2535905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535905 prefixEnd_2535905 := by exact prefixLift 2535905
  have htrace : WordTrace (prefixWord ++ tailWord_2535905) baseStart_2535905 baseEnd_2535905 := by
    simpa [prefixWord, tailWord_2535905, baseEnd_2535905] using wordTrace_append hprefix tailTrace_2535905
  have hstable : (prefixWord ++ tailWord_2535905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535905).length < 2 ^ (prefixWord ++ tailWord_2535905).sum := by decide
  have hdescent : baseEnd_2535905 < baseStart_2535905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535918 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_2535918 : Nat := 118140960795 + 2535918 * 2 ^ 59
def prefixEnd_2535918 : Nat := 4983230072969 + 3 ^ 40 * 2535918 * 2
def baseEnd_2535918 : Nat := 289365518753003209525007

theorem tailTrace_2535918 : CollatzResearch.WordTrace tailWord_2535918 prefixEnd_2535918 289365518753003209525007 := by
  unfold tailWord_2535918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11561566003351207644829051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61661685351206440772421605 11561566003351207644829051)
  ·
    refine ⟨17342349005026811467243577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11561566003351207644829051 17342349005026811467243577)
    ·
      refine ⟨13006761753770108600432683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17342349005026811467243577 13006761753770108600432683)
      ·
        refine ⟨19510142630655162900649025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13006761753770108600432683 19510142630655162900649025)
        ·
          refine ⟨14632606972991372175486769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19510142630655162900649025 14632606972991372175486769)
          ·
            refine ⟨10974455229743529131615077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14632606972991372175486769 10974455229743529131615077)
            ·
              refine ⟨2057710355576911712177827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10974455229743529131615077 2057710355576911712177827)
              ·
                refine ⟨3086565533365367568266741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057710355576911712177827 3086565533365367568266741)
                ·
                  refine ⟨289365518753003209525007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3086565533365367568266741 289365518753003209525007)
                  ·
                    rfl

theorem cell22_2535918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_2535918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535918 prefixEnd_2535918 := by exact prefixLift 2535918
  have htrace : WordTrace (prefixWord ++ tailWord_2535918) baseStart_2535918 baseEnd_2535918 := by
    simpa [prefixWord, tailWord_2535918, baseEnd_2535918] using wordTrace_append hprefix tailTrace_2535918
  have hstable : (prefixWord ++ tailWord_2535918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535918).length < 2 ^ (prefixWord ++ tailWord_2535918).sum := by decide
  have hdescent : baseEnd_2535918 < baseStart_2535918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535929 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 6]
def baseStart_2535929 : Nat := 118140960795 + 2535929 * 2 ^ 59
def prefixEnd_2535929 : Nat := 4983230072969 + 3 ^ 40 * 2535929 * 2
def baseEnd_2535929 : Nat := 289366773927936422183329

theorem tailTrace_2535929 : CollatzResearch.WordTrace tailWord_2535929 prefixEnd_2535929 289366773927936422183329 := by
  unfold tailWord_2535929
  simp only [CollatzResearch.WordTrace]
  refine ⟨92492929229769810037282841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61661952819846540024855227 92492929229769810037282841)
  ·
    refine ⟨69369696922327357527962131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92492929229769810037282841 69369696922327357527962131)
    ·
      refine ⟨104054545383491036291943197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69369696922327357527962131 104054545383491036291943197)
      ·
        refine ⟨39020454518809138609478699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104054545383491036291943197 39020454518809138609478699)
        ·
          refine ⟨58530681778213707914218049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39020454518809138609478699 58530681778213707914218049)
          ·
            refine ⟨43898011333660280935663537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58530681778213707914218049 43898011333660280935663537)
            ·
              refine ⟨32923508500245210701747653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43898011333660280935663537 32923508500245210701747653)
              ·
                refine ⟨6173157843795977006577685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32923508500245210701747653 6173157843795977006577685)
                ·
                  refine ⟨289366773927936422183329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6173157843795977006577685 289366773927936422183329)
                  ·
                    rfl

theorem cell22_2535929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_2535929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535929 prefixEnd_2535929 := by exact prefixLift 2535929
  have htrace : WordTrace (prefixWord ++ tailWord_2535929) baseStart_2535929 baseEnd_2535929 := by
    simpa [prefixWord, tailWord_2535929, baseEnd_2535929] using wordTrace_append hprefix tailTrace_2535929
  have hstable : (prefixWord ++ tailWord_2535929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535929).length < 2 ^ (prefixWord ++ tailWord_2535929).sum := by decide
  have hdescent : baseEnd_2535929 < baseStart_2535929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535978 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2535978 : Nat := 118140960795 + 2535978 * 2 ^ 59
def prefixEnd_2535978 : Nat := 4983230072969 + 3 ^ 40 * 2535978 * 2
def baseEnd_2535978 : Nat := 868117095485189472074837

theorem tailTrace_2535978 : CollatzResearch.WordTrace tailWord_2535978 prefixEnd_2535978 868117095485189472074837 := by
  unfold tailWord_2535978
  simp only [CollatzResearch.WordTrace]
  refine ⟨23123679101648072851454147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61663144271061527603877725 23123679101648072851454147)
  ·
    refine ⟨34685518652472109277181221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23123679101648072851454147 34685518652472109277181221)
    ·
      refine ⟨6503534747338520489471479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34685518652472109277181221 6503534747338520489471479)
      ·
        refine ⟨9755302121007780734207219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6503534747338520489471479 9755302121007780734207219)
        ·
          refine ⟨14632953181511671101310829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9755302121007780734207219 14632953181511671101310829)
          ·
            refine ⟨5487357443066876662991561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14632953181511671101310829 5487357443066876662991561)
            ·
              refine ⟨4115518082300157497243671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5487357443066876662991561 4115518082300157497243671)
              ·
                refine ⟨6173277123450236245865507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4115518082300157497243671 6173277123450236245865507)
                ·
                  refine ⟨9259915685175354368798261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6173277123450236245865507 9259915685175354368798261)
                  ·
                    refine ⟨868117095485189472074837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9259915685175354368798261 868117095485189472074837)
                    ·
                      rfl

theorem cell22_2535978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2535978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535978 prefixEnd_2535978 := by exact prefixLift 2535978
  have htrace : WordTrace (prefixWord ++ tailWord_2535978) baseStart_2535978 baseEnd_2535978 := by
    simpa [prefixWord, tailWord_2535978, baseEnd_2535978] using wordTrace_append hprefix tailTrace_2535978
  have hstable : (prefixWord ++ tailWord_2535978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535978).length < 2 ^ (prefixWord ++ tailWord_2535978).sum := by decide
  have hdescent : baseEnd_2535978 < baseStart_2535978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535991 : List Nat := [1, 1, 3, 1, 2, 3, 5, 6]
def baseStart_2535991 : Nat := 118140960795 + 2535991 * 2 ^ 59
def prefixEnd_2535991 : Nat := 4983230072969 + 3 ^ 40 * 2535991 * 2
def baseEnd_2535991 : Nat := 96457949516762419055533

theorem tailTrace_2535991 : CollatzResearch.WordTrace tailWord_2535991 prefixEnd_2535991 96457949516762419055533 := by
  unfold tailWord_2535991
  simp only [CollatzResearch.WordTrace]
  refine ⟨92495190555545194626039827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61663460370363463084026551 92495190555545194626039827)
  ·
    refine ⟨138742785833317791939059741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92495190555545194626039827 138742785833317791939059741)
    ·
      refine ⟨52028544687494171977147403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138742785833317791939059741 52028544687494171977147403)
      ·
        refine ⟨78042817031241257965721105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52028544687494171977147403 78042817031241257965721105)
        ·
          refine ⟨58532112773430943474290829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78042817031241257965721105 58532112773430943474290829)
          ·
            refine ⟨21949542290036603802859061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58532112773430943474290829 21949542290036603802859061)
            ·
              refine ⟨2057769589690931606518037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21949542290036603802859061 2057769589690931606518037)
              ·
                refine ⟨96457949516762419055533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2057769589690931606518037 96457949516762419055533)
                ·
                  rfl

theorem cell22_2535991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 6].length) (baseStart_2535991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2535991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2535991 prefixEnd_2535991 := by exact prefixLift 2535991
  have htrace : WordTrace (prefixWord ++ tailWord_2535991) baseStart_2535991 baseEnd_2535991 := by
    simpa [prefixWord, tailWord_2535991, baseEnd_2535991] using wordTrace_append hprefix tailTrace_2535991
  have hstable : (prefixWord ++ tailWord_2535991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535991).length < 2 ^ (prefixWord ++ tailWord_2535991).sum := by decide
  have hdescent : baseEnd_2535991 < baseStart_2535991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536023 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 3, 3]
def baseStart_2536023 : Nat := 118140960795 + 2536023 * 2 ^ 59
def prefixEnd_2536023 : Nat := 4983230072969 + 3 ^ 40 * 2536023 * 2
def baseEnd_2536023 : Nat := 868132499904824354699699

theorem tailTrace_2536023 : CollatzResearch.WordTrace tailWord_2536023 prefixEnd_2536023 868132499904824354699699 := by
  unfold tailWord_2536023
  simp only [CollatzResearch.WordTrace]
  refine ⟨92496357691429264091204723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61664238460952842727469815 92496357691429264091204723)
  ·
    refine ⟨138744536537143896136807085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92496357691429264091204723 138744536537143896136807085)
    ·
      refine ⟨52029201201428961051302657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138744536537143896136807085 52029201201428961051302657)
      ·
        refine ⟨39021900901071720788476993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52029201201428961051302657 39021900901071720788476993)
        ·
          refine ⟨29266425675803790591357745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39021900901071720788476993 29266425675803790591357745)
          ·
            refine ⟨21949819256852842943518309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29266425675803790591357745 21949819256852842943518309)
            ·
              refine ⟨4115591110659908051909683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21949819256852842943518309 4115591110659908051909683)
              ·
                refine ⟨6173386665989862077864525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4115591110659908051909683 6173386665989862077864525)
                ·
                  refine ⟨2315019999746198279199197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6173386665989862077864525 2315019999746198279199197)
                  ·
                    refine ⟨868132499904824354699699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315019999746198279199197 868132499904824354699699)
                    ·
                      rfl

theorem cell22_2536023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_2536023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536023 prefixEnd_2536023 := by exact prefixLift 2536023
  have htrace : WordTrace (prefixWord ++ tailWord_2536023) baseStart_2536023 baseEnd_2536023 := by
    simpa [prefixWord, tailWord_2536023, baseEnd_2536023] using wordTrace_append hprefix tailTrace_2536023
  have hstable : (prefixWord ++ tailWord_2536023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536023).length < 2 ^ (prefixWord ++ tailWord_2536023).sum := by decide
  have hdescent : baseEnd_2536023 < baseStart_2536023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536057 : List Nat := [1, 2, 1, 3, 3, 4, 1, 3, 1, 3]
def baseStart_2536057 : Nat := 118140960795 + 2536057 * 2 ^ 59
def prefixEnd_2536057 : Nat := 4983230072969 + 3 ^ 40 * 2536057 * 2
def baseEnd_2536057 : Nat := 868144138799659599349595

theorem tailTrace_2536057 : CollatzResearch.WordTrace tailWord_2536057 prefixEnd_2536057 868144138799659599349595 := by
  unfold tailWord_2536057
  simp only [CollatzResearch.WordTrace]
  refine ⟨92497597773306087897942425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61665065182204058598628283 92497597773306087897942425)
  ·
    refine ⟨69373198329979565923456819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92497597773306087897942425 69373198329979565923456819)
    ·
      refine ⟨104059797494969348885185229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69373198329979565923456819 104059797494969348885185229)
      ·
        refine ⟨39022424060613505831944461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104059797494969348885185229 39022424060613505831944461)
        ·
          refine ⟨14633409022730064686979173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39022424060613505831944461 14633409022730064686979173)
          ·
            refine ⟨2743764191761887128808595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14633409022730064686979173 2743764191761887128808595)
            ·
              refine ⟨4115646287642830693212893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743764191761887128808595 4115646287642830693212893)
              ·
                refine ⟨1543367357866061509954835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4115646287642830693212893 1543367357866061509954835)
                ·
                  refine ⟨2315051036799092264932253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543367357866061509954835 2315051036799092264932253)
                  ·
                    refine ⟨868144138799659599349595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315051036799092264932253 868144138799659599349595)
                    ·
                      rfl

theorem cell22_2536057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 1, 3].length) (baseStart_2536057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536057 prefixEnd_2536057 := by exact prefixLift 2536057
  have htrace : WordTrace (prefixWord ++ tailWord_2536057) baseStart_2536057 baseEnd_2536057 := by
    simpa [prefixWord, tailWord_2536057, baseEnd_2536057] using wordTrace_append hprefix tailTrace_2536057
  have hstable : (prefixWord ++ tailWord_2536057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536057).length < 2 ^ (prefixWord ++ tailWord_2536057).sum := by decide
  have hdescent : baseEnd_2536057 < baseStart_2536057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536074 : List Nat := [3, 1, 2, 3, 3, 1, 3, 2, 1, 3]
def baseStart_2536074 : Nat := 118140960795 + 2536074 * 2 ^ 59
def prefixEnd_2536074 : Nat := 4983230072969 + 3 ^ 40 * 2536074 * 2
def baseEnd_2536074 : Nat := 868149958247077221674543

theorem tailTrace_2536074 : CollatzResearch.WordTrace tailWord_2536074 prefixEnd_2536074 868149958247077221674543 := by
  unfold tailWord_2536074
  simp only [CollatzResearch.WordTrace]
  refine ⟨23124554453561124950327819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61665478542829666534207517 23124554453561124950327819)
  ·
    refine ⟨34686831680341687425491729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23124554453561124950327819 34686831680341687425491729)
    ·
      refine ⟨26015123760256265569118797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34686831680341687425491729 26015123760256265569118797)
      ·
        refine ⟨9755671410096099588419549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26015123760256265569118797 9755671410096099588419549)
        ·
          refine ⟨3658376778786037345657331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9755671410096099588419549 3658376778786037345657331)
          ·
            refine ⟨5487565168179056018485997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3658376778786037345657331 5487565168179056018485997)
            ·
              refine ⟨2057836938067146006932249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5487565168179056018485997 2057836938067146006932249)
              ·
                refine ⟨1543377703550359505199187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057836938067146006932249 1543377703550359505199187)
                ·
                  refine ⟨2315066555325539257798781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543377703550359505199187 2315066555325539257798781)
                  ·
                    refine ⟨868149958247077221674543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315066555325539257798781 868149958247077221674543)
                    ·
                      rfl

theorem cell22_2536074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_2536074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536074 prefixEnd_2536074 := by exact prefixLift 2536074
  have htrace : WordTrace (prefixWord ++ tailWord_2536074) baseStart_2536074 baseEnd_2536074 := by
    simpa [prefixWord, tailWord_2536074, baseEnd_2536074] using wordTrace_append hprefix tailTrace_2536074
  have hstable : (prefixWord ++ tailWord_2536074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536074).length < 2 ^ (prefixWord ++ tailWord_2536074).sum := by decide
  have hdescent : baseEnd_2536074 < baseStart_2536074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536117 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2536117 : Nat := 118140960795 + 2536117 * 2 ^ 59
def prefixEnd_2536117 : Nat := 4983230072969 + 3 ^ 40 * 2536117 * 2
def baseEnd_2536117 : Nat := 868164678025839442849411

theorem tailTrace_2536117 : CollatzResearch.WordTrace tailWord_2536117 prefixEnd_2536117 868164678025839442849411 := by
  unfold tailWord_2536117
  simp only [CollatzResearch.WordTrace]
  refine ⟨92499786153088718145126605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61666524102059145430084403 92499786153088718145126605)
  ·
    refine ⟨34687419807408269304422477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92499786153088718145126605 34687419807408269304422477)
    ·
      refine ⟨13007782427778100989158429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34687419807408269304422477 13007782427778100989158429)
      ·
        refine ⟨4877918410416787870934411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13007782427778100989158429 4877918410416787870934411)
        ·
          refine ⟨7316877615625181806401617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4877918410416787870934411 7316877615625181806401617)
          ·
            refine ⟨5487658211718886354801213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7316877615625181806401617 5487658211718886354801213)
            ·
              refine ⟨2057871829394582383050455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5487658211718886354801213 2057871829394582383050455)
              ·
                refine ⟨3086807744091873574575683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057871829394582383050455 3086807744091873574575683)
                ·
                  refine ⟨4630211616137810361863525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3086807744091873574575683 4630211616137810361863525)
                  ·
                    refine ⟨868164678025839442849411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4630211616137810361863525 868164678025839442849411)
                    ·
                      rfl

theorem cell22_2536117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2536117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536117 prefixEnd_2536117 := by exact prefixLift 2536117
  have htrace : WordTrace (prefixWord ++ tailWord_2536117) baseStart_2536117 baseEnd_2536117 := by
    simpa [prefixWord, tailWord_2536117, baseEnd_2536117] using wordTrace_append hprefix tailTrace_2536117
  have hstable : (prefixWord ++ tailWord_2536117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536117).length < 2 ^ (prefixWord ++ tailWord_2536117).sum := by decide
  have hdescent : baseEnd_2536117 < baseStart_2536117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536128 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_2536128 : Nat := 118140960795 + 2536128 * 2 ^ 59
def prefixEnd_2536128 : Nat := 4983230072969 + 3 ^ 40 * 2536128 * 2
def baseEnd_2536128 : Nat := 868168443550639080824377

theorem tailTrace_2536128 : CollatzResearch.WordTrace tailWord_2536128 prefixEnd_2536128 868168443550639080824377 := by
  unfold tailWord_2536128
  simp only [CollatzResearch.WordTrace]
  refine ⟨46250093678024433511888519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61666791570699244682518025 46250093678024433511888519)
  ·
    refine ⟨69375140517036650267832779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46250093678024433511888519 69375140517036650267832779)
    ·
      refine ⟨104062710775554975401749169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69375140517036650267832779 104062710775554975401749169)
      ·
        refine ⟨78047033081666231551311877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104062710775554975401749169 78047033081666231551311877)
        ·
          refine ⟨14633818702812418415870977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78047033081666231551311877 14633818702812418415870977)
          ·
            refine ⟨10975364027109313811903233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14633818702812418415870977 10975364027109313811903233)
            ·
              refine ⟨8231523020331985358927425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10975364027109313811903233 8231523020331985358927425)
              ·
                refine ⟨6173642265248989019195569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8231523020331985358927425 6173642265248989019195569)
                ·
                  refine ⟨4630231698936741764396677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6173642265248989019195569 4630231698936741764396677)
                  ·
                    refine ⟨868168443550639080824377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4630231698936741764396677 868168443550639080824377)
                    ·
                      rfl

theorem cell22_2536128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_2536128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536128 prefixEnd_2536128 := by exact prefixLift 2536128
  have htrace : WordTrace (prefixWord ++ tailWord_2536128) baseStart_2536128 baseEnd_2536128 := by
    simpa [prefixWord, tailWord_2536128, baseEnd_2536128] using wordTrace_append hprefix tailTrace_2536128
  have hstable : (prefixWord ++ tailWord_2536128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536128).length < 2 ^ (prefixWord ++ tailWord_2536128).sum := by decide
  have hdescent : baseEnd_2536128 < baseStart_2536128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536132 : List Nat := [2, 3, 3, 1, 1, 2, 4, 2, 4]
def baseStart_2536132 : Nat := 118140960795 + 2536132 * 2 ^ 59
def prefixEnd_2536132 : Nat := 4983230072969 + 3 ^ 40 * 2536132 * 2
def baseEnd_2536132 : Nat := 289389937610794801241455

theorem tailTrace_2536132 : CollatzResearch.WordTrace tailWord_2536132 prefixEnd_2536132 289389937610794801241455 := by
  unfold tailWord_2536132
  simp only [CollatzResearch.WordTrace]
  refine ⟨46250166624017187853461325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61666888832022917137948433 46250166624017187853461325)
  ·
    refine ⟨17343812484006445445047997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46250166624017187853461325 17343812484006445445047997)
    ·
      refine ⟨6503929681502417041892999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17343812484006445445047997 6503929681502417041892999)
      ·
        refine ⟨9755894522253625562839499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6503929681502417041892999 9755894522253625562839499)
        ·
          refine ⟨14633841783380438344259249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9755894522253625562839499 14633841783380438344259249)
          ·
            refine ⟨10975381337535328758194437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14633841783380438344259249 10975381337535328758194437)
            ·
              refine ⟨2057884000787874142161457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10975381337535328758194437 2057884000787874142161457)
              ·
                refine ⟨1543413000590905606621093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057884000787874142161457 1543413000590905606621093)
                ·
                  refine ⟨289389937610794801241455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543413000590905606621093 289389937610794801241455)
                  ·
                    rfl

theorem cell22_2536132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_2536132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536132 prefixEnd_2536132 := by exact prefixLift 2536132
  have htrace : WordTrace (prefixWord ++ tailWord_2536132) baseStart_2536132 baseEnd_2536132 := by
    simpa [prefixWord, tailWord_2536132, baseEnd_2536132] using wordTrace_append hprefix tailTrace_2536132
  have hstable : (prefixWord ++ tailWord_2536132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536132).length < 2 ^ (prefixWord ++ tailWord_2536132).sum := by decide
  have hdescent : baseEnd_2536132 < baseStart_2536132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536171 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 7]
def baseStart_2536171 : Nat := 118140960795 + 2536171 * 2 ^ 59
def prefixEnd_2536171 : Nat := 4983230072969 + 3 ^ 40 * 2536171 * 2
def baseEnd_2536171 : Nat := 289394387776467100666415

theorem tailTrace_2536171 : CollatzResearch.WordTrace tailWord_2536171 prefixEnd_2536171 289394387776467100666415 := by
  unfold tailWord_2536171
  simp only [CollatzResearch.WordTrace]
  refine ⟨92501755694893085367592367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61667837129928723578394911 92501755694893085367592367)
  ·
    refine ⟨138752633542339628051388551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92501755694893085367592367 138752633542339628051388551)
    ·
      refine ⟨208128950313509442077082827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138752633542339628051388551 208128950313509442077082827)
      ·
        refine ⟨312193425470264163115624241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208128950313509442077082827 312193425470264163115624241)
        ·
          refine ⟨234145069102698122336718181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312193425470264163115624241 234145069102698122336718181)
          ·
            refine ⟨43902200456755897938134659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234145069102698122336718181 43902200456755897938134659)
            ·
              refine ⟨65853300685133846907201989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43902200456755897938134659 65853300685133846907201989)
              ·
                refine ⟨12347493878462596295100373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65853300685133846907201989 12347493878462596295100373)
                ·
                  refine ⟨289394387776467100666415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12347493878462596295100373 289394387776467100666415)
                  ·
                    rfl

theorem cell22_2536171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 7].length) (baseStart_2536171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536171 prefixEnd_2536171 := by exact prefixLift 2536171
  have htrace : WordTrace (prefixWord ++ tailWord_2536171) baseStart_2536171 baseEnd_2536171 := by
    simpa [prefixWord, tailWord_2536171, baseEnd_2536171] using wordTrace_append hprefix tailTrace_2536171
  have hstable : (prefixWord ++ tailWord_2536171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536171).length < 2 ^ (prefixWord ++ tailWord_2536171).sum := by decide
  have hdescent : baseEnd_2536171 < baseStart_2536171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536188 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 7]
def baseStart_2536188 : Nat := 118140960795 + 2536188 * 2 ^ 59
def prefixEnd_2536188 : Nat := 4983230072969 + 3 ^ 40 * 2536188 * 2
def baseEnd_2536188 : Nat := 289396327592272974774731

theorem tailTrace_2536188 : CollatzResearch.WordTrace tailWord_2536188 prefixEnd_2536188 289396327592272974774731 := by
  unfold tailWord_2536188
  simp only [CollatzResearch.WordTrace]
  refine ⟨46251187867915748635480609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61668250490554331513974145 46251187867915748635480609)
  ·
    refine ⟨34688390900936811476610457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46251187867915748635480609 34688390900936811476610457)
    ·
      refine ⟨26016293175702608607457843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34688390900936811476610457 26016293175702608607457843)
      ·
        refine ⟨39024439763553912911186765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26016293175702608607457843 39024439763553912911186765)
        ·
          refine ⟨14634164911332717341695037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39024439763553912911186765 14634164911332717341695037)
          ·
            refine ⟨5487811841749769003135639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14634164911332717341695037 5487811841749769003135639)
            ·
              refine ⟨8231717762624653504703459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5487811841749769003135639 8231717762624653504703459)
              ·
                refine ⟨12347576643936980257055189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8231717762624653504703459 12347576643936980257055189)
                ·
                  refine ⟨289396327592272974774731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12347576643936980257055189 289396327592272974774731)
                  ·
                    rfl

theorem cell22_2536188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_2536188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536188 prefixEnd_2536188 := by exact prefixLift 2536188
  have htrace : WordTrace (prefixWord ++ tailWord_2536188) baseStart_2536188 baseEnd_2536188 := by
    simpa [prefixWord, tailWord_2536188, baseEnd_2536188] using wordTrace_append hprefix tailTrace_2536188
  have hstable : (prefixWord ++ tailWord_2536188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536188).length < 2 ^ (prefixWord ++ tailWord_2536188).sum := by decide
  have hdescent : baseEnd_2536188 < baseStart_2536188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536263 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 6, 4]
def baseStart_2536263 : Nat := 118140960795 + 2536263 * 2 ^ 59
def prefixEnd_2536263 : Nat := 4983230072969 + 3 ^ 40 * 2536263 * 2
def baseEnd_2536263 : Nat := 868214656809543728698963

theorem tailTrace_2536263 : CollatzResearch.WordTrace tailWord_2536263 prefixEnd_2536263 868214656809543728698963 := by
  unfold tailWord_2536263
  simp only [CollatzResearch.WordTrace]
  refine ⟨92505111210559785079941443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61670074140373190053294295 92505111210559785079941443)
  ·
    refine ⟨138757666815839677619912165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92505111210559785079941443 138757666815839677619912165)
    ·
      refine ⟨26017062527969939553733531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138757666815839677619912165 26017062527969939553733531)
      ·
        refine ⟨39025593791954909330600297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26017062527969939553733531 39025593791954909330600297)
        ·
          refine ⟨29269195343966181997950223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39025593791954909330600297 29269195343966181997950223)
          ·
            refine ⟨43903793015949272996925335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29269195343966181997950223 43903793015949272996925335)
            ·
              refine ⟨65855689523923909495388003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43903793015949272996925335 65855689523923909495388003)
              ·
                refine ⟨98783534285885864243082005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65855689523923909495388003 98783534285885864243082005)
                ·
                  refine ⟨4630478169650899886394469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98783534285885864243082005 4630478169650899886394469)
                  ·
                    refine ⟨868214656809543728698963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4630478169650899886394469 868214656809543728698963)
                    ·
                      rfl

theorem cell22_2536263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_2536263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536263 prefixEnd_2536263 := by exact prefixLift 2536263
  have htrace : WordTrace (prefixWord ++ tailWord_2536263) baseStart_2536263 baseEnd_2536263 := by
    simpa [prefixWord, tailWord_2536263, baseEnd_2536263] using wordTrace_append hprefix tailTrace_2536263
  have hstable : (prefixWord ++ tailWord_2536263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536263).length < 2 ^ (prefixWord ++ tailWord_2536263).sum := by decide
  have hdescent : baseEnd_2536263 < baseStart_2536263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536327 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 3, 3]
def baseStart_2536327 : Nat := 118140960795 + 2536327 * 2 ^ 59
def prefixEnd_2536327 : Nat := 4983230072969 + 3 ^ 40 * 2536327 * 2
def baseEnd_2536327 : Nat := 868236565317468895098767

theorem tailTrace_2536327 : CollatzResearch.WordTrace tailWord_2536327 prefixEnd_2536327 868236565317468895098767 := by
  unfold tailWord_2536327
  simp only [CollatzResearch.WordTrace]
  refine ⟨92507445482327924010271235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61671630321551949340180823 92507445482327924010271235)
  ·
    refine ⟨138761168223491886015406853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92507445482327924010271235 138761168223491886015406853)
    ·
      refine ⟨26017719041904728627888785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138761168223491886015406853 26017719041904728627888785)
      ·
        refine ⟨19513289281428546470916589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26017719041904728627888785 19513289281428546470916589)
        ·
          refine ⟨7317483480535704926593721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19513289281428546470916589 7317483480535704926593721)
          ·
            refine ⟨5488112610401778694945291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7317483480535704926593721 5488112610401778694945291)
            ·
              refine ⟨8232168915602668042417937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5488112610401778694945291 8232168915602668042417937)
              ·
                refine ⟨6174126686702001031813453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8232168915602668042417937 6174126686702001031813453)
                ·
                  refine ⟨2315297507513250386930045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6174126686702001031813453 2315297507513250386930045)
                  ·
                    refine ⟨868236565317468895098767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315297507513250386930045 868236565317468895098767)
                    ·
                      rfl

theorem cell22_2536327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_2536327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536327 prefixEnd_2536327 := by exact prefixLift 2536327
  have htrace : WordTrace (prefixWord ++ tailWord_2536327) baseStart_2536327 baseEnd_2536327 := by
    simpa [prefixWord, tailWord_2536327, baseEnd_2536327] using wordTrace_append hprefix tailTrace_2536327
  have hstable : (prefixWord ++ tailWord_2536327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536327).length < 2 ^ (prefixWord ++ tailWord_2536327).sum := by decide
  have hdescent : baseEnd_2536327 < baseStart_2536327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536340 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 7]
def baseStart_2536340 : Nat := 118140960795 + 2536340 * 2 ^ 59
def prefixEnd_2536340 : Nat := 4983230072969 + 3 ^ 40 * 2536340 * 2
def baseEnd_2536340 : Nat := 289413671827713731507909

theorem tailTrace_2536340 : CollatzResearch.WordTrace tailWord_2536340 prefixEnd_2536340 289413671827713731507909 := by
  unfold tailWord_2536340
  simp only [CollatzResearch.WordTrace]
  refine ⟨46253959815640413615247237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61671946420853884820329649 46253959815640413615247237)
  ·
    refine ⟨8672617465432577552858857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46253959815640413615247237 8672617465432577552858857)
    ·
      refine ⟨6504463099074433164644143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8672617465432577552858857 6504463099074433164644143)
      ·
        refine ⟨9756694648611649746966215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6504463099074433164644143 9756694648611649746966215)
        ·
          refine ⟨14635041972917474620449323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9756694648611649746966215 14635041972917474620449323)
          ·
            refine ⟨21952562959376211930673985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14635041972917474620449323 21952562959376211930673985)
            ·
              refine ⟨16464422219532158948005489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21952562959376211930673985 16464422219532158948005489)
              ·
                refine ⟨12348316664649119211004117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16464422219532158948005489 12348316664649119211004117)
                ·
                  refine ⟨289413671827713731507909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12348316664649119211004117 289413671827713731507909)
                  ·
                    rfl

theorem cell22_2536340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_2536340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536340 prefixEnd_2536340 := by exact prefixLift 2536340
  have htrace : WordTrace (prefixWord ++ tailWord_2536340) baseStart_2536340 baseEnd_2536340 := by
    simpa [prefixWord, tailWord_2536340, baseEnd_2536340] using wordTrace_append hprefix tailTrace_2536340
  have hstable : (prefixWord ++ tailWord_2536340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536340).length < 2 ^ (prefixWord ++ tailWord_2536340).sum := by decide
  have hdescent : baseEnd_2536340 < baseStart_2536340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536417 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 2, 3]
def baseStart_2536417 : Nat := 118140960795 + 2536417 * 2 ^ 59
def prefixEnd_2536417 : Nat := 4983230072969 + 3 ^ 40 * 2536417 * 2
def baseEnd_2536417 : Nat := 868267374156738660348491

theorem tailTrace_2536417 : CollatzResearch.WordTrace tailWord_2536417 prefixEnd_2536417 868267374156738660348491 := by
  unfold tailWord_2536417
  simp only [CollatzResearch.WordTrace]
  refine ⟨92510728052001869381047505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61673818701334579587365003 92510728052001869381047505)
  ·
    refine ⟨69383046039001402035785629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92510728052001869381047505 69383046039001402035785629)
    ·
      refine ⟨26018642264625525763419611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69383046039001402035785629 26018642264625525763419611)
      ·
        refine ⟨39027963396938288645129417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26018642264625525763419611 39027963396938288645129417)
        ·
          refine ⟨29270972547703716483847063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39027963396938288645129417 29270972547703716483847063)
          ·
            refine ⟨43906458821555574725770595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29270972547703716483847063 43906458821555574725770595)
            ·
              refine ⟨65859688232333362088655893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43906458821555574725770595 65859688232333362088655893)
              ·
                refine ⟨3087172885890626347905745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65859688232333362088655893 3087172885890626347905745)
                ·
                  refine ⟨2315379664417969760929309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3087172885890626347905745 2315379664417969760929309)
                  ·
                    refine ⟨868267374156738660348491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315379664417969760929309 868267374156738660348491)
                    ·
                      rfl

theorem cell22_2536417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_2536417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536417 prefixEnd_2536417 := by exact prefixLift 2536417
  have htrace : WordTrace (prefixWord ++ tailWord_2536417) baseStart_2536417 baseEnd_2536417 := by
    simpa [prefixWord, tailWord_2536417, baseEnd_2536417] using wordTrace_append hprefix tailTrace_2536417
  have hstable : (prefixWord ++ tailWord_2536417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536417).length < 2 ^ (prefixWord ++ tailWord_2536417).sum := by decide
  have hdescent : baseEnd_2536417 < baseStart_2536417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536419 : List Nat := [1, 1, 1, 6, 1, 1, 5, 2, 4]
def baseStart_2536419 : Nat := 118140960795 + 2536419 * 2 ^ 59
def prefixEnd_2536419 : Nat := 4983230072969 + 3 ^ 40 * 2536419 * 2
def baseEnd_2536419 : Nat := 289422686265870440599495

theorem tailTrace_2536419 : CollatzResearch.WordTrace tailWord_2536419 prefixEnd_2536419 289422686265870440599495 := by
  unfold tailWord_2536419
  simp only [CollatzResearch.WordTrace]
  refine ⟨92510800997994623722620311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61673867331996415815080207 92510800997994623722620311)
  ·
    refine ⟨138766201496991935583930467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92510800997994623722620311 138766201496991935583930467)
    ·
      refine ⟨208149302245487903375895701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138766201496991935583930467 208149302245487903375895701)
      ·
        refine ⟨9756998542757245470745111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 208149302245487903375895701 9756998542757245470745111)
        ·
          refine ⟨14635497814135868206117667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9756998542757245470745111 14635497814135868206117667)
          ·
            refine ⟨21953246721203802309176501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14635497814135868206117667 21953246721203802309176501)
            ·
              refine ⟨2058116880112856466485297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21953246721203802309176501 2058116880112856466485297)
              ·
                refine ⟨1543587660084642349863973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058116880112856466485297 1543587660084642349863973)
                ·
                  refine ⟨289422686265870440599495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543587660084642349863973 289422686265870440599495)
                  ·
                    rfl

theorem cell22_2536419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 4].length) (baseStart_2536419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536419 prefixEnd_2536419 := by exact prefixLift 2536419
  have htrace : WordTrace (prefixWord ++ tailWord_2536419) baseStart_2536419 baseEnd_2536419 := by
    simpa [prefixWord, tailWord_2536419, baseEnd_2536419] using wordTrace_append hprefix tailTrace_2536419
  have hstable : (prefixWord ++ tailWord_2536419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536419).length < 2 ^ (prefixWord ++ tailWord_2536419).sum := by decide
  have hdescent : baseEnd_2536419 < baseStart_2536419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536513 : List Nat := [1, 2, 5, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2536513 : Nat := 118140960795 + 2536513 * 2 ^ 59
def prefixEnd_2536513 : Nat := 4983230072969 + 3 ^ 40 * 2536513 * 2
def baseEnd_2536513 : Nat := 868300236918626409948197

theorem tailTrace_2536513 : CollatzResearch.WordTrace tailWord_2536513 prefixEnd_2536513 868300236918626409948197 := by
  unfold tailWord_2536513
  simp only [CollatzResearch.WordTrace]
  refine ⟨92514229459654077776542193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61676152973102718517694795 92514229459654077776542193)
  ·
    refine ⟨69385672094740558332406645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92514229459654077776542193 69385672094740558332406645)
    ·
      refine ⟨6504906758881927343663123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69385672094740558332406645 6504906758881927343663123)
      ·
        refine ⟨9757360138322891015494685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6504906758881927343663123 9757360138322891015494685)
        ·
          refine ⟨3659010051871084130810507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9757360138322891015494685 3659010051871084130810507)
          ·
            refine ⟨5488515077806626196215761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659010051871084130810507 5488515077806626196215761)
            ·
              refine ⟨4116386308354969647161821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5488515077806626196215761 4116386308354969647161821)
              ·
                refine ⟨1543644865633113617685683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4116386308354969647161821 1543644865633113617685683)
                ·
                  refine ⟨2315467298449670426528525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543644865633113617685683 2315467298449670426528525)
                  ·
                    refine ⟨868300236918626409948197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315467298449670426528525 868300236918626409948197)
                    ·
                      rfl

theorem cell22_2536513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2536513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536513 prefixEnd_2536513 := by exact prefixLift 2536513
  have htrace : WordTrace (prefixWord ++ tailWord_2536513) baseStart_2536513 baseEnd_2536513 := by
    simpa [prefixWord, tailWord_2536513, baseEnd_2536513] using wordTrace_append hprefix tailTrace_2536513
  have hstable : (prefixWord ++ tailWord_2536513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536513).length < 2 ^ (prefixWord ++ tailWord_2536513).sum := by decide
  have hdescent : baseEnd_2536513 < baseStart_2536513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536520 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 8]
def baseStart_2536520 : Nat := 118140960795 + 2536520 * 2 ^ 59
def prefixEnd_2536520 : Nat := 4983230072969 + 3 ^ 40 * 2536520 * 2
def baseEnd_2536520 : Nat := 289434211053893575007725

theorem tailTrace_2536520 : CollatzResearch.WordTrace tailWord_2536520 prefixEnd_2536520 289434211053893575007725 := by
  unfold tailWord_2536520
  simp only [CollatzResearch.WordTrace]
  refine ⟨46257242385314358986023507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61676323180419145314698009 46257242385314358986023507)
  ·
    refine ⟨69385863577971538479035261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46257242385314358986023507 69385863577971538479035261)
    ·
      refine ⟨26019698841739326929638223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69385863577971538479035261 26019698841739326929638223)
      ·
        refine ⟨39029548262608990394457335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26019698841739326929638223 39029548262608990394457335)
        ·
          refine ⟨58544322393913485591686003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39029548262608990394457335 58544322393913485591686003)
          ·
            refine ⟨87816483590870228387529005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58544322393913485591686003 87816483590870228387529005)
            ·
              refine ⟨32931181346576335645323377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87816483590870228387529005 32931181346576335645323377)
              ·
                refine ⟨24698386009932251733992533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32931181346576335645323377 24698386009932251733992533)
                ·
                  refine ⟨289434211053893575007725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24698386009932251733992533 289434211053893575007725)
                  ·
                    rfl

theorem cell22_2536520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_2536520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536520 prefixEnd_2536520 := by exact prefixLift 2536520
  have htrace : WordTrace (prefixWord ++ tailWord_2536520) baseStart_2536520 baseEnd_2536520 := by
    simpa [prefixWord, tailWord_2536520, baseEnd_2536520] using wordTrace_append hprefix tailTrace_2536520
  have hstable : (prefixWord ++ tailWord_2536520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536520).length < 2 ^ (prefixWord ++ tailWord_2536520).sum := by decide
  have hdescent : baseEnd_2536520 < baseStart_2536520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536567 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 2, 4]
def baseStart_2536567 : Nat := 118140960795 + 2536567 * 2 ^ 59
def prefixEnd_2536567 : Nat := 4983230072969 + 3 ^ 40 * 2536567 * 2
def baseEnd_2536567 : Nat := 868318722222188269098031

theorem tailTrace_2536567 : CollatzResearch.WordTrace tailWord_2536567 prefixEnd_2536567 868318722222188269098031 := by
  unfold tailWord_2536567
  simp only [CollatzResearch.WordTrace]
  refine ⟨92516199001458444999007955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61677466000972296666005303 92516199001458444999007955)
  ·
    refine ⟨138774298502187667498511933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92516199001458444999007955 138774298502187667498511933)
    ·
      refine ⟨52040361938320375311941975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138774298502187667498511933 52040361938320375311941975)
      ·
        refine ⟨78060542907480562967912963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52040361938320375311941975 78060542907480562967912963)
        ·
          refine ⟨117090814361220844451869445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78060542907480562967912963 117090814361220844451869445)
          ·
            refine ⟨21954527692728908334725521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117090814361220844451869445 21954527692728908334725521)
            ·
              refine ⟨16465895769546681251044141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21954527692728908334725521 16465895769546681251044141)
              ·
                refine ⟨6174710913580005469141553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16465895769546681251044141 6174710913580005469141553)
                ·
                  refine ⟨4631033185185004101856165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6174710913580005469141553 4631033185185004101856165)
                  ·
                    refine ⟨868318722222188269098031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4631033185185004101856165 868318722222188269098031)
                    ·
                      rfl

theorem cell22_2536567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_2536567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536567 prefixEnd_2536567 := by exact prefixLift 2536567
  have htrace : WordTrace (prefixWord ++ tailWord_2536567) baseStart_2536567 baseEnd_2536567 := by
    simpa [prefixWord, tailWord_2536567, baseEnd_2536567] using wordTrace_append hprefix tailTrace_2536567
  have hstable : (prefixWord ++ tailWord_2536567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536567).length < 2 ^ (prefixWord ++ tailWord_2536567).sum := by decide
  have hdescent : baseEnd_2536567 < baseStart_2536567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536631 : List Nat := [1, 1, 3, 1, 4, 1, 2, 5, 1, 3]
def baseStart_2536631 : Nat := 118140960795 + 2536631 * 2 ^ 59
def prefixEnd_2536631 : Nat := 4983230072969 + 3 ^ 40 * 2536631 * 2
def baseEnd_2536631 : Nat := 868340630730113435497835

theorem tailTrace_2536631 : CollatzResearch.WordTrace tailWord_2536631 prefixEnd_2536631 868340630730113435497835 := by
  unfold tailWord_2536631
  simp only [CollatzResearch.WordTrace]
  refine ⟨92518533273226583929337747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61679022182151055952891831 92518533273226583929337747)
  ·
    refine ⟨138777799909839875894006621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92518533273226583929337747 138777799909839875894006621)
    ·
      refine ⟨52041674966189953460252483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138777799909839875894006621 52041674966189953460252483)
      ·
        refine ⟨78062512449284930190378725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52041674966189953460252483 78062512449284930190378725)
        ·
          refine ⟨14636721084240924410696011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78062512449284930190378725 14636721084240924410696011)
          ·
            refine ⟨21955081626361386616044017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14636721084240924410696011 21955081626361386616044017)
            ·
              refine ⟨16466311219771039962033013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21955081626361386616044017 16466311219771039962033013)
              ·
                refine ⟨1543716676853534996440595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16466311219771039962033013 1543716676853534996440595)
                ·
                  refine ⟨2315575015280302494660893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543716676853534996440595 2315575015280302494660893)
                  ·
                    refine ⟨868340630730113435497835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315575015280302494660893 868340630730113435497835)
                    ·
                      rfl

theorem cell22_2536631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_2536631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536631 prefixEnd_2536631 := by exact prefixLift 2536631
  have htrace : WordTrace (prefixWord ++ tailWord_2536631) baseStart_2536631 baseEnd_2536631 := by
    simpa [prefixWord, tailWord_2536631, baseEnd_2536631] using wordTrace_append hprefix tailTrace_2536631
  have hstable : (prefixWord ++ tailWord_2536631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536631).length < 2 ^ (prefixWord ++ tailWord_2536631).sum := by decide
  have hdescent : baseEnd_2536631 < baseStart_2536631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536648 : List Nat := [2, 1, 3, 1, 2, 1, 6, 2, 1, 3]
def baseStart_2536648 : Nat := 118140960795 + 2536648 * 2 ^ 59
def prefixEnd_2536648 : Nat := 4983230072969 + 3 ^ 40 * 2536648 * 2
def baseEnd_2536648 : Nat := 868346450177531057822783

theorem tailTrace_2536648 : CollatzResearch.WordTrace tailWord_2536648 prefixEnd_2536648 868346450177531057822783 := by
  unfold tailWord_2536648
  simp only [CollatzResearch.WordTrace]
  refine ⟨46259576657082497916353299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61679435542776663888471065 46259576657082497916353299)
  ·
    refine ⟨69389364985623746874529949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46259576657082497916353299 69389364985623746874529949)
    ·
      refine ⟨26021011869608905077948731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69389364985623746874529949 26021011869608905077948731)
      ·
        refine ⟨39031517804413357616923097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26021011869608905077948731 39031517804413357616923097)
        ·
          refine ⟨29273638353310018212692323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39031517804413357616923097 29273638353310018212692323)
          ·
            refine ⟨43910457529965027319038485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29273638353310018212692323 43910457529965027319038485)
            ·
              refine ⟨2058302696717110655579929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43910457529965027319038485 2058302696717110655579929)
              ·
                refine ⟨1543727022537832991684947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058302696717110655579929 1543727022537832991684947)
                ·
                  refine ⟨2315590533806749487527421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543727022537832991684947 2315590533806749487527421)
                  ·
                    refine ⟨868346450177531057822783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315590533806749487527421 868346450177531057822783)
                    ·
                      rfl

theorem cell22_2536648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_2536648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536648 prefixEnd_2536648 := by exact prefixLift 2536648
  have htrace : WordTrace (prefixWord ++ tailWord_2536648) baseStart_2536648 baseEnd_2536648 := by
    simpa [prefixWord, tailWord_2536648, baseEnd_2536648] using wordTrace_append hprefix tailTrace_2536648
  have hstable : (prefixWord ++ tailWord_2536648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536648).length < 2 ^ (prefixWord ++ tailWord_2536648).sum := by decide
  have hdescent : baseEnd_2536648 < baseStart_2536648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536672 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 8]
def baseStart_2536672 : Nat := 118140960795 + 2536672 * 2 ^ 59
def prefixEnd_2536672 : Nat := 4983230072969 + 3 ^ 40 * 2536672 * 2
def baseEnd_2536672 : Nat := 289451555289334331740903

theorem tailTrace_2536672 : CollatzResearch.WordTrace tailWord_2536672 prefixEnd_2536672 289451555289334331740903 := by
  unfold tailWord_2536672
  simp only [CollatzResearch.WordTrace]
  refine ⟨46260014333039023965790135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61680019110718698621053513 46260014333039023965790135)
  ·
    refine ⟨69390021499558535948685203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46260014333039023965790135 69390021499558535948685203)
    ·
      refine ⟨104085032249337803923027805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69390021499558535948685203 104085032249337803923027805)
      ·
        refine ⟨39031887093501676471135427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104085032249337803923027805 39031887093501676471135427)
        ·
          refine ⟨58547830640252514706703141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39031887093501676471135427 58547830640252514706703141)
          ·
            refine ⟨10977718245047346507506839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58547830640252514706703141 10977718245047346507506839)
            ·
              refine ⟨16466577367571019761260259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10977718245047346507506839 16466577367571019761260259)
              ·
                refine ⟨24699866051356529641890389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16466577367571019761260259 24699866051356529641890389)
                ·
                  refine ⟨289451555289334331740903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24699866051356529641890389 289451555289334331740903)
                  ·
                    rfl

theorem cell22_2536672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_2536672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536672 prefixEnd_2536672 := by exact prefixLift 2536672
  have htrace : WordTrace (prefixWord ++ tailWord_2536672) baseStart_2536672 baseEnd_2536672 := by
    simpa [prefixWord, tailWord_2536672, baseEnd_2536672] using wordTrace_append hprefix tailTrace_2536672
  have hstable : (prefixWord ++ tailWord_2536672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536672).length < 2 ^ (prefixWord ++ tailWord_2536672).sum := by decide
  have hdescent : baseEnd_2536672 < baseStart_2536672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536691 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 1, 4]
def baseStart_2536691 : Nat := 118140960795 + 2536691 * 2 ^ 59
def prefixEnd_2536691 : Nat := 4983230072969 + 3 ^ 40 * 2536691 * 2
def baseEnd_2536691 : Nat := 868361169956293278997651

theorem tailTrace_2536691 : CollatzResearch.WordTrace tailWord_2536691 prefixEnd_2536691 868361169956293278997651 := by
  unfold tailWord_2536691
  simp only [CollatzResearch.WordTrace]
  refine ⟨92520721653009214176521927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61680481102006142784347951 92520721653009214176521927)
  ·
    refine ⟨138781082479513821264782891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92520721653009214176521927 138781082479513821264782891)
    ·
      refine ⟨208171623719270731897174337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138781082479513821264782891 208171623719270731897174337)
      ·
        refine ⟨156128717789453048922880753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208171623719270731897174337 156128717789453048922880753)
        ·
          refine ⟨117096538342089786692160565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156128717789453048922880753 117096538342089786692160565)
          ·
            refine ⟨10977800469570917502390053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117096538342089786692160565 10977800469570917502390053)
            ·
              refine ⟨2058337588044547031698135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10977800469570917502390053 2058337588044547031698135)
              ·
                refine ⟨3087506382066820547547203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058337588044547031698135 3087506382066820547547203)
                ·
                  refine ⟨4631259573100230821320805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087506382066820547547203 4631259573100230821320805)
                  ·
                    refine ⟨868361169956293278997651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4631259573100230821320805 868361169956293278997651)
                    ·
                      rfl

theorem cell22_2536691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 4].length) (baseStart_2536691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536691 prefixEnd_2536691 := by exact prefixLift 2536691
  have htrace : WordTrace (prefixWord ++ tailWord_2536691) baseStart_2536691 baseEnd_2536691 := by
    simpa [prefixWord, tailWord_2536691, baseEnd_2536691] using wordTrace_append hprefix tailTrace_2536691
  have hstable : (prefixWord ++ tailWord_2536691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536691).length < 2 ^ (prefixWord ++ tailWord_2536691).sum := by decide
  have hdescent : baseEnd_2536691 < baseStart_2536691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536747 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 6, 6]
def baseStart_2536747 : Nat := 118140960795 + 2536747 * 2 ^ 59
def prefixEnd_2536747 : Nat := 4983230072969 + 3 ^ 40 * 2536747 * 2
def baseEnd_2536747 : Nat := 868380339900727799597479

theorem tailTrace_2536747 : CollatzResearch.WordTrace tailWord_2536747 prefixEnd_2536747 868380339900727799597479 := by
  unfold tailWord_2536747
  simp only [CollatzResearch.WordTrace]
  refine ⟨92522764140806335740560495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61681842760537557160373663 92522764140806335740560495)
  ·
    refine ⟨138784146211209503610840743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92522764140806335740560495 138784146211209503610840743)
    ·
      refine ⟨208176219316814255416261115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138784146211209503610840743 208176219316814255416261115)
      ·
        refine ⟨312264328975221383124391673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208176219316814255416261115 312264328975221383124391673)
        ·
          refine ⟨234198246731416037343293755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312264328975221383124391673 234198246731416037343293755)
          ·
            refine ⟨351297370097124056014940633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234198246731416037343293755 351297370097124056014940633)
            ·
              refine ⟨263473027572843042011205475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351297370097124056014940633 263473027572843042011205475)
              ·
                refine ⟨395209541359264563016808213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263473027572843042011205475 395209541359264563016808213)
                ·
                  refine ⟨18525447251215526391412885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 395209541359264563016808213 18525447251215526391412885)
                  ·
                    refine ⟨868380339900727799597479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18525447251215526391412885 868380339900727799597479)
                    ·
                      rfl

theorem cell22_2536747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_2536747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536747 prefixEnd_2536747 := by exact prefixLift 2536747
  have htrace : WordTrace (prefixWord ++ tailWord_2536747) baseStart_2536747 baseEnd_2536747 := by
    simpa [prefixWord, tailWord_2536747, baseEnd_2536747] using wordTrace_append hprefix tailTrace_2536747
  have hstable : (prefixWord ++ tailWord_2536747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536747).length < 2 ^ (prefixWord ++ tailWord_2536747).sum := by decide
  have hdescent : baseEnd_2536747 < baseStart_2536747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536772 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2536772 : Nat := 118140960795 + 2536772 * 2 ^ 59
def prefixEnd_2536772 : Nat := 4983230072969 + 3 ^ 40 * 2536772 * 2
def baseEnd_2536772 : Nat := 868388897911636067722403

theorem tailTrace_2536772 : CollatzResearch.WordTrace tailWord_2536772 prefixEnd_2536772 868388897911636067722403 := by
  unfold tailWord_2536772
  simp only [CollatzResearch.WordTrace]
  refine ⟨46261837982857882505110285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61682450643810510006813713 46261837982857882505110285)
  ·
    refine ⟨17348189243571705939416357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46261837982857882505110285 17348189243571705939416357)
    ·
      refine ⟨3252785483169694863640567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17348189243571705939416357 3252785483169694863640567)
      ·
        refine ⟨4879178224754542295460851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252785483169694863640567 4879178224754542295460851)
        ·
          refine ⟨7318767337131813443191277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4879178224754542295460851 7318767337131813443191277)
          ·
            refine ⟨2744537751424430041196729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7318767337131813443191277 2744537751424430041196729)
            ·
              refine ⟨2058403313568322530897547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2744537751424430041196729 2058403313568322530897547)
              ·
                refine ⟨3087604970352483796346321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058403313568322530897547 3087604970352483796346321)
                ·
                  refine ⟨2315703727764362847259741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3087604970352483796346321 2315703727764362847259741)
                  ·
                    refine ⟨868388897911636067722403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315703727764362847259741 868388897911636067722403)
                    ·
                      rfl

theorem cell22_2536772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2536772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536772 prefixEnd_2536772 := by exact prefixLift 2536772
  have htrace : WordTrace (prefixWord ++ tailWord_2536772) baseStart_2536772 baseEnd_2536772 := by
    simpa [prefixWord, tailWord_2536772, baseEnd_2536772] using wordTrace_append hprefix tailTrace_2536772
  have hstable : (prefixWord ++ tailWord_2536772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536772).length < 2 ^ (prefixWord ++ tailWord_2536772).sum := by decide
  have hdescent : baseEnd_2536772 < baseStart_2536772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536841 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 6]
def baseStart_2536841 : Nat := 118140960795 + 2536841 * 2 ^ 59
def prefixEnd_2536841 : Nat := 4983230072969 + 3 ^ 40 * 2536841 * 2
def baseEnd_2536841 : Nat := 289470839340580962582397

theorem tailTrace_2536841 : CollatzResearch.WordTrace tailWord_2536841 prefixEnd_2536841 289470839340580962582397 := by
  unfold tailWord_2536841
  simp only [CollatzResearch.WordTrace]
  refine ⟨92526192602465789794482377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61684128401643859862988251 92526192602465789794482377)
  ·
    refine ⟨69394644451849342345861783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92526192602465789794482377 69394644451849342345861783)
    ·
      refine ⟨104091966677774013518792675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69394644451849342345861783 104091966677774013518792675)
      ·
        refine ⟨156137950016661020278189013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104091966677774013518792675 156137950016661020278189013)
        ·
          refine ⟨3659483203515492662770055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 156137950016661020278189013 3659483203515492662770055)
          ·
            refine ⟨5489224805273238994155083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659483203515492662770055 5489224805273238994155083)
            ·
              refine ⟨8233837207909858491232625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5489224805273238994155083 8233837207909858491232625)
              ·
                refine ⟨6175377905932393868424469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8233837207909858491232625 6175377905932393868424469)
                ·
                  refine ⟨289470839340580962582397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6175377905932393868424469 289470839340580962582397)
                  ·
                    rfl

theorem cell22_2536841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_2536841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536841 prefixEnd_2536841 := by exact prefixLift 2536841
  have htrace : WordTrace (prefixWord ++ tailWord_2536841) baseStart_2536841 baseEnd_2536841 := by
    simpa [prefixWord, tailWord_2536841, baseEnd_2536841] using wordTrace_append hprefix tailTrace_2536841
  have hstable : (prefixWord ++ tailWord_2536841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536841).length < 2 ^ (prefixWord ++ tailWord_2536841).sum := by decide
  have hdescent : baseEnd_2536841 < baseStart_2536841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536858 : List Nat := [3, 1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_2536858 : Nat := 118140960795 + 2536858 * 2 ^ 59
def prefixEnd_2536858 : Nat := 4983230072969 + 3 ^ 40 * 2536858 * 2
def baseEnd_2536858 : Nat := 289472779156386836690713

theorem tailTrace_2536858 : CollatzResearch.WordTrace tailWord_2536858 prefixEnd_2536858 289472779156386836690713 := by
  unfold tailWord_2536858
  simp only [CollatzResearch.WordTrace]
  refine ⟨23131703160851050424462807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61684541762269467798567485 23131703160851050424462807)
  ·
    refine ⟨34697554741276575636694211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23131703160851050424462807 34697554741276575636694211)
    ·
      refine ⟨52046332111914863455041317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34697554741276575636694211 52046332111914863455041317)
      ·
        refine ⟨9758687270984036897820247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52046332111914863455041317 9758687270984036897820247)
        ·
          refine ⟨14638030906476055346730371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9758687270984036897820247 14638030906476055346730371)
          ·
            refine ⟨21957046359714083020095557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14638030906476055346730371 21957046359714083020095557)
            ·
              refine ⟨4116946192446390566267917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21957046359714083020095557 4116946192446390566267917)
              ·
                refine ⟨1543854822167396462350469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4116946192446390566267917 1543854822167396462350469)
                ·
                  refine ⟨289472779156386836690713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543854822167396462350469 289472779156386836690713)
                  ·
                    rfl

theorem cell22_2536858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_2536858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536858 prefixEnd_2536858 := by exact prefixLift 2536858
  have htrace : WordTrace (prefixWord ++ tailWord_2536858) baseStart_2536858 baseEnd_2536858 := by
    simpa [prefixWord, tailWord_2536858, baseEnd_2536858] using wordTrace_append hprefix tailTrace_2536858
  have hstable : (prefixWord ++ tailWord_2536858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536858).length < 2 ^ (prefixWord ++ tailWord_2536858).sum := by decide
  have hdescent : baseEnd_2536858 < baseStart_2536858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536860 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 1, 4]
def baseStart_2536860 : Nat := 118140960795 + 2536860 * 2 ^ 59
def prefixEnd_2536860 : Nat := 4983230072969 + 3 ^ 40 * 2536860 * 2
def baseEnd_2536860 : Nat := 868419022110033171522133

theorem tailTrace_2536860 : CollatzResearch.WordTrace tailWord_2536860 prefixEnd_2536860 868419022110033171522133 := by
  unfold tailWord_2536860
  simp only [CollatzResearch.WordTrace]
  refine ⟨46263442794698478019712017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61684590392931304026282689 46263442794698478019712017)
  ·
    refine ⟨34697582096023858514784013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46263442794698478019712017 34697582096023858514784013)
    ·
      refine ⟨13011593286008946943044005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34697582096023858514784013 13011593286008946943044005)
      ·
        refine ⟨2439673741126677551820751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13011593286008946943044005 2439673741126677551820751)
        ·
          refine ⟨3659510611690016327731127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2439673741126677551820751 3659510611690016327731127)
          ·
            refine ⟨5489265917535024491596691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659510611690016327731127 5489265917535024491596691)
            ·
              refine ⟨8233898876302536737395037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5489265917535024491596691 8233898876302536737395037)
              ·
                refine ⟨3087712078613451276523139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8233898876302536737395037 3087712078613451276523139)
                ·
                  refine ⟨4631568117920176914784709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087712078613451276523139 4631568117920176914784709)
                  ·
                    refine ⟨868419022110033171522133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4631568117920176914784709 868419022110033171522133)
                    ·
                      rfl

theorem cell22_2536860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_2536860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536860 prefixEnd_2536860 := by exact prefixLift 2536860
  have htrace : WordTrace (prefixWord ++ tailWord_2536860) baseStart_2536860 baseEnd_2536860 := by
    simpa [prefixWord, tailWord_2536860, baseEnd_2536860] using wordTrace_append hprefix tailTrace_2536860
  have hstable : (prefixWord ++ tailWord_2536860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536860).length < 2 ^ (prefixWord ++ tailWord_2536860).sum := by decide
  have hdescent : baseEnd_2536860 < baseStart_2536860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536871 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2536871 : Nat := 118140960795 + 2536871 * 2 ^ 59
def prefixEnd_2536871 : Nat := 4983230072969 + 3 ^ 40 * 2536871 * 2
def baseEnd_2536871 : Nat := 868422787634832809497099

theorem tailTrace_2536871 : CollatzResearch.WordTrace tailWord_2536871 prefixEnd_2536871 868422787634832809497099 := by
  unfold tailWord_2536871
  simp only [CollatzResearch.WordTrace]
  refine ⟨92527286792357104918074467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61684857861571403278716311 92527286792357104918074467)
  ·
    refine ⟨138790930188535657377111701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92527286792357104918074467 138790930188535657377111701)
    ·
      refine ⟨6505824852587608939552111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138790930188535657377111701 6505824852587608939552111)
      ·
        refine ⟨9758737278881413409328167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6505824852587608939552111 9758737278881413409328167)
        ·
          refine ⟨14638105918322120113992251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9758737278881413409328167 14638105918322120113992251)
          ·
            refine ⟨21957158877483180170988377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14638105918322120113992251 21957158877483180170988377)
            ·
              refine ⟨16467869158112385128241283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21957158877483180170988377 16467869158112385128241283)
              ·
                refine ⟨24701803737168577692361925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16467869158112385128241283 24701803737168577692361925)
                ·
                  refine ⟨4631588200719108317317861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24701803737168577692361925 4631588200719108317317861)
                  ·
                    refine ⟨868422787634832809497099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4631588200719108317317861 868422787634832809497099)
                    ·
                      rfl

theorem cell22_2536871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2536871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536871 prefixEnd_2536871 := by exact prefixLift 2536871
  have htrace : WordTrace (prefixWord ++ tailWord_2536871) baseStart_2536871 baseEnd_2536871 := by
    simpa [prefixWord, tailWord_2536871, baseEnd_2536871] using wordTrace_append hprefix tailTrace_2536871
  have hstable : (prefixWord ++ tailWord_2536871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536871).length < 2 ^ (prefixWord ++ tailWord_2536871).sum := by decide
  have hdescent : baseEnd_2536871 < baseStart_2536871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536899 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 2, 6]
def baseStart_2536899 : Nat := 118140960795 + 2536899 * 2 ^ 59
def prefixEnd_2536899 : Nat := 4983230072969 + 3 ^ 40 * 2536899 * 2
def baseEnd_2536899 : Nat := 868432372607050069797013

theorem tailTrace_2536899 : CollatzResearch.WordTrace tailWord_2536899 prefixEnd_2536899 868432372607050069797013 := by
  unfold tailWord_2536899
  simp only [CollatzResearch.WordTrace]
  refine ⟨92528308036255665700093751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61685538690837110466729167 92528308036255665700093751)
  ·
    refine ⟨138792462054383498550140627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92528308036255665700093751 138792462054383498550140627)
    ·
      refine ⟨208188693081575247825210941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138792462054383498550140627 208188693081575247825210941)
      ·
        refine ⟨78070759905590717934454103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208188693081575247825210941 78070759905590717934454103)
        ·
          refine ⟨117106139858386076901681155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78070759905590717934454103 117106139858386076901681155)
          ·
            refine ⟨175659209787579115352521733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117106139858386076901681155 175659209787579115352521733)
            ·
              refine ⟨32936101835171084128597825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175659209787579115352521733 32936101835171084128597825)
              ·
                refine ⟨24702076376378313096448369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32936101835171084128597825 24702076376378313096448369)
                ·
                  refine ⟨18526557282283734822336277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24702076376378313096448369 18526557282283734822336277)
                  ·
                    refine ⟨868432372607050069797013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18526557282283734822336277 868432372607050069797013)
                    ·
                      rfl

theorem cell22_2536899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_2536899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536899 prefixEnd_2536899 := by exact prefixLift 2536899
  have htrace : WordTrace (prefixWord ++ tailWord_2536899) baseStart_2536899 baseEnd_2536899 := by
    simpa [prefixWord, tailWord_2536899, baseEnd_2536899] using wordTrace_append hprefix tailTrace_2536899
  have hstable : (prefixWord ++ tailWord_2536899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536899).length < 2 ^ (prefixWord ++ tailWord_2536899).sum := by decide
  have hdescent : baseEnd_2536899 < baseStart_2536899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536931 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 7]
def baseStart_2536931 : Nat := 118140960795 + 2536931 * 2 ^ 59
def prefixEnd_2536931 : Nat := 4983230072969 + 3 ^ 40 * 2536931 * 2
def baseEnd_2536931 : Nat := 289481108953670884332305

theorem tailTrace_2536931 : CollatzResearch.WordTrace tailWord_2536931 prefixEnd_2536931 289481108953670884332305 := by
  unfold tailWord_2536931
  simp only [CollatzResearch.WordTrace]
  refine ⟨92529475172139735165258647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61686316781426490110172431 92529475172139735165258647)
  ·
    refine ⟨138794212758209602747887971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92529475172139735165258647 138794212758209602747887971)
    ·
      refine ⟨208191319137314404121831957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138794212758209602747887971 208191319137314404121831957)
      ·
        refine ⟨9758968084561612693210873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 208191319137314404121831957 9758968084561612693210873)
        ·
          refine ⟨7319226063421209519908155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9758968084561612693210873 7319226063421209519908155)
          ·
            refine ⟨10978839095131814279862233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7319226063421209519908155 10978839095131814279862233)
            ·
              refine ⟨8234129321348860709896675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10978839095131814279862233 8234129321348860709896675)
              ·
                refine ⟨12351193982023291064845013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8234129321348860709896675 12351193982023291064845013)
                ·
                  refine ⟨289481108953670884332305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12351193982023291064845013 289481108953670884332305)
                  ·
                    rfl

theorem cell22_2536931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 7].length) (baseStart_2536931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536931 prefixEnd_2536931 := by exact prefixLift 2536931
  have htrace : WordTrace (prefixWord ++ tailWord_2536931) baseStart_2536931 baseEnd_2536931 := by
    simpa [prefixWord, tailWord_2536931, baseEnd_2536931] using wordTrace_append hprefix tailTrace_2536931
  have hstable : (prefixWord ++ tailWord_2536931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536931).length < 2 ^ (prefixWord ++ tailWord_2536931).sum := by decide
  have hdescent : baseEnd_2536931 < baseStart_2536931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536935 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 3, 3]
def baseStart_2536935 : Nat := 118140960795 + 2536935 * 2 ^ 59
def prefixEnd_2536935 : Nat := 4983230072969 + 3 ^ 40 * 2536935 * 2
def baseEnd_2536935 : Nat := 868444696142757975896903

theorem tailTrace_2536935 : CollatzResearch.WordTrace tailWord_2536935 prefixEnd_2536935 868444696142757975896903 := by
  unfold tailWord_2536935
  simp only [CollatzResearch.WordTrace]
  refine ⟨92529621064125243848404259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61686414042750162565602839 92529621064125243848404259)
  ·
    refine ⟨138794431596187865772606389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92529621064125243848404259 138794431596187865772606389)
    ·
      refine ⟨13011977962142612416181849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138794431596187865772606389 13011977962142612416181849)
      ·
        refine ⟨9758983471606959312136387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13011977962142612416181849 9758983471606959312136387)
        ·
          refine ⟨14638475207410438968204581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9758983471606959312136387 14638475207410438968204581)
          ·
            refine ⟨2744714101389457306538359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14638475207410438968204581 2744714101389457306538359)
            ·
              refine ⟨4117071152084185959807539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744714101389457306538359 4117071152084185959807539)
              ·
                refine ⟨6175606728126278939711309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4117071152084185959807539 6175606728126278939711309)
                ·
                  refine ⟨2315852523047354602391741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6175606728126278939711309 2315852523047354602391741)
                  ·
                    refine ⟨868444696142757975896903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315852523047354602391741 868444696142757975896903)
                    ·
                      rfl

theorem cell22_2536935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_2536935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2536935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2536935 prefixEnd_2536935 := by exact prefixLift 2536935
  have htrace : WordTrace (prefixWord ++ tailWord_2536935) baseStart_2536935 baseEnd_2536935 := by
    simpa [prefixWord, tailWord_2536935, baseEnd_2536935] using wordTrace_append hprefix tailTrace_2536935
  have hstable : (prefixWord ++ tailWord_2536935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536935).length < 2 ^ (prefixWord ++ tailWord_2536935).sum := by decide
  have hdescent : baseEnd_2536935 < baseStart_2536935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537023 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 2, 4]
def baseStart_2537023 : Nat := 118140960795 + 2537023 * 2 ^ 59
def prefixEnd_2537023 : Nat := 4983230072969 + 3 ^ 40 * 2537023 * 2
def baseEnd_2537023 : Nat := 868474820341155079696633

theorem tailTrace_2537023 : CollatzResearch.WordTrace tailWord_2537023 prefixEnd_2537023 868474820341155079696633 := by
  unfold tailWord_2537023
  simp only [CollatzResearch.WordTrace]
  refine ⟨92532830687806434877607723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61688553791870956585071815 92532830687806434877607723)
  ·
    refine ⟨138799246031709652316411585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92532830687806434877607723 138799246031709652316411585)
    ·
      refine ⟨104099434523782239237308689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138799246031709652316411585 104099434523782239237308689)
      ·
        refine ⟨78074575892836679427981517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104099434523782239237308689 78074575892836679427981517)
        ·
          refine ⟨29277965959813754785493069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78074575892836679427981517 29277965959813754785493069)
          ·
            refine ⟨10979237234930158044559901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29277965959813754785493069 10979237234930158044559901)
            ·
              refine ⟨4117213963098809266709963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10979237234930158044559901 4117213963098809266709963)
              ·
                refine ⟨6175820944648213900064945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4117213963098809266709963 6175820944648213900064945)
                ·
                  refine ⟨4631865708486160425048709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6175820944648213900064945 4631865708486160425048709)
                  ·
                    refine ⟨868474820341155079696633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4631865708486160425048709 868474820341155079696633)
                    ·
                      rfl

theorem cell22_2537023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_2537023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537023 prefixEnd_2537023 := by exact prefixLift 2537023
  have htrace : WordTrace (prefixWord ++ tailWord_2537023) baseStart_2537023 baseEnd_2537023 := by
    simpa [prefixWord, tailWord_2537023, baseEnd_2537023] using wordTrace_append hprefix tailTrace_2537023
  have hstable : (prefixWord ++ tailWord_2537023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537023).length < 2 ^ (prefixWord ++ tailWord_2537023).sum := by decide
  have hdescent : baseEnd_2537023 < baseStart_2537023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537042 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_2537042 : Nat := 118140960795 + 2537042 * 2 ^ 59
def prefixEnd_2537042 : Nat := 4983230072969 + 3 ^ 40 * 2537042 * 2
def baseEnd_2537042 : Nat := 868481324429445363471575

theorem tailTrace_2537042 : CollatzResearch.WordTrace tailWord_2537042 prefixEnd_2537042 868481324429445363471575 := by
  unfold tailWord_2537042
  simp only [CollatzResearch.WordTrace]
  refine ⟨23133380918684400280637345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61689015783158400748366253 23133380918684400280637345)
  ·
    refine ⟨17350035689013300210478009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23133380918684400280637345 17350035689013300210478009)
    ·
      refine ⟨13012526766759975157858507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17350035689013300210478009 13012526766759975157858507)
      ·
        refine ⟨19518790150139962736787761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13012526766759975157858507 19518790150139962736787761)
        ·
          refine ⟨14639092612604972052590821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19518790150139962736787761 14639092612604972052590821)
          ·
            refine ⟨2744829864863432259860779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14639092612604972052590821 2744829864863432259860779)
            ·
              refine ⟨4117244797295148389791169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744829864863432259860779 4117244797295148389791169)
              ·
                refine ⟨3087933597971361292343377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4117244797295148389791169 3087933597971361292343377)
                ·
                  refine ⟨2315950198478520969257533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3087933597971361292343377 2315950198478520969257533)
                  ·
                    refine ⟨868481324429445363471575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315950198478520969257533 868481324429445363471575)
                    ·
                      rfl

theorem cell22_2537042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_2537042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537042 prefixEnd_2537042 := by exact prefixLift 2537042
  have htrace : WordTrace (prefixWord ++ tailWord_2537042) baseStart_2537042 baseEnd_2537042 := by
    simpa [prefixWord, tailWord_2537042, baseEnd_2537042] using wordTrace_append hprefix tailTrace_2537042
  have hstable : (prefixWord ++ tailWord_2537042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537042).length < 2 ^ (prefixWord ++ tailWord_2537042).sum := by decide
  have hdescent : baseEnd_2537042 < baseStart_2537042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537143 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 3, 5]
def baseStart_2537143 : Nat := 118140960795 + 2537143 * 2 ^ 59
def prefixEnd_2537143 : Nat := 4983230072969 + 3 ^ 40 * 2537143 * 2
def baseEnd_2537143 : Nat := 868515898793514766696265

theorem tailTrace_2537143 : CollatzResearch.WordTrace tailWord_2537143 prefixEnd_2537143 868515898793514766696265 := by
  unfold tailWord_2537143
  simp only [CollatzResearch.WordTrace]
  refine ⟨92537207447371695371976083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61691471631581130247984055 92537207447371695371976083)
  ·
    refine ⟨138805811171057543057964125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92537207447371695371976083 138805811171057543057964125)
    ·
      refine ⟨52052179189146578646736547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138805811171057543057964125 52052179189146578646736547)
      ·
        refine ⟨78078268783719867970104821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52052179189146578646736547 78078268783719867970104821)
        ·
          refine ⟨7319837698473737622197327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78078268783719867970104821 7319837698473737622197327)
          ·
            refine ⟨10979756547710606433295991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7319837698473737622197327 10979756547710606433295991)
            ·
              refine ⟨16469634821565909649943987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10979756547710606433295991 16469634821565909649943987)
              ·
                refine ⟨24704452232348864474915981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16469634821565909649943987 24704452232348864474915981)
                ·
                  refine ⟨9264169587130824178093493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24704452232348864474915981 9264169587130824178093493)
                  ·
                    refine ⟨868515898793514766696265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9264169587130824178093493 868515898793514766696265)
                    ·
                      rfl

theorem cell22_2537143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_2537143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537143 prefixEnd_2537143 := by exact prefixLift 2537143
  have htrace : WordTrace (prefixWord ++ tailWord_2537143) baseStart_2537143 baseEnd_2537143 := by
    simpa [prefixWord, tailWord_2537143, baseEnd_2537143] using wordTrace_append hprefix tailTrace_2537143
  have hstable : (prefixWord ++ tailWord_2537143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537143).length < 2 ^ (prefixWord ++ tailWord_2537143).sum := by decide
  have hdescent : baseEnd_2537143 < baseStart_2537143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537162 : List Nat := [3, 1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_2537162 : Nat := 118140960795 + 2537162 * 2 ^ 59
def prefixEnd_2537162 : Nat := 4983230072969 + 3 ^ 40 * 2537162 * 2
def baseEnd_2537162 : Nat := 289507467627268350157069

theorem tailTrace_2537162 : CollatzResearch.WordTrace tailWord_2537162 prefixEnd_2537162 289507467627268350157069 := by
  unfold tailWord_2537162
  simp only [CollatzResearch.WordTrace]
  refine ⟨23134475108575715404229435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61691933622868574411278493 23134475108575715404229435)
  ·
    refine ⟨34701712662863573106344153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23134475108575715404229435 34701712662863573106344153)
    ·
      refine ⟨26026284497147679829758115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34701712662863573106344153 26026284497147679829758115)
      ·
        refine ⟨39039426745721519744637173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26026284497147679829758115 39039426745721519744637173)
        ·
          refine ⟨3659946257411392476059735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39039426745721519744637173 3659946257411392476059735)
          ·
            refine ⟨5489919386117088714089603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659946257411392476059735 5489919386117088714089603)
            ·
              refine ⟨8234879079175633071134405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5489919386117088714089603 8234879079175633071134405)
              ·
                refine ⟨1544039827345431200837701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8234879079175633071134405 1544039827345431200837701)
                ·
                  refine ⟨289507467627268350157069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1544039827345431200837701 289507467627268350157069)
                  ·
                    rfl

theorem cell22_2537162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_2537162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537162 prefixEnd_2537162 := by exact prefixLift 2537162
  have htrace : WordTrace (prefixWord ++ tailWord_2537162) baseStart_2537162 baseEnd_2537162 := by
    simpa [prefixWord, tailWord_2537162, baseEnd_2537162] using wordTrace_append hprefix tailTrace_2537162
  have hstable : (prefixWord ++ tailWord_2537162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537162).length < 2 ^ (prefixWord ++ tailWord_2537162).sum := by decide
  have hdescent : baseEnd_2537162 < baseStart_2537162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537192 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 2, 4]
def baseStart_2537192 : Nat := 118140960795 + 2537192 * 2 ^ 59
def prefixEnd_2537192 : Nat := 4983230072969 + 3 ^ 40 * 2537192 * 2
def baseEnd_2537192 : Nat := 868532672494894972221115

theorem tailTrace_2537192 : CollatzResearch.WordTrace tailWord_2537192 prefixEnd_2537192 868532672494894972221115 := by
  unfold tailWord_2537192
  simp only [CollatzResearch.WordTrace]
  refine ⟨46269497312097088370254915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61692663082796117827006553 46269497312097088370254915)
  ·
    refine ⟨69404245968145632555382373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46269497312097088370254915 69404245968145632555382373)
    ·
      refine ⟨13013296119027306104134195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69404245968145632555382373 13013296119027306104134195)
      ·
        refine ⟨19519944178540959156201293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13013296119027306104134195 19519944178540959156201293)
        ·
          refine ⟨7319979066952859683575485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19519944178540959156201293 7319979066952859683575485)
          ·
            refine ⟨2744992150107322381340807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7319979066952859683575485 2744992150107322381340807)
            ·
              refine ⟨4117488225160983572011211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744992150107322381340807 4117488225160983572011211)
              ·
                refine ⟨6176232337741475358016817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4117488225160983572011211 6176232337741475358016817)
                ·
                  refine ⟨4632174253306106518512613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6176232337741475358016817 4632174253306106518512613)
                  ·
                    refine ⟨868532672494894972221115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4632174253306106518512613 868532672494894972221115)
                    ·
                      rfl

theorem cell22_2537192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_2537192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537192 prefixEnd_2537192 := by exact prefixLift 2537192
  have htrace : WordTrace (prefixWord ++ tailWord_2537192) baseStart_2537192 baseEnd_2537192 := by
    simpa [prefixWord, tailWord_2537192, baseEnd_2537192] using wordTrace_append hprefix tailTrace_2537192
  have hstable : (prefixWord ++ tailWord_2537192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537192).length < 2 ^ (prefixWord ++ tailWord_2537192).sum := by decide
  have hdescent : baseEnd_2537192 < baseStart_2537192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537256 : List Nat := [2, 1, 5, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2537256 : Nat := 118140960795 + 2537256 * 2 ^ 59
def prefixEnd_2537256 : Nat := 4983230072969 + 3 ^ 40 * 2537256 * 2
def baseEnd_2537256 : Nat := 868554581002820138620919

theorem tailTrace_2537256 : CollatzResearch.WordTrace tailWord_2537256 prefixEnd_2537256 868554581002820138620919 := by
  unfold tailWord_2537256
  simp only [CollatzResearch.WordTrace]
  refine ⟨46270664447981157835419811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61694219263974877113893081 46270664447981157835419811)
  ·
    refine ⟨69405996671971736753129717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46270664447981157835419811 69405996671971736753129717)
    ·
      refine ⟨6506812187997350320605911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69405996671971736753129717 6506812187997350320605911)
      ·
        refine ⟨9760218281996025480908867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6506812187997350320605911 9760218281996025480908867)
        ·
          refine ⟨14640327422994038221363301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9760218281996025480908867 14640327422994038221363301)
          ·
            refine ⟨2745061391811382166505619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14640327422994038221363301 2745061391811382166505619)
            ·
              refine ⟨4117592087717073249758429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2745061391811382166505619 4117592087717073249758429)
              ·
                refine ⟨1544097032893902468659411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4117592087717073249758429 1544097032893902468659411)
                ·
                  refine ⟨2316145549340853702989117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544097032893902468659411 2316145549340853702989117)
                  ·
                    refine ⟨868554581002820138620919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2316145549340853702989117 868554581002820138620919)
                    ·
                      rfl

theorem cell22_2537256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2537256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537256 prefixEnd_2537256 := by exact prefixLift 2537256
  have htrace : WordTrace (prefixWord ++ tailWord_2537256) baseStart_2537256 baseEnd_2537256 := by
    simpa [prefixWord, tailWord_2537256, baseEnd_2537256] using wordTrace_append hprefix tailTrace_2537256
  have hstable : (prefixWord ++ tailWord_2537256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537256).length < 2 ^ (prefixWord ++ tailWord_2537256).sum := by decide
  have hdescent : baseEnd_2537256 < baseStart_2537256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537273 : List Nat := [1, 2, 1, 7, 1, 1, 3, 2, 1, 3]
def baseStart_2537273 : Nat := 118140960795 + 2537273 * 2 ^ 59
def prefixEnd_2537273 : Nat := 4983230072969 + 3 ^ 40 * 2537273 * 2
def baseEnd_2537273 : Nat := 868560400450237760945867

theorem tailTrace_2537273 : CollatzResearch.WordTrace tailWord_2537273 prefixEnd_2537273 868560400450237760945867 := by
  unfold tailWord_2537273
  simp only [CollatzResearch.WordTrace]
  refine ⟨92541948936900727574208473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61694632624600485049472315 92541948936900727574208473)
  ·
    refine ⟨69406461702675545680656355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92541948936900727574208473 69406461702675545680656355)
    ·
      refine ⟨104109692554013318520984533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69406461702675545680656355 104109692554013318520984533)
      ·
        refine ⟨2440070919234687152835575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 104109692554013318520984533 2440070919234687152835575)
        ·
          refine ⟨3660106378852030729253363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440070919234687152835575 3660106378852030729253363)
          ·
            refine ⟨5490159568278046093880045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3660106378852030729253363 5490159568278046093880045)
            ·
              refine ⟨2058809838104267285205017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5490159568278046093880045 2058809838104267285205017)
              ·
                refine ⟨1544107378578200463903763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058809838104267285205017 1544107378578200463903763)
                ·
                  refine ⟨2316161067867300695855645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544107378578200463903763 2316161067867300695855645)
                  ·
                    refine ⟨868560400450237760945867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2316161067867300695855645 868560400450237760945867)
                    ·
                      rfl

theorem cell22_2537273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 1, 3].length) (baseStart_2537273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537273 prefixEnd_2537273 := by exact prefixLift 2537273
  have htrace : WordTrace (prefixWord ++ tailWord_2537273) baseStart_2537273 baseEnd_2537273 := by
    simpa [prefixWord, tailWord_2537273, baseEnd_2537273] using wordTrace_append hprefix tailTrace_2537273
  have hstable : (prefixWord ++ tailWord_2537273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537273).length < 2 ^ (prefixWord ++ tailWord_2537273).sum := by decide
  have hdescent : baseEnd_2537273 < baseStart_2537273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537286 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2537286 : Nat := 118140960795 + 2537286 * 2 ^ 59
def prefixEnd_2537286 : Nat := 4983230072969 + 3 ^ 40 * 2537286 * 2
def baseEnd_2537286 : Nat := 289521616871970020123609

theorem tailTrace_2537286 : CollatzResearch.WordTrace tailWord_2537286 prefixEnd_2537286 289521616871970020123609 := by
  unfold tailWord_2537286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891950721432925962325991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61694948723902420529621141 2891950721432925962325991)
  ·
    refine ⟨4337926082149388943488987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2891950721432925962325991 4337926082149388943488987)
    ·
      refine ⟨6506889123224083415233481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337926082149388943488987 6506889123224083415233481)
      ·
        refine ⟨4880166842418062561425111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6506889123224083415233481 4880166842418062561425111)
        ·
          refine ⟨7320250263627093842137667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4880166842418062561425111 7320250263627093842137667)
          ·
            refine ⟨10980375395440640763206501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7320250263627093842137667 10980375395440640763206501)
            ·
              refine ⟨2058820386645120143101219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10980375395440640763206501 2058820386645120143101219)
              ·
                refine ⟨3088230579967680214651829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058820386645120143101219 3088230579967680214651829)
                ·
                  refine ⟨289521616871970020123609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3088230579967680214651829 289521616871970020123609)
                  ·
                    rfl

theorem cell22_2537286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2537286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537286 prefixEnd_2537286 := by exact prefixLift 2537286
  have htrace : WordTrace (prefixWord ++ tailWord_2537286) baseStart_2537286 baseEnd_2537286 := by
    simpa [prefixWord, tailWord_2537286, baseEnd_2537286] using wordTrace_append hprefix tailTrace_2537286
  have hstable : (prefixWord ++ tailWord_2537286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537286).length < 2 ^ (prefixWord ++ tailWord_2537286).sum := by decide
  have hdescent : baseEnd_2537286 < baseStart_2537286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537475 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 2, 7]
def baseStart_2537475 : Nat := 118140960795 + 2537475 * 2 ^ 59
def prefixEnd_2537475 : Nat := 4983230072969 + 3 ^ 40 * 2537475 * 2
def baseEnd_2537475 : Nat := 868629549178376567395247

theorem tailTrace_2537475 : CollatzResearch.WordTrace tailWord_2537475 prefixEnd_2537475 868629549178376567395247 := by
  unfold tailWord_2537475
  simp only [CollatzResearch.WordTrace]
  refine ⟨92549316482168916073061879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61699544321445944048707919 92549316482168916073061879)
  ·
    refine ⟨138823974723253374109592819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92549316482168916073061879 138823974723253374109592819)
    ·
      refine ⟨208235962084880061164389229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138823974723253374109592819 208235962084880061164389229)
      ·
        refine ⟨78088485781830022936645961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208235962084880061164389229 78088485781830022936645961)
        ·
          refine ⟨58566364336372517202484471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78088485781830022936645961 58566364336372517202484471)
          ·
            refine ⟨87849546504558775803726707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58566364336372517202484471 87849546504558775803726707)
            ·
              refine ⟨131774319756838163705590061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87849546504558775803726707 131774319756838163705590061)
              ·
                refine ⟨49415369908814311389596273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131774319756838163705590061 49415369908814311389596273)
                ·
                  refine ⟨37061527431610733542197205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49415369908814311389596273 37061527431610733542197205)
                  ·
                    refine ⟨868629549178376567395247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37061527431610733542197205 868629549178376567395247)
                    ·
                      rfl

theorem cell22_2537475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_2537475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537475 prefixEnd_2537475 := by exact prefixLift 2537475
  have htrace : WordTrace (prefixWord ++ tailWord_2537475) baseStart_2537475 baseEnd_2537475 := by
    simpa [prefixWord, tailWord_2537475, baseEnd_2537475] using wordTrace_append hprefix tailTrace_2537475
  have hstable : (prefixWord ++ tailWord_2537475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537475).length < 2 ^ (prefixWord ++ tailWord_2537475).sum := by decide
  have hdescent : baseEnd_2537475 < baseStart_2537475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537479 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2537479 : Nat := 118140960795 + 2537479 * 2 ^ 59
def prefixEnd_2537479 : Nat := 4983230072969 + 3 ^ 40 * 2537479 * 2
def baseEnd_2537479 : Nat := 868630918460121890295235

theorem tailTrace_2537479 : CollatzResearch.WordTrace tailWord_2537479 prefixEnd_2537479 868630918460121890295235 := by
  unfold tailWord_2537479
  simp only [CollatzResearch.WordTrace]
  refine ⟨92549462374154424756207491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61699641582769616504138327 92549462374154424756207491)
  ·
    refine ⟨138824193561231637134311237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92549462374154424756207491 138824193561231637134311237)
    ·
      refine ⟨26029536292730931962683357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138824193561231637134311237 26029536292730931962683357)
      ·
        refine ⟨9761076109774099486006259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26029536292730931962683357 9761076109774099486006259)
        ·
          refine ⟨14641614164661149229009389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761076109774099486006259 14641614164661149229009389)
          ·
            refine ⟨5490605311747930960878521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14641614164661149229009389 5490605311747930960878521)
            ·
              refine ⟨4117953983810948220658891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5490605311747930960878521 4117953983810948220658891)
              ·
                refine ⟨6176930975716422330988337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4117953983810948220658891 6176930975716422330988337)
                ·
                  refine ⟨4632698231787316748241253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6176930975716422330988337 4632698231787316748241253)
                  ·
                    refine ⟨868630918460121890295235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4632698231787316748241253 868630918460121890295235)
                    ·
                      rfl

theorem cell22_2537479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2537479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537479 prefixEnd_2537479 := by exact prefixLift 2537479
  have htrace : WordTrace (prefixWord ++ tailWord_2537479) baseStart_2537479 baseEnd_2537479 := by
    simpa [prefixWord, tailWord_2537479, baseEnd_2537479] using wordTrace_append hprefix tailTrace_2537479
  have hstable : (prefixWord ++ tailWord_2537479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537479).length < 2 ^ (prefixWord ++ tailWord_2537479).sum := by decide
  have hdescent : baseEnd_2537479 < baseStart_2537479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537511 : List Nat := [1, 1, 7, 1, 2, 2, 1, 7]
def baseStart_2537511 : Nat := 118140960795 + 2537511 * 2 ^ 59
def prefixEnd_2537511 : Nat := 4983230072969 + 3 ^ 40 * 2537511 * 2
def baseEnd_2537511 : Nat := 96515763634898274832793

theorem tailTrace_2537511 : CollatzResearch.WordTrace tailWord_2537511 prefixEnd_2537511 96515763634898274832793 := by
  unfold tailWord_2537511
  simp only [CollatzResearch.WordTrace]
  refine ⟨92550629510038494221372387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61700419673358996147581591 92550629510038494221372387)
  ·
    refine ⟨138825944265057741332058581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92550629510038494221372387 138825944265057741332058581)
    ·
      refine ⟨3253733068712290812470123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 138825944265057741332058581 3253733068712290812470123)
      ·
        refine ⟨4880599603068436218705185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3253733068712290812470123 4880599603068436218705185)
        ·
          refine ⟨3660449702301327164028889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4880599603068436218705185 3660449702301327164028889)
          ·
            refine ⟨2745337276725995373021667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3660449702301327164028889 2745337276725995373021667)
            ·
              refine ⟨4118005915088993059532501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2745337276725995373021667 4118005915088993059532501)
              ·
                refine ⟨96515763634898274832793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4118005915088993059532501 96515763634898274832793)
                ·
                  rfl

theorem cell22_2537511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 7].length) (baseStart_2537511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537511 prefixEnd_2537511 := by exact prefixLift 2537511
  have htrace : WordTrace (prefixWord ++ tailWord_2537511) baseStart_2537511 baseEnd_2537511 := by
    simpa [prefixWord, tailWord_2537511, baseEnd_2537511] using wordTrace_append hprefix tailTrace_2537511
  have hstable : (prefixWord ++ tailWord_2537511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537511).length < 2 ^ (prefixWord ++ tailWord_2537511).sum := by decide
  have hdescent : baseEnd_2537511 < baseStart_2537511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537526 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_2537526 : Nat := 118140960795 + 2537526 * 2 ^ 59
def prefixEnd_2537526 : Nat := 4983230072969 + 3 ^ 40 * 2537526 * 2
def baseEnd_2537526 : Nat := 868647007520629434370091

theorem tailTrace_2537526 : CollatzResearch.WordTrace tailWord_2537526 prefixEnd_2537526 868647007520629434370091 := by
  unfold tailWord_2537526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784448537811509486448027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61700784403322767855445621 5784448537811509486448027)
  ·
    refine ⟨8676672806717264229672041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5784448537811509486448027 8676672806717264229672041)
    ·
      refine ⟨6507504605037948172254031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8676672806717264229672041 6507504605037948172254031)
      ·
        refine ⟨9761256907556922258381047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6507504605037948172254031 9761256907556922258381047)
        ·
          refine ⟨14641885361335383387571571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761256907556922258381047 14641885361335383387571571)
          ·
            refine ⟨21962828042003075081357357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14641885361335383387571571 21962828042003075081357357)
            ·
              refine ⟨8236060515751153155509009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21962828042003075081357357 8236060515751153155509009)
              ·
                refine ⟨6177045386813364866631757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8236060515751153155509009 6177045386813364866631757)
                ·
                  refine ⟨2316392020055011824986909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6177045386813364866631757 2316392020055011824986909)
                  ·
                    refine ⟨868647007520629434370091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2316392020055011824986909 868647007520629434370091)
                    ·
                      rfl

theorem cell22_2537526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_2537526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537526 prefixEnd_2537526 := by exact prefixLift 2537526
  have htrace : WordTrace (prefixWord ++ tailWord_2537526) baseStart_2537526 baseEnd_2537526 := by
    simpa [prefixWord, tailWord_2537526, baseEnd_2537526] using wordTrace_append hprefix tailTrace_2537526
  have hstable : (prefixWord ++ tailWord_2537526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537526).length < 2 ^ (prefixWord ++ tailWord_2537526).sum := by decide
  have hdescent : baseEnd_2537526 < baseStart_2537526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537586 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_2537586 : Nat := 118140960795 + 2537586 * 2 ^ 59
def prefixEnd_2537586 : Nat := 4983230072969 + 3 ^ 40 * 2537586 * 2
def baseEnd_2537586 : Nat := 868667546746809277869907

theorem tailTrace_2537586 : CollatzResearch.WordTrace tailWord_2537586 prefixEnd_2537586 868667546746809277869907 := by
  unfold tailWord_2537586
  simp only [CollatzResearch.WordTrace]
  refine ⟨23138341246191695507588153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61702243323177854686901741 23138341246191695507588153)
  ·
    refine ⟨17353755934643771630691115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23138341246191695507588153 17353755934643771630691115)
    ·
      refine ⟨26030633901965657446036673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17353755934643771630691115 26030633901965657446036673)
      ·
        refine ⟨19522975426474243084527505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26030633901965657446036673 19522975426474243084527505)
        ·
          refine ⟨14642231569855682313395629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19522975426474243084527505 14642231569855682313395629)
          ·
            refine ⟨5490836838695880867523361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14642231569855682313395629 5490836838695880867523361)
            ·
              refine ⟨4118127629021910650642521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5490836838695880867523361 4118127629021910650642521)
              ·
                refine ⟨3088595721766432987981891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4118127629021910650642521 3088595721766432987981891)
                ·
                  refine ⟨4632893582649649481972837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088595721766432987981891 4632893582649649481972837)
                  ·
                    refine ⟨868667546746809277869907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4632893582649649481972837 868667546746809277869907)
                    ·
                      rfl

theorem cell22_2537586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_2537586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537586 prefixEnd_2537586 := by exact prefixLift 2537586
  have htrace : WordTrace (prefixWord ++ tailWord_2537586) baseStart_2537586 baseEnd_2537586 := by
    simpa [prefixWord, tailWord_2537586, baseEnd_2537586] using wordTrace_append hprefix tailTrace_2537586
  have hstable : (prefixWord ++ tailWord_2537586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537586).length < 2 ^ (prefixWord ++ tailWord_2537586).sum := by decide
  have hdescent : baseEnd_2537586 < baseStart_2537586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537618 : List Nat := [3, 2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_2537618 : Nat := 118140960795 + 2537618 * 2 ^ 59
def prefixEnd_2537618 : Nat := 4983230072969 + 3 ^ 40 * 2537618 * 2
def baseEnd_2537618 : Nat := 289559500333590620356603

theorem tailTrace_2537618 : CollatzResearch.WordTrace tailWord_2537618 prefixEnd_2537618 289559500333590620356603 := by
  unfold tailWord_2537618
  simp only [CollatzResearch.WordTrace]
  refine ⟨23138633030162712873879377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61703021413767234330345005 23138633030162712873879377)
  ·
    refine ⟨17353974772622034655409533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23138633030162712873879377 17353974772622034655409533)
    ·
      refine ⟨6507740539733262995778575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17353974772622034655409533 6507740539733262995778575)
      ·
        refine ⟨9761610809599894493667863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6507740539733262995778575 9761610809599894493667863)
        ·
          refine ⟨14642416214399841740501795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761610809599894493667863 14642416214399841740501795)
          ·
            refine ⟨21963624321599762610752693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14642416214399841740501795 21963624321599762610752693)
            ·
              refine ⟨2059089780149977744758065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21963624321599762610752693 2059089780149977744758065)
              ·
                refine ⟨1544317335112483308568549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2059089780149977744758065 1544317335112483308568549)
                ·
                  refine ⟨289559500333590620356603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1544317335112483308568549 289559500333590620356603)
                  ·
                    rfl

theorem cell22_2537618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_2537618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537618 prefixEnd_2537618 := by exact prefixLift 2537618
  have htrace : WordTrace (prefixWord ++ tailWord_2537618) baseStart_2537618 baseEnd_2537618 := by
    simpa [prefixWord, tailWord_2537618, baseEnd_2537618] using wordTrace_append hprefix tailTrace_2537618
  have hstable : (prefixWord ++ tailWord_2537618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537618).length < 2 ^ (prefixWord ++ tailWord_2537618).sum := by decide
  have hdescent : baseEnd_2537618 < baseStart_2537618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537629 : List Nat := [1, 4, 2, 1, 1, 4, 2, 7]
def baseStart_2537629 : Nat := 118140960795 + 2537629 * 2 ^ 59
def prefixEnd_2537629 : Nat := 4983230072969 + 3 ^ 40 * 2537629 * 2
def baseEnd_2537629 : Nat := 96520251836174611004975

theorem tailTrace_2537629 : CollatzResearch.WordTrace tailWord_2537629 prefixEnd_2537629 96520251836174611004975 := by
  unfold tailWord_2537629
  simp only [CollatzResearch.WordTrace]
  refine ⟨92554933323611000374167941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61703288882407333582778627 92554933323611000374167941)
  ·
    refine ⟨17354049998177062570156489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92554933323611000374167941 17354049998177062570156489)
    ·
      refine ⟨13015537498632796927617367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17354049998177062570156489 13015537498632796927617367)
      ·
        refine ⟨19523306247949195391426051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13015537498632796927617367 19523306247949195391426051)
        ·
          refine ⟨29284959371923793087139077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19523306247949195391426051 29284959371923793087139077)
          ·
            refine ⟨5490929882235711203838577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29284959371923793087139077 5490929882235711203838577)
            ·
              refine ⟨4118197411676783402878933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5490929882235711203838577 4118197411676783402878933)
              ·
                refine ⟨96520251836174611004975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4118197411676783402878933 96520251836174611004975)
                ·
                  rfl

theorem cell22_2537629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 7].length) (baseStart_2537629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537629 prefixEnd_2537629 := by exact prefixLift 2537629
  have htrace : WordTrace (prefixWord ++ tailWord_2537629) baseStart_2537629 baseEnd_2537629 := by
    simpa [prefixWord, tailWord_2537629, baseEnd_2537629] using wordTrace_append hprefix tailTrace_2537629
  have hstable : (prefixWord ++ tailWord_2537629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537629).length < 2 ^ (prefixWord ++ tailWord_2537629).sum := by decide
  have hdescent : baseEnd_2537629 < baseStart_2537629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537633 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 2, 3]
def baseStart_2537633 : Nat := 118140960795 + 2537633 * 2 ^ 59
def prefixEnd_2537633 : Nat := 4983230072969 + 3 ^ 40 * 2537633 * 2
def baseEnd_2537633 : Nat := 868683635807316821944763

theorem tailTrace_2537633 : CollatzResearch.WordTrace tailWord_2537633 prefixEnd_2537633 868683635807316821944763 := by
  unfold tailWord_2537633
  simp only [CollatzResearch.WordTrace]
  refine ⟨92555079215596509057313553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61703386143731006038209035 92555079215596509057313553)
  ·
    refine ⟨69416309411697381792985165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92555079215596509057313553 69416309411697381792985165)
    ·
      refine ⟨26031116029386518172369437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69416309411697381792985165 26031116029386518172369437)
      ·
        refine ⟨9761668511019944314638539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26031116029386518172369437 9761668511019944314638539)
        ·
          refine ⟨14642502766529916471957809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761668511019944314638539 14642502766529916471957809)
          ·
            refine ⟨10981877074897437353968357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14642502766529916471957809 10981877074897437353968357)
            ·
              refine ⟨2059101951543269503869067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10981877074897437353968357 2059101951543269503869067)
              ·
                refine ⟨3088652927314904255803601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059101951543269503869067 3088652927314904255803601)
                ·
                  refine ⟨2316489695486178191852701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3088652927314904255803601 2316489695486178191852701)
                  ·
                    refine ⟨868683635807316821944763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2316489695486178191852701 868683635807316821944763)
                    ·
                      rfl

theorem cell22_2537633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_2537633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537633 prefixEnd_2537633 := by exact prefixLift 2537633
  have htrace : WordTrace (prefixWord ++ tailWord_2537633) baseStart_2537633 baseEnd_2537633 := by
    simpa [prefixWord, tailWord_2537633, baseEnd_2537633] using wordTrace_append hprefix tailTrace_2537633
  have hstable : (prefixWord ++ tailWord_2537633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537633).length < 2 ^ (prefixWord ++ tailWord_2537633).sum := by decide
  have hdescent : baseEnd_2537633 < baseStart_2537633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537736 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 6]
def baseStart_2537736 : Nat := 118140960795 + 2537736 * 2 ^ 59
def prefixEnd_2537736 : Nat := 4983230072969 + 3 ^ 40 * 2537736 * 2
def baseEnd_2537736 : Nat := 289572964937419628873149

theorem tailTrace_2537736 : CollatzResearch.WordTrace tailWord_2537736 prefixEnd_2537736 289572964937419628873149 := by
  unfold tailWord_2537736
  simp only [CollatzResearch.WordTrace]
  refine ⟨46279417967111678824156531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61705890622815571765542041 46279417967111678824156531)
  ·
    refine ⟨69419126950667518236234797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46279417967111678824156531 69419126950667518236234797)
    ·
      refine ⟨26032172606500319338588049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69419126950667518236234797 26032172606500319338588049)
      ·
        refine ⟨19524129454875239503941037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26032172606500319338588049 19524129454875239503941037)
        ·
          refine ⟨7321548545578214813977889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19524129454875239503941037 7321548545578214813977889)
          ·
            refine ⟨5491161409183661110483417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7321548545578214813977889 5491161409183661110483417)
            ·
              refine ⟨4118371056887745832862563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5491161409183661110483417 4118371056887745832862563)
              ·
                refine ⟨6177556585331618749293845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4118371056887745832862563 6177556585331618749293845)
                ·
                  refine ⟨289572964937419628873149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6177556585331618749293845 289572964937419628873149)
                  ·
                    rfl

theorem cell22_2537736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_2537736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537736 prefixEnd_2537736 := by exact prefixLift 2537736
  have htrace : WordTrace (prefixWord ++ tailWord_2537736) baseStart_2537736 baseEnd_2537736 := by
    simpa [prefixWord, tailWord_2537736, baseEnd_2537736] using wordTrace_append hprefix tailTrace_2537736
  have hstable : (prefixWord ++ tailWord_2537736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537736).length < 2 ^ (prefixWord ++ tailWord_2537736).sum := by decide
  have hdescent : baseEnd_2537736 < baseStart_2537736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537749 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2537749 : Nat := 118140960795 + 2537749 * 2 ^ 59
def prefixEnd_2537749 : Nat := 4983230072969 + 3 ^ 40 * 2537749 * 2
def baseEnd_2537749 : Nat := 868723344977931186044407

theorem tailTrace_2537749 : CollatzResearch.WordTrace tailWord_2537749 prefixEnd_2537749 868723344977931186044407 := by
  unfold tailWord_2537749
  simp only [CollatzResearch.WordTrace]
  refine ⟨92559310083176260868536301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61706206722117507245690867 92559310083176260868536301)
  ·
    refine ⟨34709741281191097825701113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92559310083176260868536301 34709741281191097825701113)
    ·
      refine ⟨26032305960893323369275835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34709741281191097825701113 26032305960893323369275835)
      ·
        refine ⟨39048458941339985053913753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26032305960893323369275835 39048458941339985053913753)
        ·
          refine ⟨29286344206004988790435315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39048458941339985053913753 29286344206004988790435315)
          ·
            refine ⟨43929516309007483185652973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29286344206004988790435315 43929516309007483185652973)
            ·
              refine ⟨16473568615877806194619865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43929516309007483185652973 16473568615877806194619865)
              ·
                refine ⟨12355176461908354645964899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16473568615877806194619865 12355176461908354645964899)
                ·
                  refine ⟨18532764692862531968947349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12355176461908354645964899 18532764692862531968947349)
                  ·
                    refine ⟨868723344977931186044407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18532764692862531968947349 868723344977931186044407)
                    ·
                      rfl

theorem cell22_2537749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2537749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537749 prefixEnd_2537749 := by exact prefixLift 2537749
  have htrace : WordTrace (prefixWord ++ tailWord_2537749) baseStart_2537749 baseEnd_2537749 := by
    simpa [prefixWord, tailWord_2537749, baseEnd_2537749] using wordTrace_append hprefix tailTrace_2537749
  have hstable : (prefixWord ++ tailWord_2537749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537749).length < 2 ^ (prefixWord ++ tailWord_2537749).sum := by decide
  have hdescent : baseEnd_2537749 < baseStart_2537749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537751 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 1, 5]
def baseStart_2537751 : Nat := 118140960795 + 2537751 * 2 ^ 59
def prefixEnd_2537751 : Nat := 4983230072969 + 3 ^ 40 * 2537751 * 2
def baseEnd_2537751 : Nat := 868724029618803847494401

theorem tailTrace_2537751 : CollatzResearch.WordTrace tailWord_2537751 prefixEnd_2537751 868724029618803847494401 := by
  unfold tailWord_2537751
  simp only [CollatzResearch.WordTrace]
  refine ⟨92559383029169015210109107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61706255352779343473406071 92559383029169015210109107)
  ·
    refine ⟨138839074543753522815163661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92559383029169015210109107 138839074543753522815163661)
    ·
      refine ⟨52064652953907571055686373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138839074543753522815163661 52064652953907571055686373)
      ·
        refine ⟨9762122428857669572941195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52064652953907571055686373 9762122428857669572941195)
        ·
          refine ⟨14643183643286504359411793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9762122428857669572941195 14643183643286504359411793)
          ·
            refine ⟨10982387732464878269558845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14643183643286504359411793 10982387732464878269558845)
            ·
              refine ⟨4118395399674329351084567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10982387732464878269558845 4118395399674329351084567)
              ·
                refine ⟨6177593099511494026626851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4118395399674329351084567 6177593099511494026626851)
                ·
                  refine ⟨9266389649267241039940277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6177593099511494026626851 9266389649267241039940277)
                  ·
                    refine ⟨868724029618803847494401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9266389649267241039940277 868724029618803847494401)
                    ·
                      rfl

theorem cell22_2537751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_2537751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537751 prefixEnd_2537751 := by exact prefixLift 2537751
  have htrace : WordTrace (prefixWord ++ tailWord_2537751) baseStart_2537751 baseEnd_2537751 := by
    simpa [prefixWord, tailWord_2537751, baseEnd_2537751] using wordTrace_append hprefix tailTrace_2537751
  have hstable : (prefixWord ++ tailWord_2537751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537751).length < 2 ^ (prefixWord ++ tailWord_2537751).sum := by decide
  have hdescent : baseEnd_2537751 < baseStart_2537751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537888 : List Nat := [2, 1, 1, 4, 1, 3, 1, 5, 4]
def baseStart_2537888 : Nat := 118140960795 + 2537888 * 2 ^ 59
def prefixEnd_2537888 : Nat := 4983230072969 + 3 ^ 40 * 2537888 * 2
def baseEnd_2537888 : Nat := 289590309172860385606327

theorem tailTrace_2537888 : CollatzResearch.WordTrace tailWord_2537888 prefixEnd_2537888 289590309172860385606327 := by
  unfold tailWord_2537888
  simp only [CollatzResearch.WordTrace]
  refine ⟨46282189914836343803923159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61709586553115125071897545 46282189914836343803923159)
  ·
    refine ⟨69423284872254515705884739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46282189914836343803923159 69423284872254515705884739)
    ·
      refine ⟨104134927308381773558827109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69423284872254515705884739 104134927308381773558827109)
      ·
        refine ⟨19525298870321582542280083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104134927308381773558827109 19525298870321582542280083)
        ·
          refine ⟨29287948305482373813420125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19525298870321582542280083 29287948305482373813420125)
          ·
            refine ⟨10982980614555890180032547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29287948305482373813420125 10982980614555890180032547)
            ·
              refine ⟨16474470921833835270048821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10982980614555890180032547 16474470921833835270048821)
              ·
                refine ⟨1544481648921922056567077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16474470921833835270048821 1544481648921922056567077)
                ·
                  refine ⟨289590309172860385606327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1544481648921922056567077 289590309172860385606327)
                  ·
                    rfl

theorem cell22_2537888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 4].length) (baseStart_2537888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537888 prefixEnd_2537888 := by exact prefixLift 2537888
  have htrace : WordTrace (prefixWord ++ tailWord_2537888) baseStart_2537888 baseEnd_2537888 := by
    simpa [prefixWord, tailWord_2537888, baseEnd_2537888] using wordTrace_append hprefix tailTrace_2537888
  have hstable : (prefixWord ++ tailWord_2537888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537888).length < 2 ^ (prefixWord ++ tailWord_2537888).sum := by decide
  have hdescent : baseEnd_2537888 < baseStart_2537888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537976 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_2537976 : Nat := 118140960795 + 2537976 * 2 ^ 59
def prefixEnd_2537976 : Nat := 4983230072969 + 3 ^ 40 * 2537976 * 2
def baseEnd_2537976 : Nat := 868801051716978260618711

theorem tailTrace_2537976 : CollatzResearch.WordTrace tailWord_2537976 prefixEnd_2537976 868801051716978260618711 := by
  unfold tailWord_2537976
  simp only [CollatzResearch.WordTrace]
  refine ⟨46283794726676939318524891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61711726302235919091366521 46283794726676939318524891)
  ·
    refine ⟨69425692090015408977787337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46283794726676939318524891 69425692090015408977787337)
    ·
      refine ⟨52069269067511556733340503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69425692090015408977787337 52069269067511556733340503)
      ·
        refine ⟨78103903601267335100010755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52069269067511556733340503 78103903601267335100010755)
        ·
          refine ⟨117155855401901002650016133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78103903601267335100010755 117155855401901002650016133)
          ·
            refine ⟨21966722887856437996878025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117155855401901002650016133 21966722887856437996878025)
            ·
              refine ⟨16475042165892328497658519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21966722887856437996878025 16475042165892328497658519)
              ·
                refine ⟨24712563248838492746487779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16475042165892328497658519 24712563248838492746487779)
                ·
                  refine ⟨37068844873257739119731669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24712563248838492746487779 37068844873257739119731669)
                  ·
                    refine ⟨868801051716978260618711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37068844873257739119731669 868801051716978260618711)
                    ·
                      rfl

theorem cell22_2537976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_2537976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2537976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2537976 prefixEnd_2537976 := by exact prefixLift 2537976
  have htrace : WordTrace (prefixWord ++ tailWord_2537976) baseStart_2537976 baseEnd_2537976 := by
    simpa [prefixWord, tailWord_2537976, baseEnd_2537976] using wordTrace_append hprefix tailTrace_2537976
  have hstable : (prefixWord ++ tailWord_2537976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537976).length < 2 ^ (prefixWord ++ tailWord_2537976).sum := by decide
  have hdescent : baseEnd_2537976 < baseStart_2537976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538016 : List Nat := [2, 1, 1, 6, 2, 2, 2, 2, 1, 3]
def baseStart_2538016 : Nat := 118140960795 + 2538016 * 2 ^ 59
def prefixEnd_2538016 : Nat := 4983230072969 + 3 ^ 40 * 2538016 * 2
def baseEnd_2538016 : Nat := 868814744534431489618589

theorem tailTrace_2538016 : CollatzResearch.WordTrace tailWord_2538016 prefixEnd_2538016 868814744534431489618589 := by
  unfold tailWord_2538016
  simp only [CollatzResearch.WordTrace]
  refine ⟨46284524186604482734252951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61712698915472643645670601 46284524186604482734252951)
  ·
    refine ⟨69426786279906724101379427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46284524186604482734252951 69426786279906724101379427)
    ·
      refine ⟨104140179419860086152069141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69426786279906724101379427 104140179419860086152069141)
      ·
        refine ⟨4881570910305941538378241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104140179419860086152069141 4881570910305941538378241)
        ·
          refine ⟨3661178182729456153783681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4881570910305941538378241 3661178182729456153783681)
          ·
            refine ⟨2745883637047092115337761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3661178182729456153783681 2745883637047092115337761)
            ·
              refine ⟨2059412727785319086503321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2745883637047092115337761 2059412727785319086503321)
              ·
                refine ⟨1544559545838989314877491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2059412727785319086503321 1544559545838989314877491)
                ·
                  refine ⟨2316839318758483972316237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544559545838989314877491 2316839318758483972316237)
                  ·
                    refine ⟨868814744534431489618589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2316839318758483972316237 868814744534431489618589)
                    ·
                      rfl

theorem cell22_2538016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 1, 3].length) (baseStart_2538016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538016 prefixEnd_2538016 := by exact prefixLift 2538016
  have htrace : WordTrace (prefixWord ++ tailWord_2538016) baseStart_2538016 baseEnd_2538016 := by
    simpa [prefixWord, tailWord_2538016, baseEnd_2538016] using wordTrace_append hprefix tailTrace_2538016
  have hstable : (prefixWord ++ tailWord_2538016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538016).length < 2 ^ (prefixWord ++ tailWord_2538016).sum := by decide
  have hdescent : baseEnd_2538016 < baseStart_2538016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538051 : List Nat := [1, 1, 1, 3, 1, 2, 1, 12]
def baseStart_2538051 : Nat := 118140960795 + 2538051 * 2 ^ 59
def prefixEnd_2538051 : Nat := 4983230072969 + 3 ^ 40 * 2538051 * 2
def baseEnd_2538051 : Nat := 96536302861078118332609

theorem tailTrace_2538051 : CollatzResearch.WordTrace tailWord_2538051 prefixEnd_2538051 96536302861078118332609 := by
  unfold tailWord_2538051
  simp only [CollatzResearch.WordTrace]
  refine ⟨92570324928082166446030007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61713549952054777630686671 92570324928082166446030007)
  ·
    refine ⟨138855487392123249669045011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92570324928082166446030007 138855487392123249669045011)
    ·
      refine ⟨208283231088184874503567517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138855487392123249669045011 208283231088184874503567517)
      ·
        refine ⟨78106211658069327938837819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208283231088184874503567517 78106211658069327938837819)
        ·
          refine ⟨117159317487103991908256729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78106211658069327938837819 117159317487103991908256729)
          ·
            refine ⟨87869488115327993931192547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117159317487103991908256729 87869488115327993931192547)
            ·
              refine ⟨131804232172991990896788821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87869488115327993931192547 131804232172991990896788821)
              ·
                refine ⟨96536302861078118332609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 131804232172991990896788821 96536302861078118332609)
                ·
                  rfl

theorem cell22_2538051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 12].length) (baseStart_2538051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538051 prefixEnd_2538051 := by exact prefixLift 2538051
  have htrace : WordTrace (prefixWord ++ tailWord_2538051) baseStart_2538051 baseEnd_2538051 := by
    simpa [prefixWord, tailWord_2538051, baseEnd_2538051] using wordTrace_append hprefix tailTrace_2538051
  have hstable : (prefixWord ++ tailWord_2538051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538051).length < 2 ^ (prefixWord ++ tailWord_2538051).sum := by decide
  have hdescent : baseEnd_2538051 < baseStart_2538051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538053 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_2538053 : Nat := 118140960795 + 2538053 * 2 ^ 59
def prefixEnd_2538053 : Nat := 4983230072969 + 3 ^ 40 * 2538053 * 2
def baseEnd_2538053 : Nat := 868827410390575726443475

theorem tailTrace_2538053 : CollatzResearch.WordTrace tailWord_2538053 prefixEnd_2538053 868827410390575726443475 := by
  unfold tailWord_2538053
  simp only [CollatzResearch.WordTrace]
  refine ⟨92570397874074920787602813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61713598582716613858401875 92570397874074920787602813)
  ·
    refine ⟨34713899202778095295351055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92570397874074920787602813 34713899202778095295351055)
    ·
      refine ⟨52070848804167142943026583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34713899202778095295351055 52070848804167142943026583)
      ·
        refine ⟨78106273206250714414539875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52070848804167142943026583 78106273206250714414539875)
        ·
          refine ⟨117159409809376071621809813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78106273206250714414539875 117159409809376071621809813)
          ·
            refine ⟨5491847334814503357272335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117159409809376071621809813 5491847334814503357272335)
            ·
              refine ⟨8237771002221755035908503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5491847334814503357272335 8237771002221755035908503)
              ·
                refine ⟨12356656503332632553862755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8237771002221755035908503 12356656503332632553862755)
                ·
                  refine ⟨18534984754998948830794133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12356656503332632553862755 18534984754998948830794133)
                  ·
                    refine ⟨868827410390575726443475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18534984754998948830794133 868827410390575726443475)
                    ·
                      rfl

theorem cell22_2538053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_2538053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538053 prefixEnd_2538053 := by exact prefixLift 2538053
  have htrace : WordTrace (prefixWord ++ tailWord_2538053) baseStart_2538053 baseEnd_2538053 := by
    simpa [prefixWord, tailWord_2538053, baseEnd_2538053] using wordTrace_append hprefix tailTrace_2538053
  have hstable : (prefixWord ++ tailWord_2538053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538053).length < 2 ^ (prefixWord ++ tailWord_2538053).sum := by decide
  have hdescent : baseEnd_2538053 < baseStart_2538053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538068 : List Nat := [2, 4, 1, 1, 1, 4, 9]
def baseStart_2538068 : Nat := 118140960795 + 2538068 * 2 ^ 59
def prefixEnd_2538068 : Nat := 4983230072969 + 3 ^ 40 * 2538068 * 2
def baseEnd_2538068 : Nat := 32178983155448914345127

theorem tailTrace_2538068 : CollatzResearch.WordTrace tailWord_2538068 prefixEnd_2538068 32178983155448914345127 := by
  unfold tailWord_2538068
  simp only [CollatzResearch.WordTrace]
  refine ⟨46285472484510289174699429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61713963312680385566265905 46285472484510289174699429)
  ·
    refine ⟨8678526090845679220256143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46285472484510289174699429 8678526090845679220256143)
    ·
      refine ⟨13017789136268518830384215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8678526090845679220256143 13017789136268518830384215)
      ·
        refine ⟨19526683704402778245576323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13017789136268518830384215 19526683704402778245576323)
        ·
          refine ⟨29290025556604167368364485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19526683704402778245576323 29290025556604167368364485)
          ·
            refine ⟨5491879791863281381568341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29290025556604167368364485 5491879791863281381568341)
            ·
              refine ⟨32178983155448914345127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5491879791863281381568341 32178983155448914345127)
              ·
                rfl

theorem cell22_2538068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 9].length) (baseStart_2538068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538068 prefixEnd_2538068 := by exact prefixLift 2538068
  have htrace : WordTrace (prefixWord ++ tailWord_2538068) baseStart_2538068 baseEnd_2538068 := by
    simpa [prefixWord, tailWord_2538068, baseEnd_2538068] using wordTrace_append hprefix tailTrace_2538068
  have hstable : (prefixWord ++ tailWord_2538068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538068).length < 2 ^ (prefixWord ++ tailWord_2538068).sum := by decide
  have hdescent : baseEnd_2538068 < baseStart_2538068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538113 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 9]
def baseStart_2538113 : Nat := 118140960795 + 2538113 * 2 ^ 59
def prefixEnd_2538113 : Nat := 4983230072969 + 3 ^ 40 * 2538113 * 2
def baseEnd_2538113 : Nat := 289615983205585189981097

theorem tailTrace_2538113 : CollatzResearch.WordTrace tailWord_2538113 prefixEnd_2538113 289615983205585189981097 := by
  unfold tailWord_2538113
  simp only [CollatzResearch.WordTrace]
  refine ⟨92572586253857551034786993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61715057502571700689857995 92572586253857551034786993)
  ·
    refine ⟨69429439690393163276090245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92572586253857551034786993 69429439690393163276090245)
    ·
      refine ⟨13018019941948718114266921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69429439690393163276090245 13018019941948718114266921)
      ·
        refine ⟨9763514956461538585700191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13018019941948718114266921 9763514956461538585700191)
        ·
          refine ⟨14645272434692307878550287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9763514956461538585700191 14645272434692307878550287)
          ·
            refine ⟨21967908652038461817825431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14645272434692307878550287 21967908652038461817825431)
            ·
              refine ⟨32951862978057692726738147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21967908652038461817825431 32951862978057692726738147)
              ·
                refine ⟨49427794467086539090107221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32951862978057692726738147 49427794467086539090107221)
                ·
                  refine ⟨289615983205585189981097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49427794467086539090107221 289615983205585189981097)
                  ·
                    rfl

theorem cell22_2538113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_2538113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538113 prefixEnd_2538113 := by exact prefixLift 2538113
  have htrace : WordTrace (prefixWord ++ tailWord_2538113) baseStart_2538113 baseEnd_2538113 := by
    simpa [prefixWord, tailWord_2538113, baseEnd_2538113] using wordTrace_append hprefix tailTrace_2538113
  have hstable : (prefixWord ++ tailWord_2538113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538113).length < 2 ^ (prefixWord ++ tailWord_2538113).sum := by decide
  have hdescent : baseEnd_2538113 < baseStart_2538113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538130 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_2538130 : Nat := 118140960795 + 2538130 * 2 ^ 59
def prefixEnd_2538130 : Nat := 4983230072969 + 3 ^ 40 * 2538130 * 2
def baseEnd_2538130 : Nat := 289617923021391064089413

theorem tailTrace_2538130 : CollatzResearch.WordTrace tailWord_2538130 prefixEnd_2538130 289617923021391064089413 := by
  unfold tailWord_2538130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23143301573698990734538961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61715470863197308625437229 23143301573698990734538961)
  ·
    refine ⟨17357476180274243050904221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23143301573698990734538961 17357476180274243050904221)
    ·
      refine ⟨6509053567602841144089083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17357476180274243050904221 6509053567602841144089083)
      ·
        refine ⟨9763580351404261716133625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6509053567602841144089083 9763580351404261716133625)
        ·
          refine ⟨7322685263553196287100219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9763580351404261716133625 7322685263553196287100219)
          ·
            refine ⟨10984027895329794430650329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322685263553196287100219 10984027895329794430650329)
            ·
              refine ⟨8238020921497345822987747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10984027895329794430650329 8238020921497345822987747)
              ·
                refine ⟨12357031382246018734481621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8238020921497345822987747 12357031382246018734481621)
                ·
                  refine ⟨289617923021391064089413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12357031382246018734481621 289617923021391064089413)
                  ·
                    rfl

theorem cell22_2538130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_2538130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538130 prefixEnd_2538130 := by exact prefixLift 2538130
  have htrace : WordTrace (prefixWord ++ tailWord_2538130) baseStart_2538130 baseEnd_2538130 := by
    simpa [prefixWord, tailWord_2538130, baseEnd_2538130] using wordTrace_append hprefix tailTrace_2538130
  have hstable : (prefixWord ++ tailWord_2538130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538130).length < 2 ^ (prefixWord ++ tailWord_2538130).sum := by decide
  have hdescent : baseEnd_2538130 < baseStart_2538130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538207 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 2, 3]
def baseStart_2538207 : Nat := 118140960795 + 2538207 * 2 ^ 59
def prefixEnd_2538207 : Nat := 4983230072969 + 3 ^ 40 * 2538207 * 2
def baseEnd_2538207 : Nat := 868880127737770658093003

theorem tailTrace_2538207 : CollatzResearch.WordTrace tailWord_2538207 prefixEnd_2538207 868880127737770658093003 := by
  unfold tailWord_2538207
  simp only [CollatzResearch.WordTrace]
  refine ⟨92576014715517005088708875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61717343143678003392472583 92576014715517005088708875)
  ·
    refine ⟨138864022073275507633063313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92576014715517005088708875 138864022073275507633063313)
    ·
      refine ⟨104148016554956630724797485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138864022073275507633063313 104148016554956630724797485)
      ·
        refine ⟨39055506208108736521799057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104148016554956630724797485 39055506208108736521799057)
        ·
          refine ⟨29291629656081552391349293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39055506208108736521799057 29291629656081552391349293)
          ·
            refine ⟨10984361121030582146755985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29291629656081552391349293 10984361121030582146755985)
            ·
              refine ⟨8238270840772936610066989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10984361121030582146755985 8238270840772936610066989)
              ·
                refine ⟨3089351565289851228775121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8238270840772936610066989 3089351565289851228775121)
                ·
                  refine ⟨2317013673967388421581341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3089351565289851228775121 2317013673967388421581341)
                  ·
                    refine ⟨868880127737770658093003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2317013673967388421581341 868880127737770658093003)
                    ·
                      rfl

theorem cell22_2538207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 3].length) (baseStart_2538207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538207 prefixEnd_2538207 := by exact prefixLift 2538207
  have htrace : WordTrace (prefixWord ++ tailWord_2538207) baseStart_2538207 baseEnd_2538207 := by
    simpa [prefixWord, tailWord_2538207, baseEnd_2538207] using wordTrace_append hprefix tailTrace_2538207
  have hstable : (prefixWord ++ tailWord_2538207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538207).length < 2 ^ (prefixWord ++ tailWord_2538207).sum := by decide
  have hdescent : baseEnd_2538207 < baseStart_2538207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538222 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_2538222 : Nat := 118140960795 + 2538222 * 2 ^ 59
def prefixEnd_2538222 : Nat := 4983230072969 + 3 ^ 40 * 2538222 * 2
def baseEnd_2538222 : Nat := 868885262544315618967957

theorem tailTrace_2538222 : CollatzResearch.WordTrace tailWord_2538222 prefixEnd_2538222 868885262544315618967957 := by
  unfold tailWord_2538222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11572070226307832831313115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61717707873641775100336613 11572070226307832831313115)
  ·
    refine ⟨17358105339461749246969673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11572070226307832831313115 17358105339461749246969673)
    ·
      refine ⟨13018579004596311935227255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17358105339461749246969673 13018579004596311935227255)
      ·
        refine ⟨19527868506894467902840883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13018579004596311935227255 19527868506894467902840883)
        ·
          refine ⟨29291802760341701854261325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19527868506894467902840883 29291802760341701854261325)
          ·
            refine ⟨10984426035128138195347997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29291802760341701854261325 10984426035128138195347997)
            ·
              refine ⟨4119159763173051823255499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10984426035128138195347997 4119159763173051823255499)
              ·
                refine ⟨6178739644759577734883249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4119159763173051823255499 6178739644759577734883249)
                ·
                  refine ⟨4634054733569683301162437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6178739644759577734883249 4634054733569683301162437)
                  ·
                    refine ⟨868885262544315618967957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4634054733569683301162437 868885262544315618967957)
                    ·
                      rfl

theorem cell22_2538222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_2538222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538222 prefixEnd_2538222 := by exact prefixLift 2538222
  have htrace : WordTrace (prefixWord ++ tailWord_2538222) baseStart_2538222 baseEnd_2538222 := by
    simpa [prefixWord, tailWord_2538222, baseEnd_2538222] using wordTrace_append hprefix tailTrace_2538222
  have hstable : (prefixWord ++ tailWord_2538222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538222).length < 2 ^ (prefixWord ++ tailWord_2538222).sum := by decide
  have hdescent : baseEnd_2538222 < baseStart_2538222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538258 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2538258 : Nat := 118140960795 + 2538258 * 2 ^ 59
def prefixEnd_2538258 : Nat := 4983230072969 + 3 ^ 40 * 2538258 * 2
def baseEnd_2538258 : Nat := 868897586080023525067847

theorem tailTrace_2538258 : CollatzResearch.WordTrace tailWord_2538258 prefixEnd_2538258 868897586080023525067847 := by
  unfold tailWord_2538258
  simp only [CollatzResearch.WordTrace]
  refine ⟨23144468709583060199703857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61718583225554827199210285 23144468709583060199703857)
  ·
    refine ⟨17358351532187295149777893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23144468709583060199703857 17358351532187295149777893)
    ·
      refine ⟨3254690912285117840583355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17358351532187295149777893 3254690912285117840583355)
      ·
        refine ⟨4882036368427676760875033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254690912285117840583355 4882036368427676760875033)
        ·
          refine ⟨3661527276320757570656275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4882036368427676760875033 3661527276320757570656275)
          ·
            refine ⟨5492290914481136355984413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3661527276320757570656275 5492290914481136355984413)
            ·
              refine ⟨2059609092930426133494155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5492290914481136355984413 2059609092930426133494155)
              ·
                refine ⟨3089413639395639200241233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059609092930426133494155 3089413639395639200241233)
                ·
                  refine ⟨2317060229546729400180925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3089413639395639200241233 2317060229546729400180925)
                  ·
                    refine ⟨868897586080023525067847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2317060229546729400180925 868897586080023525067847)
                    ·
                      rfl

theorem cell22_2538258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2538258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538258 prefixEnd_2538258 := by exact prefixLift 2538258
  have htrace : WordTrace (prefixWord ++ tailWord_2538258) baseStart_2538258 baseEnd_2538258 := by
    simpa [prefixWord, tailWord_2538258, baseEnd_2538258] using wordTrace_append hprefix tailTrace_2538258
  have hstable : (prefixWord ++ tailWord_2538258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538258).length < 2 ^ (prefixWord ++ tailWord_2538258).sum := by decide
  have hdescent : baseEnd_2538258 < baseStart_2538258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538329 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 1, 4]
def baseStart_2538329 : Nat := 118140960795 + 2538329 * 2 ^ 59
def prefixEnd_2538329 : Nat := 4983230072969 + 3 ^ 40 * 2538329 * 2
def baseEnd_2538329 : Nat := 868921890831003006542629

theorem tailTrace_2538329 : CollatzResearch.WordTrace tailWord_2538329 prefixEnd_2538329 868921890831003006542629 := by
  unfold tailWord_2538329
  simp only [CollatzResearch.WordTrace]
  refine ⟨92580464421075019924650041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61720309614050013283100027 92580464421075019924650041)
  ·
    refine ⟨69435348315806264943487531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92580464421075019924650041 69435348315806264943487531)
    ·
      refine ⟨104153022473709397415231297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69435348315806264943487531 104153022473709397415231297)
      ·
        refine ⟨78114766855282048061423473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104153022473709397415231297 78114766855282048061423473)
        ·
          refine ⟨58586075141461536046067605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78114766855282048061423473 58586075141461536046067605)
          ·
            refine ⟨2746222272256009502159419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58586075141461536046067605 2746222272256009502159419)
            ·
              refine ⟨4119333408384014253239129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746222272256009502159419 4119333408384014253239129)
              ·
                refine ⟨3089500056288010689929347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4119333408384014253239129 3089500056288010689929347)
                ·
                  refine ⟨4634250084432016034894021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089500056288010689929347 4634250084432016034894021)
                  ·
                    refine ⟨868921890831003006542629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4634250084432016034894021 868921890831003006542629)
                    ·
                      rfl

theorem cell22_2538329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 4].length) (baseStart_2538329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538329 prefixEnd_2538329 := by exact prefixLift 2538329
  have htrace : WordTrace (prefixWord ++ tailWord_2538329) baseStart_2538329 baseEnd_2538329 := by
    simpa [prefixWord, tailWord_2538329, baseEnd_2538329] using wordTrace_append hprefix tailTrace_2538329
  have hstable : (prefixWord ++ tailWord_2538329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538329).length < 2 ^ (prefixWord ++ tailWord_2538329).sum := by decide
  have hdescent : baseEnd_2538329 < baseStart_2538329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538361 : List Nat := [1, 2, 1, 3, 2, 5, 2, 2, 4]
def baseStart_2538361 : Nat := 118140960795 + 2538361 * 2 ^ 59
def prefixEnd_2538361 : Nat := 4983230072969 + 3 ^ 40 * 2538361 * 2
def baseEnd_2538361 : Nat := 289644281694988529914177

theorem tailTrace_2538361 : CollatzResearch.WordTrace tailWord_2538361 prefixEnd_2538361 289644281694988529914177 := by
  unfold tailWord_2538361
  simp only [CollatzResearch.WordTrace]
  refine ⟨92581631556959089389814937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61721087704639392926543291 92581631556959089389814937)
  ·
    refine ⟨69436223667719317042361203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92581631556959089389814937 69436223667719317042361203)
    ·
      refine ⟨104154335501578975563541805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69436223667719317042361203 104154335501578975563541805)
      ·
        refine ⟨39057875813092115836328177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104154335501578975563541805 39057875813092115836328177)
        ·
          refine ⟨29293406859819086877246133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39057875813092115836328177 29293406859819086877246133)
          ·
            refine ⟨2746256893108039394741825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29293406859819086877246133 2746256893108039394741825)
            ·
              refine ⟨2059692669831029546056369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2746256893108039394741825 2059692669831029546056369)
              ·
                refine ⟨1544769502373272159542277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2059692669831029546056369 1544769502373272159542277)
                ·
                  refine ⟨289644281694988529914177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1544769502373272159542277 289644281694988529914177)
                  ·
                    rfl

theorem cell22_2538361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 4].length) (baseStart_2538361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538361 prefixEnd_2538361 := by exact prefixLift 2538361
  have htrace : WordTrace (prefixWord ++ tailWord_2538361) baseStart_2538361 baseEnd_2538361 := by
    simpa [prefixWord, tailWord_2538361, baseEnd_2538361] using wordTrace_append hprefix tailTrace_2538361
  have hstable : (prefixWord ++ tailWord_2538361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538361).length < 2 ^ (prefixWord ++ tailWord_2538361).sum := by decide
  have hdescent : baseEnd_2538361 < baseStart_2538361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538385 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_2538385 : Nat := 118140960795 + 2538385 * 2 ^ 59
def prefixEnd_2538385 : Nat := 4983230072969 + 3 ^ 40 * 2538385 * 2
def baseEnd_2538385 : Nat := 868941060775437527142457

theorem tailTrace_2538385 : CollatzResearch.WordTrace tailWord_2538385 prefixEnd_2538385 868941060775437527142457 := by
  unfold tailWord_2538385
  simp only [CollatzResearch.WordTrace]
  refine ⟨92582506908872141488688609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61721671272581427659125739 92582506908872141488688609)
  ·
    refine ⟨69436880181654106116516457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92582506908872141488688609 69436880181654106116516457)
    ·
      refine ⟨52077660136240579587387343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69436880181654106116516457 52077660136240579587387343)
      ·
        refine ⟨78116490204360869381081015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52077660136240579587387343 78116490204360869381081015)
        ·
          refine ⟨117174735306541304071621523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78116490204360869381081015 117174735306541304071621523)
          ·
            refine ⟨175762102959811956107432285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117174735306541304071621523 175762102959811956107432285)
            ·
              refine ⟨65910788609929483540287107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175762102959811956107432285 65910788609929483540287107)
              ·
                refine ⟨98866182914894225310430661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65910788609929483540287107 98866182914894225310430661)
                ·
                  refine ⟨18537409296542667245705749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98866182914894225310430661 18537409296542667245705749)
                  ·
                    refine ⟨868941060775437527142457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18537409296542667245705749 868941060775437527142457)
                    ·
                      rfl

theorem cell22_2538385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_2538385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538385 prefixEnd_2538385 := by exact prefixLift 2538385
  have htrace : WordTrace (prefixWord ++ tailWord_2538385) baseStart_2538385 baseEnd_2538385 := by
    simpa [prefixWord, tailWord_2538385, baseEnd_2538385] using wordTrace_append hprefix tailTrace_2538385
  have hstable : (prefixWord ++ tailWord_2538385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538385).length < 2 ^ (prefixWord ++ tailWord_2538385).sum := by decide
  have hdescent : baseEnd_2538385 < baseStart_2538385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538421 : List Nat := [1, 3, 3, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2538421 : Nat := 118140960795 + 2538421 * 2 ^ 59
def prefixEnd_2538421 : Nat := 4983230072969 + 3 ^ 40 * 2538421 * 2
def baseEnd_2538421 : Nat := 868953384311145433242347

theorem tailTrace_2538421 : CollatzResearch.WordTrace tailWord_2538421 prefixEnd_2538421 868953384311145433242347 := by
  unfold tailWord_2538421
  simp only [CollatzResearch.WordTrace]
  refine ⟨92583819936741719636999117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61722546624494479757999411 92583819936741719636999117)
  ·
    refine ⟨34718932476278144863874669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92583819936741719636999117 34718932476278144863874669)
    ·
      refine ⟨13019599678604304323953001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34718932476278144863874669 13019599678604304323953001)
      ·
        refine ⟨9764699758953228242964751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13019599678604304323953001 9764699758953228242964751)
        ·
          refine ⟨14647049638429842364447127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9764699758953228242964751 14647049638429842364447127)
          ·
            refine ⟨21970574457644763546670691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14647049638429842364447127 21970574457644763546670691)
            ·
              refine ⟨32955861686467145320006037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21970574457644763546670691 32955861686467145320006037)
              ·
                refine ⟨1544806016553147436875283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32955861686467145320006037 1544806016553147436875283)
                ·
                  refine ⟨2317209024829721155312925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544806016553147436875283 2317209024829721155312925)
                  ·
                    refine ⟨868953384311145433242347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2317209024829721155312925 868953384311145433242347)
                    ·
                      rfl

theorem cell22_2538421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2538421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538421 prefixEnd_2538421 := by exact prefixLift 2538421
  have htrace : WordTrace (prefixWord ++ tailWord_2538421) baseStart_2538421 baseEnd_2538421 := by
    simpa [prefixWord, tailWord_2538421, baseEnd_2538421] using wordTrace_append hprefix tailTrace_2538421
  have hstable : (prefixWord ++ tailWord_2538421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538421).length < 2 ^ (prefixWord ++ tailWord_2538421).sum := by decide
  have hdescent : baseEnd_2538421 < baseStart_2538421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538432 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_2538432 : Nat := 118140960795 + 2538432 * 2 ^ 59
def prefixEnd_2538432 : Nat := 4983230072969 + 3 ^ 40 * 2538432 * 2
def baseEnd_2538432 : Nat := 868957149835945071217313

theorem tailTrace_2538432 : CollatzResearch.WordTrace tailWord_2538432 prefixEnd_2538432 868957149835945071217313 := by
  unfold tailWord_2538432
  simp only [CollatzResearch.WordTrace]
  refine ⟨46292110569850934257824775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61722814093134579010433033 46292110569850934257824775)
  ·
    refine ⟨69438165854776401386737163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46292110569850934257824775 69438165854776401386737163)
    ·
      refine ⟨104157248782164602080105745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69438165854776401386737163 104157248782164602080105745)
      ·
        refine ⟨78117936586623451560079309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104157248782164602080105745 78117936586623451560079309)
        ·
          refine ⟨29294226219983794335029741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78117936586623451560079309 29294226219983794335029741)
          ·
            refine ⟨10985334832493922875636153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29294226219983794335029741 10985334832493922875636153)
            ·
              refine ⟨8239001124370442156727115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10985334832493922875636153 8239001124370442156727115)
              ·
                refine ⟨12358501686555663235090673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8239001124370442156727115 12358501686555663235090673)
                ·
                  refine ⟨9268876264916747426318005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12358501686555663235090673 9268876264916747426318005)
                  ·
                    refine ⟨868957149835945071217313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9268876264916747426318005 868957149835945071217313)
                    ·
                      rfl

theorem cell22_2538432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_2538432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538432 prefixEnd_2538432 := by exact prefixLift 2538432
  have htrace : WordTrace (prefixWord ++ tailWord_2538432) baseStart_2538432 baseEnd_2538432 := by
    simpa [prefixWord, tailWord_2538432, baseEnd_2538432] using wordTrace_append hprefix tailTrace_2538432
  have hstable : (prefixWord ++ tailWord_2538432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538432).length < 2 ^ (prefixWord ++ tailWord_2538432).sum := by decide
  have hdescent : baseEnd_2538432 < baseStart_2538432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538479 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 6]
def baseStart_2538479 : Nat := 118140960795 + 2538479 * 2 ^ 59
def prefixEnd_2538479 : Nat := 4983230072969 + 3 ^ 40 * 2538479 * 2
def baseEnd_2538479 : Nat := 289657746298817538430723

theorem tailTrace_2538479 : CollatzResearch.WordTrace tailWord_2538479 prefixEnd_2538479 289657746298817538430723 := by
  unfold tailWord_2538479
  simp only [CollatzResearch.WordTrace]
  refine ⟨92585935370531595542610491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61723956913687730361740327 92585935370531595542610491)
  ·
    refine ⟨138878903055797393313915737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92585935370531595542610491 138878903055797393313915737)
    ·
      refine ⟨104159177291848044985436803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138878903055797393313915737 104159177291848044985436803)
      ·
        refine ⟨156238765937772067478155205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104159177291848044985436803 156238765937772067478155205)
        ·
          refine ⟨29294768613332262652154101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156238765937772067478155205 29294768613332262652154101)
          ·
            refine ⟨2746384557499899623639447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29294768613332262652154101 2746384557499899623639447)
            ·
              refine ⟨4119576836249849435459171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746384557499899623639447 4119576836249849435459171)
              ·
                refine ⟨6179365254374774153188757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4119576836249849435459171 6179365254374774153188757)
                ·
                  refine ⟨289657746298817538430723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6179365254374774153188757 289657746298817538430723)
                  ·
                    rfl

theorem cell22_2538479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 6].length) (baseStart_2538479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538479 prefixEnd_2538479 := by exact prefixLift 2538479
  have htrace : WordTrace (prefixWord ++ tailWord_2538479) baseStart_2538479 baseEnd_2538479 := by
    simpa [prefixWord, tailWord_2538479, baseEnd_2538479] using wordTrace_append hprefix tailTrace_2538479
  have hstable : (prefixWord ++ tailWord_2538479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538479).length < 2 ^ (prefixWord ++ tailWord_2538479).sum := by decide
  have hdescent : baseEnd_2538479 < baseStart_2538479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538485 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 5]
def baseStart_2538485 : Nat := 118140960795 + 2538485 * 2 ^ 59
def prefixEnd_2538485 : Nat := 4983230072969 + 3 ^ 40 * 2538485 * 2
def baseEnd_2538485 : Nat := 289658430939690199880717

theorem tailTrace_2538485 : CollatzResearch.WordTrace tailWord_2538485 prefixEnd_2538485 289658430939690199880717 := by
  unfold tailWord_2538485
  simp only [CollatzResearch.WordTrace]
  refine ⟨92586154208509858567328909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61724102805673239044885939 92586154208509858567328909)
  ·
    refine ⟨34719807828191196962748341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92586154208509858567328909 34719807828191196962748341)
    ·
      refine ⟨3254981983892924715257657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34719807828191196962748341 3254981983892924715257657)
      ·
        refine ⟨2441236487919693536443243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3254981983892924715257657 2441236487919693536443243)
        ·
          refine ⟨3661854731879540304664865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441236487919693536443243 3661854731879540304664865)
          ·
            refine ⟨2746391048909655228498649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3661854731879540304664865 2746391048909655228498649)
            ·
              refine ⟨2059793286682241421373987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2746391048909655228498649 2059793286682241421373987)
              ·
                refine ⟨3089689930023362132060981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059793286682241421373987 3089689930023362132060981)
                ·
                  refine ⟨289658430939690199880717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3089689930023362132060981 289658430939690199880717)
                  ·
                    rfl

theorem cell22_2538485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_2538485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538485 prefixEnd_2538485 := by exact prefixLift 2538485
  have htrace : WordTrace (prefixWord ++ tailWord_2538485) baseStart_2538485 baseEnd_2538485 := by
    simpa [prefixWord, tailWord_2538485, baseEnd_2538485] using wordTrace_append hprefix tailTrace_2538485
  have hstable : (prefixWord ++ tailWord_2538485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538485).length < 2 ^ (prefixWord ++ tailWord_2538485).sum := by decide
  have hdescent : baseEnd_2538485 < baseStart_2538485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538498 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2538498 : Nat := 118140960795 + 2538498 * 2 ^ 59
def prefixEnd_2538498 : Nat := 4983230072969 + 3 ^ 40 * 2538498 * 2
def baseEnd_2538498 : Nat := 868979742984742899067111

theorem tailTrace_2538498 : CollatzResearch.WordTrace tailWord_2538498 prefixEnd_2538498 868979742984742899067111 := by
  unfold tailWord_2538498
  simp only [CollatzResearch.WordTrace]
  refine ⟨23146657089365690446888037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61724418904975174525034765 23146657089365690446888037)
  ·
    refine ⟨4339998204256066958791507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23146657089365690446888037 4339998204256066958791507)
    ·
      refine ⟨6509997306384100438187261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4339998204256066958791507 6509997306384100438187261)
      ·
        refine ⟨2441248989894037664320223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6509997306384100438187261 2441248989894037664320223)
        ·
          refine ⟨3661873484841056496480335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441248989894037664320223 3661873484841056496480335)
          ·
            refine ⟨5492810227261584744720503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3661873484841056496480335 5492810227261584744720503)
            ·
              refine ⟨8239215340892377117080755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5492810227261584744720503 8239215340892377117080755)
              ·
                refine ⟨12358823011338565675621133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8239215340892377117080755 12358823011338565675621133)
                ·
                  refine ⟨4634558629251962128357925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12358823011338565675621133 4634558629251962128357925)
                  ·
                    refine ⟨868979742984742899067111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4634558629251962128357925 868979742984742899067111)
                    ·
                      rfl

theorem cell22_2538498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2538498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538498 prefixEnd_2538498 := by exact prefixLift 2538498
  have htrace : WordTrace (prefixWord ++ tailWord_2538498) baseStart_2538498 baseEnd_2538498 := by
    simpa [prefixWord, tailWord_2538498, baseEnd_2538498] using wordTrace_append hprefix tailTrace_2538498
  have hstable : (prefixWord ++ tailWord_2538498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538498).length < 2 ^ (prefixWord ++ tailWord_2538498).sum := by decide
  have hdescent : baseEnd_2538498 < baseStart_2538498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538507 : List Nat := [1, 1, 1, 1, 6, 2, 2, 8]
def baseStart_2538507 : Nat := 118140960795 + 2538507 * 2 ^ 59
def prefixEnd_2538507 : Nat := 4983230072969 + 3 ^ 40 * 2538507 * 2
def baseEnd_2538507 : Nat := 96553647096518875065787

theorem tailTrace_2538507 : CollatzResearch.WordTrace tailWord_2538507 prefixEnd_2538507 96553647096518875065787 := by
  unfold tailWord_2538507
  simp only [CollatzResearch.WordTrace]
  refine ⟨92586956614430156324629775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61724637742953437549753183 92586956614430156324629775)
  ·
    refine ⟨138880434921645234486944663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92586956614430156324629775 138880434921645234486944663)
    ·
      refine ⟨208320652382467851730416995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138880434921645234486944663 208320652382467851730416995)
      ·
        refine ⟨312480978573701777595625493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208320652382467851730416995 312480978573701777595625493)
        ·
          refine ⟨14647545870642270824794945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 312480978573701777595625493 14647545870642270824794945)
          ·
            refine ⟨10985659402981703118596209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14647545870642270824794945 10985659402981703118596209)
            ·
              refine ⟨8239244552236277338947157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10985659402981703118596209 8239244552236277338947157)
              ·
                refine ⟨96553647096518875065787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8239244552236277338947157 96553647096518875065787)
                ·
                  rfl

theorem cell22_2538507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 8].length) (baseStart_2538507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538507 prefixEnd_2538507 := by exact prefixLift 2538507
  have htrace : WordTrace (prefixWord ++ tailWord_2538507) baseStart_2538507 baseEnd_2538507 := by
    simpa [prefixWord, tailWord_2538507, baseEnd_2538507] using wordTrace_append hprefix tailTrace_2538507
  have hstable : (prefixWord ++ tailWord_2538507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538507).length < 2 ^ (prefixWord ++ tailWord_2538507).sum := by decide
  have hdescent : baseEnd_2538507 < baseStart_2538507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538524 : List Nat := [2, 2, 3, 1, 5, 9]
def baseStart_2538524 : Nat := 118140960795 + 2538524 * 2 ^ 59
def prefixEnd_2538524 : Nat := 4983230072969 + 3 ^ 40 * 2538524 * 2
def baseEnd_2538524 : Nat := 10728254855754166640951

theorem tailTrace_2538524 : CollatzResearch.WordTrace tailWord_2538524 prefixEnd_2538524 10728254855754166640951 := by
  unfold tailWord_2538524
  simp only [CollatzResearch.WordTrace]
  refine ⟨46293788327684284113999313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61725051103579045485332417 46293788327684284113999313)
  ·
    refine ⟨34720341245763213085499485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46293788327684284113999313 34720341245763213085499485)
    ·
      refine ⟨13020127967161204907062307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34720341245763213085499485 13020127967161204907062307)
      ·
        refine ⟨19530191950741807360593461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13020127967161204907062307 19530191950741807360593461)
        ·
          refine ⟨1830955495382044440055637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19530191950741807360593461 1830955495382044440055637)
          ·
            refine ⟨10728254855754166640951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1830955495382044440055637 10728254855754166640951)
            ·
              rfl

theorem cell22_2538524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 9].length) (baseStart_2538524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538524 prefixEnd_2538524 := by exact prefixLift 2538524
  have htrace : WordTrace (prefixWord ++ tailWord_2538524) baseStart_2538524 baseEnd_2538524 := by
    simpa [prefixWord, tailWord_2538524, baseEnd_2538524] using wordTrace_append hprefix tailTrace_2538524
  have hstable : (prefixWord ++ tailWord_2538524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538524).length < 2 ^ (prefixWord ++ tailWord_2538524).sum := by decide
  have hdescent : baseEnd_2538524 < baseStart_2538524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538539 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 3, 3]
def baseStart_2538539 : Nat := 118140960795 + 2538539 * 2 ^ 59
def prefixEnd_2538539 : Nat := 4983230072969 + 3 ^ 40 * 2538539 * 2
def baseEnd_2538539 : Nat := 868993778122632458791985

theorem tailTrace_2538539 : CollatzResearch.WordTrace tailWord_2538539 prefixEnd_2538539 868993778122632458791985 := by
  unfold tailWord_2538539
  simp only [CollatzResearch.WordTrace]
  refine ⟨92588123750314225789794671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61725415833542817193196447 92588123750314225789794671)
  ·
    refine ⟨138882185625471338684692007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92588123750314225789794671 138882185625471338684692007)
    ·
      refine ⟨208323278438207008027038011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138882185625471338684692007 208323278438207008027038011)
      ·
        refine ⟨312484917657310512040557017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208323278438207008027038011 312484917657310512040557017)
        ·
          refine ⟨234363688242982884030417763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312484917657310512040557017 234363688242982884030417763)
          ·
            refine ⟨351545532364474326045626645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234363688242982884030417763 351545532364474326045626645)
            ·
              refine ⟨16478696829584734033388749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 351545532364474326045626645 16478696829584734033388749)
              ·
                refine ⟨6179511311094275262520781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16478696829584734033388749 6179511311094275262520781)
                ·
                  refine ⟨2317316741660353223445293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6179511311094275262520781 2317316741660353223445293)
                  ·
                    refine ⟨868993778122632458791985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2317316741660353223445293 868993778122632458791985)
                    ·
                      rfl

theorem cell22_2538539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 3].length) (baseStart_2538539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538539 prefixEnd_2538539 := by exact prefixLift 2538539
  have htrace : WordTrace (prefixWord ++ tailWord_2538539) baseStart_2538539 baseEnd_2538539 := by
    simpa [prefixWord, tailWord_2538539, baseEnd_2538539] using wordTrace_append hprefix tailTrace_2538539
  have hstable : (prefixWord ++ tailWord_2538539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538539).length < 2 ^ (prefixWord ++ tailWord_2538539).sum := by decide
  have hdescent : baseEnd_2538539 < baseStart_2538539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538556 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 3, 3]
def baseStart_2538556 : Nat := 118140960795 + 2538556 * 2 ^ 59
def prefixEnd_2538556 : Nat := 4983230072969 + 3 ^ 40 * 2538556 * 2
def baseEnd_2538556 : Nat := 868999597570050081116933

theorem tailTrace_2538556 : CollatzResearch.WordTrace tailWord_2538556 prefixEnd_2538556 868999597570050081116933 := by
  unfold tailWord_2538556
  simp only [CollatzResearch.WordTrace]
  refine ⟨46294371895626318846581761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61725829194168425128775681 46294371895626318846581761)
  ·
    refine ⟨34720778921719739134936321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46294371895626318846581761 34720778921719739134936321)
    ·
      refine ⟨26040584191289804351202241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34720778921719739134936321 26040584191289804351202241)
      ·
        refine ⟨19530438143467353263401681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26040584191289804351202241 19530438143467353263401681)
        ·
          refine ⟨14647828607600514947551261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19530438143467353263401681 14647828607600514947551261)
          ·
            refine ⟨5492935727850193105331723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14647828607600514947551261 5492935727850193105331723)
            ·
              refine ⟨8239403591775289657997585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5492935727850193105331723 8239403591775289657997585)
              ·
                refine ⟨6179552693831467243498189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8239403591775289657997585 6179552693831467243498189)
                ·
                  refine ⟨2317332260186800216311821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6179552693831467243498189 2317332260186800216311821)
                  ·
                    refine ⟨868999597570050081116933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2317332260186800216311821 868999597570050081116933)
                    ·
                      rfl

theorem cell22_2538556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_2538556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538556 prefixEnd_2538556 := by exact prefixLift 2538556
  have htrace : WordTrace (prefixWord ++ tailWord_2538556) baseStart_2538556 baseEnd_2538556 := by
    simpa [prefixWord, tailWord_2538556, baseEnd_2538556] using wordTrace_append hprefix tailTrace_2538556
  have hstable : (prefixWord ++ tailWord_2538556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538556).length < 2 ^ (prefixWord ++ tailWord_2538556).sum := by decide
  have hdescent : baseEnd_2538556 < baseStart_2538556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538590 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2538590 : Nat := 118140960795 + 2538590 * 2 ^ 59
def prefixEnd_2538590 : Nat := 4983230072969 + 3 ^ 40 * 2538590 * 2
def baseEnd_2538590 : Nat := 869011236464885325766829

theorem tailTrace_2538590 : CollatzResearch.WordTrace tailWord_2538590 prefixEnd_2538590 869011236464885325766829 := by
  unfold tailWord_2538590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11573747984141182687487653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61726655915419640999934149 11573747984141182687487653)
  ·
    refine ⟨2170077747026471753903935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11573747984141182687487653 2170077747026471753903935)
    ·
      refine ⟨3255116620539707630855903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2170077747026471753903935 3255116620539707630855903)
      ·
        refine ⟨4882674930809561446283855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3255116620539707630855903 4882674930809561446283855)
        ·
          refine ⟨7324012396214342169425783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882674930809561446283855 7324012396214342169425783)
          ·
            refine ⟨10986018594321513254138675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7324012396214342169425783 10986018594321513254138675)
            ·
              refine ⟨16479027891482269881208013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10986018594321513254138675 16479027891482269881208013)
              ·
                refine ⟨6179635459305851205453005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16479027891482269881208013 6179635459305851205453005)
                ·
                  refine ⟨2317363297239694202044877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6179635459305851205453005 2317363297239694202044877)
                  ·
                    refine ⟨869011236464885325766829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2317363297239694202044877 869011236464885325766829)
                    ·
                      rfl

theorem cell22_2538590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2538590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538590 prefixEnd_2538590 := by exact prefixLift 2538590
  have htrace : WordTrace (prefixWord ++ tailWord_2538590) baseStart_2538590 baseEnd_2538590 := by
    simpa [prefixWord, tailWord_2538590, baseEnd_2538590] using wordTrace_append hprefix tailTrace_2538590
  have hstable : (prefixWord ++ tailWord_2538590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538590).length < 2 ^ (prefixWord ++ tailWord_2538590).sum := by decide
  have hdescent : baseEnd_2538590 < baseStart_2538590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538710 : List Nat := [5, 2, 1, 2, 2, 2, 1, 7]
def baseStart_2538710 : Nat := 118140960795 + 2538710 * 2 ^ 59
def prefixEnd_2538710 : Nat := 4983230072969 + 3 ^ 40 * 2538710 * 2
def baseEnd_2538710 : Nat := 96561368324138334751829

theorem tailTrace_2538710 : CollatzResearch.WordTrace tailWord_2538710 prefixEnd_2538710 96561368324138334751829 := by
  unfold tailWord_2538710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5787147539543420124641849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61729573755129814662846389 5787147539543420124641849)
  ·
    refine ⟨4340360654657565093481387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5787147539543420124641849 4340360654657565093481387)
    ·
      refine ⟨6510540981986347640222081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4340360654657565093481387 6510540981986347640222081)
      ·
        refine ⟨4882905736489760730166561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6510540981986347640222081 4882905736489760730166561)
        ·
          refine ⟨3662179302367320547624921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4882905736489760730166561 3662179302367320547624921)
          ·
            refine ⟨2746634476775490410718691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3662179302367320547624921 2746634476775490410718691)
            ·
              refine ⟨4119951715163235616078037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746634476775490410718691 4119951715163235616078037)
              ·
                refine ⟨96561368324138334751829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4119951715163235616078037 96561368324138334751829)
                ·
                  rfl

theorem cell22_2538710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_2538710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538710 prefixEnd_2538710 := by exact prefixLift 2538710
  have htrace : WordTrace (prefixWord ++ tailWord_2538710) baseStart_2538710 baseEnd_2538710 := by
    simpa [prefixWord, tailWord_2538710, baseEnd_2538710] using wordTrace_append hprefix tailTrace_2538710
  have hstable : (prefixWord ++ tailWord_2538710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538710).length < 2 ^ (prefixWord ++ tailWord_2538710).sum := by decide
  have hdescent : baseEnd_2538710 < baseStart_2538710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538719 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 1, 7]
def baseStart_2538719 : Nat := 118140960795 + 2538719 * 2 ^ 59
def prefixEnd_2538719 : Nat := 4983230072969 + 3 ^ 40 * 2538719 * 2
def baseEnd_2538719 : Nat := 869055395801171989291433

theorem tailTrace_2538719 : CollatzResearch.WordTrace tailWord_2538719 prefixEnd_2538719 869055395801171989291433 := by
  unfold tailWord_2538719
  simp only [CollatzResearch.WordTrace]
  refine ⟨92594688889662116531347211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61729792593108077687564807 92594688889662116531347211)
  ·
    refine ⟨138892033334493174797020817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92594688889662116531347211 138892033334493174797020817)
    ·
      refine ⟨104169025000869881097765613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138892033334493174797020817 104169025000869881097765613)
      ·
        refine ⟨39063384375326205411662105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104169025000869881097765613 39063384375326205411662105)
        ·
          refine ⟨29297538281494654058746579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39063384375326205411662105 29297538281494654058746579)
          ·
            refine ⟨43946307422241981088119869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29297538281494654058746579 43946307422241981088119869)
            ·
              refine ⟨16479865283340742908044951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43946307422241981088119869 16479865283340742908044951)
              ·
                refine ⟨24719797925011114362067427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16479865283340742908044951 24719797925011114362067427)
                ·
                  refine ⟨37079696887516671543101141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24719797925011114362067427 37079696887516671543101141)
                  ·
                    refine ⟨869055395801171989291433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37079696887516671543101141 869055395801171989291433)
                    ·
                      rfl

theorem cell22_2538719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_2538719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538719 prefixEnd_2538719 := by exact prefixLift 2538719
  have htrace : WordTrace (prefixWord ++ tailWord_2538719) baseStart_2538719 baseEnd_2538719 := by
    simpa [prefixWord, tailWord_2538719, baseEnd_2538719] using wordTrace_append hprefix tailTrace_2538719
  have hstable : (prefixWord ++ tailWord_2538719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538719).length < 2 ^ (prefixWord ++ tailWord_2538719).sum := by decide
  have hdescent : baseEnd_2538719 < baseStart_2538719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538721 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 5]
def baseStart_2538721 : Nat := 118140960795 + 2538721 * 2 ^ 59
def prefixEnd_2538721 : Nat := 4983230072969 + 3 ^ 40 * 2538721 * 2
def baseEnd_2538721 : Nat := 289685360147348216913809

theorem tailTrace_2538721 : CollatzResearch.WordTrace tailWord_2538721 prefixEnd_2538721 289685360147348216913809 := by
  unfold tailWord_2538721
  simp only [CollatzResearch.WordTrace]
  refine ⟨92594761835654870872920017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61729841223769913915280011 92594761835654870872920017)
  ·
    refine ⟨69446071376741153154690013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92594761835654870872920017 69446071376741153154690013)
    ·
      refine ⟨26042276766277932433008755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69446071376741153154690013 26042276766277932433008755)
      ·
        refine ⟨39063415149416898649513133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26042276766277932433008755 39063415149416898649513133)
        ·
          refine ⟨14648780681031336993567425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39063415149416898649513133 14648780681031336993567425)
          ·
            refine ⟨10986585510773502745175569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14648780681031336993567425 10986585510773502745175569)
            ·
              refine ⟨8239939133080127058881677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10986585510773502745175569 8239939133080127058881677)
              ·
                refine ⟨3089977174905047647080629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8239939133080127058881677 3089977174905047647080629)
                ·
                  refine ⟨289685360147348216913809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3089977174905047647080629 289685360147348216913809)
                  ·
                    rfl

theorem cell22_2538721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_2538721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538721 prefixEnd_2538721 := by exact prefixLift 2538721
  have htrace : WordTrace (prefixWord ++ tailWord_2538721) baseStart_2538721 baseEnd_2538721 := by
    simpa [prefixWord, tailWord_2538721, baseEnd_2538721] using wordTrace_append hprefix tailTrace_2538721
  have hstable : (prefixWord ++ tailWord_2538721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538721).length < 2 ^ (prefixWord ++ tailWord_2538721).sum := by decide
  have hdescent : baseEnd_2538721 < baseStart_2538721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538766 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_2538766 : Nat := 118140960795 + 2538766 * 2 ^ 59
def prefixEnd_2538766 : Nat := 4983230072969 + 3 ^ 40 * 2538766 * 2
def baseEnd_2538766 : Nat := 289690494953893177788763

theorem tailTrace_2538766 : CollatzResearch.WordTrace tailWord_2538766 prefixEnd_2538766 289690494953893177788763 := by
  unfold tailWord_2538766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11574550390061480444788519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61730935413661229038872101 11574550390061480444788519)
  ·
    refine ⟨17361825585092220667182779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11574550390061480444788519 17361825585092220667182779)
    ·
      refine ⟨26042738377638331000774169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17361825585092220667182779 26042738377638331000774169)
      ·
        refine ⟨19532053783228748250580627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26042738377638331000774169 19532053783228748250580627)
        ·
          refine ⟨29298080674843122375870941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19532053783228748250580627 29298080674843122375870941)
          ·
            refine ⟨10986780253066170890951603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29298080674843122375870941 10986780253066170890951603)
            ·
              refine ⟨16480170379599256336427405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10986780253066170890951603 16480170379599256336427405)
              ·
                refine ⟨6180063892349721126160277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16480170379599256336427405 6180063892349721126160277)
                ·
                  refine ⟨289690494953893177788763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6180063892349721126160277 289690494953893177788763)
                  ·
                    rfl

theorem cell22_2538766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_2538766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538766 prefixEnd_2538766 := by exact prefixLift 2538766
  have htrace : WordTrace (prefixWord ++ tailWord_2538766) baseStart_2538766 baseEnd_2538766 := by
    simpa [prefixWord, tailWord_2538766, baseEnd_2538766] using wordTrace_append hprefix tailTrace_2538766
  have hstable : (prefixWord ++ tailWord_2538766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538766).length < 2 ^ (prefixWord ++ tailWord_2538766).sum := by decide
  have hdescent : baseEnd_2538766 < baseStart_2538766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538796 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_2538796 : Nat := 118140960795 + 2538796 * 2 ^ 59
def prefixEnd_2538796 : Nat := 4983230072969 + 3 ^ 40 * 2538796 * 2
def baseEnd_2538796 : Nat := 869081754474769455116197

theorem tailTrace_2538796 : CollatzResearch.WordTrace tailWord_2538796 prefixEnd_2538796 869081754474769455116197 := by
  unfold tailWord_2538796
  simp only [CollatzResearch.WordTrace]
  refine ⟨46298748655191579340950121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61731664873588772454600161 46298748655191579340950121)
  ·
    refine ⟨34724061491393684505712591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46298748655191579340950121 34724061491393684505712591)
    ·
      refine ⟨52086092237090526758568887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34724061491393684505712591 52086092237090526758568887)
      ·
        refine ⟨78129138355635790137853331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52086092237090526758568887 78129138355635790137853331)
        ·
          refine ⟨117193707533453685206779997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78129138355635790137853331 117193707533453685206779997)
          ·
            refine ⟨43947640325045131952542499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117193707533453685206779997 43947640325045131952542499)
            ·
              refine ⟨65921460487567697928813749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43947640325045131952542499 65921460487567697928813749)
              ·
                refine ⟨6180136920709471680826289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65921460487567697928813749 6180136920709471680826289)
                ·
                  refine ⟨4635102690532103760619717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6180136920709471680826289 4635102690532103760619717)
                  ·
                    refine ⟨869081754474769455116197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4635102690532103760619717 869081754474769455116197)
                    ·
                      rfl

theorem cell22_2538796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_2538796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538796 prefixEnd_2538796 := by exact prefixLift 2538796
  have htrace : WordTrace (prefixWord ++ tailWord_2538796) baseStart_2538796 baseEnd_2538796 := by
    simpa [prefixWord, tailWord_2538796, baseEnd_2538796] using wordTrace_append hprefix tailTrace_2538796
  have hstable : (prefixWord ++ tailWord_2538796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538796).length < 2 ^ (prefixWord ++ tailWord_2538796).sum := by decide
  have hdescent : baseEnd_2538796 < baseStart_2538796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538817 : List Nat := [1, 2, 5, 2, 1, 2, 3, 2, 4]
def baseStart_2538817 : Nat := 118140960795 + 2538817 * 2 ^ 59
def prefixEnd_2538817 : Nat := 4983230072969 + 3 ^ 40 * 2538817 * 2
def baseEnd_2538817 : Nat := 289696314401310800113711

theorem tailTrace_2538817 : CollatzResearch.WordTrace tailWord_2538817 prefixEnd_2538817 289696314401310800113711 := by
  unfold tailWord_2538817
  simp only [CollatzResearch.WordTrace]
  refine ⟨92598263243307079268414705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61732175495538052845609803 92598263243307079268414705)
  ·
    refine ⟨69448697432480309451311029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92598263243307079268414705 69448697432480309451311029)
    ·
      refine ⟨6510815384295029011060409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69448697432480309451311029 6510815384295029011060409)
      ·
        refine ⟨4883111538221271758295307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6510815384295029011060409 4883111538221271758295307)
        ·
          refine ⟨7324667307331907637442961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883111538221271758295307 7324667307331907637442961)
          ·
            refine ⟨5493500480498930728082221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7324667307331907637442961 5493500480498930728082221)
            ·
              refine ⟨2060062680187099023030833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5493500480498930728082221 2060062680187099023030833)
              ·
                refine ⟨1545047010140324267273125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2060062680187099023030833 1545047010140324267273125)
                ·
                  refine ⟨289696314401310800113711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1545047010140324267273125 289696314401310800113711)
                  ·
                    rfl

theorem cell22_2538817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 4].length) (baseStart_2538817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538817 prefixEnd_2538817 := by exact prefixLift 2538817
  have htrace : WordTrace (prefixWord ++ tailWord_2538817) baseStart_2538817 baseEnd_2538817 := by
    simpa [prefixWord, tailWord_2538817, baseEnd_2538817] using wordTrace_append hprefix tailTrace_2538817
  have hstable : (prefixWord ++ tailWord_2538817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538817).length < 2 ^ (prefixWord ++ tailWord_2538817).sum := by decide
  have hdescent : baseEnd_2538817 < baseStart_2538817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538871 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 2, 5]
def baseStart_2538871 : Nat := 118140960795 + 2538871 * 2 ^ 59
def prefixEnd_2538871 : Nat := 4983230072969 + 3 ^ 40 * 2538871 * 2
def baseEnd_2538871 : Nat := 869107428507494259490967

theorem tailTrace_2538871 : CollatzResearch.WordTrace tailWord_2538871 prefixEnd_2538871 869107428507494259490967 := by
  unfold tailWord_2538871
  simp only [CollatzResearch.WordTrace]
  refine ⟨92600232785111446490880467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61733488523407630993920311 92600232785111446490880467)
  ·
    refine ⟨138900349177667169736320701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92600232785111446490880467 138900349177667169736320701)
    ·
      refine ⟨52087630941625188651120263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138900349177667169736320701 52087630941625188651120263)
      ·
        refine ⟨78131446412437782976680395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52087630941625188651120263 78131446412437782976680395)
        ·
          refine ⟨117197169618656674465020593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78131446412437782976680395 117197169618656674465020593)
          ·
            refine ⟨87897877213992505848765445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117197169618656674465020593 87897877213992505848765445)
            ·
              refine ⟨16480851977623594846643521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87897877213992505848765445 16480851977623594846643521)
              ·
                refine ⟨12360638983217696134982641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16480851977623594846643521 12360638983217696134982641)
                ·
                  refine ⟨9270479237413272101236981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12360638983217696134982641 9270479237413272101236981)
                  ·
                    refine ⟨869107428507494259490967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9270479237413272101236981 869107428507494259490967)
                    ·
                      rfl

theorem cell22_2538871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_2538871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538871 prefixEnd_2538871 := by exact prefixLift 2538871
  have htrace : WordTrace (prefixWord ++ tailWord_2538871) baseStart_2538871 baseEnd_2538871 := by
    simpa [prefixWord, tailWord_2538871, baseEnd_2538871] using wordTrace_append hprefix tailTrace_2538871
  have hstable : (prefixWord ++ tailWord_2538871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538871).length < 2 ^ (prefixWord ++ tailWord_2538871).sum := by decide
  have hdescent : baseEnd_2538871 < baseStart_2538871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538888 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_2538888 : Nat := 118140960795 + 2538888 * 2 ^ 59
def prefixEnd_2538888 : Nat := 4983230072969 + 3 ^ 40 * 2538888 * 2
def baseEnd_2538888 : Nat := 869113247954911881815915

theorem tailTrace_2538888 : CollatzResearch.WordTrace tailWord_2538888 prefixEnd_2538888 869113247954911881815915 := by
  unfold tailWord_2538888
  simp only [CollatzResearch.WordTrace]
  refine ⟨46300426413024929197124659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61733901884033238929499545 46300426413024929197124659)
  ·
    refine ⟨69450639619537393795686989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46300426413024929197124659 69450639619537393795686989)
    ·
      refine ⟨26043989857326522673382621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69450639619537393795686989 26043989857326522673382621)
      ·
        refine ⟨9766496196497446002518483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26043989857326522673382621 9766496196497446002518483)
        ·
          refine ⟨14649744294746169003777725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9766496196497446002518483 14649744294746169003777725)
          ·
            refine ⟨5493654110529813376416647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14649744294746169003777725 5493654110529813376416647)
            ·
              refine ⟨8240481165794720064624971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5493654110529813376416647 8240481165794720064624971)
              ·
                refine ⟨12360721748692080096937457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8240481165794720064624971 12360721748692080096937457)
                ·
                  refine ⟨9270541311519060072703093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12360721748692080096937457 9270541311519060072703093)
                  ·
                    refine ⟨869113247954911881815915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9270541311519060072703093 869113247954911881815915)
                    ·
                      rfl

theorem cell22_2538888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_2538888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538888 prefixEnd_2538888 := by exact prefixLift 2538888
  have htrace : WordTrace (prefixWord ++ tailWord_2538888) baseStart_2538888 baseEnd_2538888 := by
    simpa [prefixWord, tailWord_2538888, baseEnd_2538888] using wordTrace_append hprefix tailTrace_2538888
  have hstable : (prefixWord ++ tailWord_2538888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538888).length < 2 ^ (prefixWord ++ tailWord_2538888).sum := by decide
  have hdescent : baseEnd_2538888 < baseStart_2538888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538901 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 8]
def baseStart_2538901 : Nat := 118140960795 + 2538901 * 2 ^ 59
def prefixEnd_2538901 : Nat := 4983230072969 + 3 ^ 40 * 2538901 * 2
def baseEnd_2538901 : Nat := 289705899373528060413625

theorem tailTrace_2538901 : CollatzResearch.WordTrace tailWord_2538901 prefixEnd_2538901 289705899373528060413625 := by
  unfold tailWord_2538901
  simp only [CollatzResearch.WordTrace]
  refine ⟨92601326975002761614472557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61734217983335174409648371 92601326975002761614472557)
  ·
    refine ⟨34725497615626035605427209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92601326975002761614472557 34725497615626035605427209)
    ·
      refine ⟨26044123211719526704070407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34725497615626035605427209 26044123211719526704070407)
      ·
        refine ⟨39066184817579290056105611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26044123211719526704070407 39066184817579290056105611)
        ·
          refine ⟨58599277226368935084158417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39066184817579290056105611 58599277226368935084158417)
          ·
            refine ⟨43949457919776701313118813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58599277226368935084158417 43949457919776701313118813)
            ·
              refine ⟨16481046719916262992419555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43949457919776701313118813 16481046719916262992419555)
              ·
                refine ⟨24721570079874394488629333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16481046719916262992419555 24721570079874394488629333)
                ·
                  refine ⟨289705899373528060413625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24721570079874394488629333 289705899373528060413625)
                  ·
                    rfl

theorem cell22_2538901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_2538901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538901 prefixEnd_2538901 := by exact prefixLift 2538901
  have htrace : WordTrace (prefixWord ++ tailWord_2538901) baseStart_2538901 baseEnd_2538901 := by
    simpa [prefixWord, tailWord_2538901, baseEnd_2538901] using wordTrace_append hprefix tailTrace_2538901
  have hstable : (prefixWord ++ tailWord_2538901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538901).length < 2 ^ (prefixWord ++ tailWord_2538901).sum := by decide
  have hdescent : baseEnd_2538901 < baseStart_2538901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538903 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 1, 4]
def baseStart_2538903 : Nat := 118140960795 + 2538903 * 2 ^ 59
def prefixEnd_2538903 : Nat := 4983230072969 + 3 ^ 40 * 2538903 * 2
def baseEnd_2538903 : Nat := 869118382761456842690869

theorem tailTrace_2538903 : CollatzResearch.WordTrace tailWord_2538903 prefixEnd_2538903 869118382761456842690869 := by
  unfold tailWord_2538903
  simp only [CollatzResearch.WordTrace]
  refine ⟨92601399920995515956045363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61734266613997010637363575 92601399920995515956045363)
  ·
    refine ⟨138902099881493273934068045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92601399920995515956045363 138902099881493273934068045)
    ·
      refine ⟨52088287455559977725275517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138902099881493273934068045 52088287455559977725275517)
      ·
        refine ⟨19533107795834991646978319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52088287455559977725275517 19533107795834991646978319)
        ·
          refine ⟨29299661693752487470467479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19533107795834991646978319 29299661693752487470467479)
          ·
            refine ⟨43949492540628731205701219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29299661693752487470467479 43949492540628731205701219)
            ·
              refine ⟨65924238810943096808551829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43949492540628731205701219 65924238810943096808551829)
              ·
                refine ⟨3090198694262957662900867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65924238810943096808551829 3090198694262957662900867)
                ·
                  refine ⟨4635298041394436494351301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090198694262957662900867 4635298041394436494351301)
                  ·
                    refine ⟨869118382761456842690869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4635298041394436494351301 869118382761456842690869)
                    ·
                      rfl

theorem cell22_2538903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_2538903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2538903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2538903 prefixEnd_2538903 := by exact prefixLift 2538903
  have htrace : WordTrace (prefixWord ++ tailWord_2538903) baseStart_2538903 baseEnd_2538903 := by
    simpa [prefixWord, tailWord_2538903, baseEnd_2538903] using wordTrace_append hprefix tailTrace_2538903
  have hstable : (prefixWord ++ tailWord_2538903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538903).length < 2 ^ (prefixWord ++ tailWord_2538903).sum := by decide
  have hdescent : baseEnd_2538903 < baseStart_2538903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539130 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 5, 3]
def baseStart_2539130 : Nat := 118140960795 + 2539130 * 2 ^ 59
def prefixEnd_2539130 : Nat := 4983230072969 + 3 ^ 40 * 2539130 * 2
def baseEnd_2539130 : Nat := 869196089500503917265173

theorem tailTrace_2539130 : CollatzResearch.WordTrace tailWord_2539130 prefixEnd_2539130 869196089500503917265173 := by
  unfold tailWord_2539130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23152419822793283431139711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61739786194115422483039229 23152419822793283431139711)
  ·
    refine ⟨34728629734189925146709567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23152419822793283431139711 34728629734189925146709567)
    ·
      refine ⟨52092944601284887720064351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34728629734189925146709567 52092944601284887720064351)
      ·
        refine ⟨78139416901927331580096527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52092944601284887720064351 78139416901927331580096527)
        ·
          refine ⟨117209125352890997370144791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78139416901927331580096527 117209125352890997370144791)
          ·
            refine ⟨175813688029336496055217187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117209125352890997370144791 175813688029336496055217187)
            ·
              refine ⟨263720532044004744082825781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175813688029336496055217187 263720532044004744082825781)
              ·
                refine ⟨24723799879125444757764917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 263720532044004744082825781 24723799879125444757764917)
                ·
                  refine ⟨2317856238668010446040461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24723799879125444757764917 2317856238668010446040461)
                  ·
                    refine ⟨869196089500503917265173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2317856238668010446040461 869196089500503917265173)
                    ·
                      rfl

theorem cell22_2539130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_2539130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539130 prefixEnd_2539130 := by exact prefixLift 2539130
  have htrace : WordTrace (prefixWord ++ tailWord_2539130) baseStart_2539130 baseEnd_2539130 := by
    simpa [prefixWord, tailWord_2539130, baseEnd_2539130] using wordTrace_append hprefix tailTrace_2539130
  have hstable : (prefixWord ++ tailWord_2539130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539130).length < 2 ^ (prefixWord ++ tailWord_2539130).sum := by decide
  have hdescent : baseEnd_2539130 < baseStart_2539130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539160 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 7]
def baseStart_2539160 : Nat := 118140960795 + 2539160 * 2 ^ 59
def prefixEnd_2539160 : Nat := 4983230072969 + 3 ^ 40 * 2539160 * 2
def baseEnd_2539160 : Nat := 289735453037864613005027

theorem tailTrace_2539160 : CollatzResearch.WordTrace tailWord_2539160 prefixEnd_2539160 289735453037864613005027 := by
  unfold tailWord_2539160
  simp only [CollatzResearch.WordTrace]
  refine ⟨46305386740532224424075467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61740515654042965898767289 46305386740532224424075467)
  ·
    refine ⟨69458080110798336636113201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46305386740532224424075467 69458080110798336636113201)
    ·
      refine ⟨52093560083098752477084901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69458080110798336636113201 52093560083098752477084901)
      ·
        refine ⟨9767542515581016089453419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52093560083098752477084901 9767542515581016089453419)
        ·
          refine ⟨14651313773371524134180129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9767542515581016089453419 14651313773371524134180129)
          ·
            refine ⟨10988485330028643100635097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14651313773371524134180129 10988485330028643100635097)
            ·
              refine ⟨8241363997521482325476323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10988485330028643100635097 8241363997521482325476323)
              ·
                refine ⟨12362045996282223488214485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8241363997521482325476323 12362045996282223488214485)
                ·
                  refine ⟨289735453037864613005027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12362045996282223488214485 289735453037864613005027)
                  ·
                    rfl

theorem cell22_2539160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_2539160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539160 prefixEnd_2539160 := by exact prefixLift 2539160
  have htrace : WordTrace (prefixWord ++ tailWord_2539160) baseStart_2539160 baseEnd_2539160 := by
    simpa [prefixWord, tailWord_2539160, baseEnd_2539160] using wordTrace_append hprefix tailTrace_2539160
  have hstable : (prefixWord ++ tailWord_2539160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539160).length < 2 ^ (prefixWord ++ tailWord_2539160).sum := by decide
  have hdescent : baseEnd_2539160 < baseStart_2539160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539170 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_2539170 : Nat := 118140960795 + 2539170 * 2 ^ 59
def prefixEnd_2539170 : Nat := 4983230072969 + 3 ^ 40 * 2539170 * 2
def baseEnd_2539170 : Nat := 869209782317957146265051

theorem tailTrace_2539170 : CollatzResearch.WordTrace tailWord_2539170 prefixEnd_2539170 869209782317957146265051 := by
  unfold tailWord_2539170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23152784552757055139003741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61740758807352147037343309 23152784552757055139003741)
  ·
    refine ⟨8682294207283895677126403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23152784552757055139003741 8682294207283895677126403)
    ·
      refine ⟨13023441310925843515689605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8682294207283895677126403 13023441310925843515689605)
      ·
        refine ⟨2441895245798595659191801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13023441310925843515689605 2441895245798595659191801)
        ·
          refine ⟨1831421434348946744393851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2441895245798595659191801 1831421434348946744393851)
          ·
            refine ⟨2747132151523420116590777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831421434348946744393851 2747132151523420116590777)
            ·
              refine ⟨2060349113642565087443083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2747132151523420116590777 2060349113642565087443083)
              ·
                refine ⟨3090523670463847631164625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060349113642565087443083 3090523670463847631164625)
                ·
                  refine ⟨2317892752847885723373469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3090523670463847631164625 2317892752847885723373469)
                  ·
                    refine ⟨869209782317957146265051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2317892752847885723373469 869209782317957146265051)
                    ·
                      rfl

theorem cell22_2539170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_2539170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539170 prefixEnd_2539170 := by exact prefixLift 2539170
  have htrace : WordTrace (prefixWord ++ tailWord_2539170) baseStart_2539170 baseEnd_2539170 := by
    simpa [prefixWord, tailWord_2539170, baseEnd_2539170] using wordTrace_append hprefix tailTrace_2539170
  have hstable : (prefixWord ++ tailWord_2539170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539170).length < 2 ^ (prefixWord ++ tailWord_2539170).sum := by decide
  have hdescent : baseEnd_2539170 < baseStart_2539170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539237 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_2539237 : Nat := 118140960795 + 2539237 * 2 ^ 59
def prefixEnd_2539237 : Nat := 4983230072969 + 3 ^ 40 * 2539237 * 2
def baseEnd_2539237 : Nat := 869232717787191304839845

theorem tailTrace_2539237 : CollatzResearch.WordTrace tailWord_2539237 prefixEnd_2539237 869232717787191304839845 := by
  unfold tailWord_2539237
  simp only [CollatzResearch.WordTrace]
  refine ⟨92613581901785490998703965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61742387934523660665802643 92613581901785490998703965)
  ·
    refine ⟨34730093213169559124513987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92613581901785490998703965 34730093213169559124513987)
    ·
      refine ⟨52095139819754338686770981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34730093213169559124513987 52095139819754338686770981)
      ·
        refine ⟨9767838716203938503769559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52095139819754338686770981 9767838716203938503769559)
        ·
          refine ⟨14651758074305907755654339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9767838716203938503769559 14651758074305907755654339)
          ·
            refine ⟨21977637111458861633481509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14651758074305907755654339 21977637111458861633481509)
            ·
              refine ⟨4120806958398536556277783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21977637111458861633481509 4120806958398536556277783)
              ·
                refine ⟨6181210437597804834416675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120806958398536556277783 6181210437597804834416675)
                ·
                  refine ⟨9271815656396707251625013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181210437597804834416675 9271815656396707251625013)
                  ·
                    refine ⟨869232717787191304839845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9271815656396707251625013 869232717787191304839845)
                    ·
                      rfl

theorem cell22_2539237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_2539237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539237 prefixEnd_2539237 := by exact prefixLift 2539237
  have htrace : WordTrace (prefixWord ++ tailWord_2539237) baseStart_2539237 baseEnd_2539237 := by
    simpa [prefixWord, tailWord_2539237, baseEnd_2539237] using wordTrace_append hprefix tailTrace_2539237
  have hstable : (prefixWord ++ tailWord_2539237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539237).length < 2 ^ (prefixWord ++ tailWord_2539237).sum := by decide
  have hdescent : baseEnd_2539237 < baseStart_2539237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539239 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 6]
def baseStart_2539239 : Nat := 118140960795 + 2539239 * 2 ^ 59
def prefixEnd_2539239 : Nat := 4983230072969 + 3 ^ 40 * 2539239 * 2
def baseEnd_2539239 : Nat := 289744467476021322096613

theorem tailTrace_2539239 : CollatzResearch.WordTrace tailWord_2539239 prefixEnd_2539239 289744467476021322096613 := by
  unfold tailWord_2539239
  simp only [CollatzResearch.WordTrace]
  refine ⟨92613654847778245340276771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61742436565185496893517847 92613654847778245340276771)
  ·
    refine ⟨138920482271667368010415157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92613654847778245340276771 138920482271667368010415157)
    ·
      refine ⟨13023795212968815750976421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138920482271667368010415157 13023795212968815750976421)
      ·
        refine ⟨2441961602431652953308079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13023795212968815750976421 2441961602431652953308079)
        ·
          refine ⟨3662942403647479429962119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441961602431652953308079 3662942403647479429962119)
          ·
            refine ⟨5494413605471219144943179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3662942403647479429962119 5494413605471219144943179)
            ·
              refine ⟨8241620408206828717414769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5494413605471219144943179 8241620408206828717414769)
              ·
                refine ⟨6181215306155121538061077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8241620408206828717414769 6181215306155121538061077)
                ·
                  refine ⟨289744467476021322096613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6181215306155121538061077 289744467476021322096613)
                  ·
                    rfl

theorem cell22_2539239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 6].length) (baseStart_2539239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539239 prefixEnd_2539239 := by exact prefixLift 2539239
  have htrace : WordTrace (prefixWord ++ tailWord_2539239) baseStart_2539239 baseEnd_2539239 := by
    simpa [prefixWord, tailWord_2539239, baseEnd_2539239] using wordTrace_append hprefix tailTrace_2539239
  have hstable : (prefixWord ++ tailWord_2539239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539239).length < 2 ^ (prefixWord ++ tailWord_2539239).sum := by decide
  have hdescent : baseEnd_2539239 < baseStart_2539239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539346 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_2539346 : Nat := 118140960795 + 2539346 * 2 ^ 59
def prefixEnd_2539346 : Nat := 4983230072969 + 3 ^ 40 * 2539346 * 2
def baseEnd_2539346 : Nat := 289756676904917117954837

theorem tailTrace_2539346 : CollatzResearch.WordTrace tailWord_2539346 prefixEnd_2539346 289756676904917117954837 := by
  unfold tailWord_2539346
  simp only [CollatzResearch.WordTrace]
  refine ⟨23154389364597650653605473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61745038305593735076281261 23154389364597650653605473)
  ·
    refine ⟨17365792023448237990204105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23154389364597650653605473 17365792023448237990204105)
    ·
      refine ⟨13024344017586178492653079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17365792023448237990204105 13024344017586178492653079)
      ·
        refine ⟨19536516026379267738979619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13024344017586178492653079 19536516026379267738979619)
        ·
          refine ⟨29304774039568901608469429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19536516026379267738979619 29304774039568901608469429)
          ·
            refine ⟨2747322566209584525794009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29304774039568901608469429 2747322566209584525794009)
            ·
              refine ⟨2060491924657188394345507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2747322566209584525794009 2060491924657188394345507)
              ·
                refine ⟨3090737886985782591518261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060491924657188394345507 3090737886985782591518261)
                ·
                  refine ⟨289756676904917117954837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3090737886985782591518261 289756676904917117954837)
                  ·
                    rfl

theorem cell22_2539346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_2539346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539346 prefixEnd_2539346 := by exact prefixLift 2539346
  have htrace : WordTrace (prefixWord ++ tailWord_2539346) baseStart_2539346 baseEnd_2539346 := by
    simpa [prefixWord, tailWord_2539346, baseEnd_2539346] using wordTrace_append hprefix tailTrace_2539346
  have hstable : (prefixWord ++ tailWord_2539346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539346).length < 2 ^ (prefixWord ++ tailWord_2539346).sum := by decide
  have hdescent : baseEnd_2539346 < baseStart_2539346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539355 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]
def baseStart_2539355 : Nat := 118140960795 + 2539355 * 2 ^ 59
def prefixEnd_2539355 : Nat := 4983230072969 + 3 ^ 40 * 2539355 * 2
def baseEnd_2539355 : Nat := 869273111598678330389483

theorem tailTrace_2539355 : CollatzResearch.WordTrace tailWord_2539355 prefixEnd_2539355 869273111598678330389483 := by
  unfold tailWord_2539355
  simp only [CollatzResearch.WordTrace]
  refine ⟨92617885715357997151499519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61745257143571998100999679 92617885715357997151499519)
  ·
    refine ⟨138926828573036995727249279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92617885715357997151499519 138926828573036995727249279)
    ·
      refine ⟨208390242859555493590873919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138926828573036995727249279 208390242859555493590873919)
      ·
        refine ⟨312585364289333240386310879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208390242859555493590873919 312585364289333240386310879)
        ·
          refine ⟨468878046433999860579466319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312585364289333240386310879 468878046433999860579466319)
          ·
            refine ⟨703317069650999790869199479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468878046433999860579466319 703317069650999790869199479)
            ·
              refine ⟨1054975604476499686303799219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703317069650999790869199479 1054975604476499686303799219)
              ·
                refine ⟨1582463406714749529455698829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054975604476499686303799219 1582463406714749529455698829)
                ·
                  refine ⟨593423777518031073545887061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1582463406714749529455698829 593423777518031073545887061)
                  ·
                    refine ⟨869273111598678330389483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 593423777518031073545887061 869273111598678330389483)
                    ·
                      rfl

theorem cell22_2539355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_2539355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539355 prefixEnd_2539355 := by exact prefixLift 2539355
  have htrace : WordTrace (prefixWord ++ tailWord_2539355) baseStart_2539355 baseEnd_2539355 := by
    simpa [prefixWord, tailWord_2539355, baseEnd_2539355] using wordTrace_append hprefix tailTrace_2539355
  have hstable : (prefixWord ++ tailWord_2539355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539355).length < 2 ^ (prefixWord ++ tailWord_2539355).sum := by decide
  have hdescent : baseEnd_2539355 < baseStart_2539355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539359 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 1, 4]
def baseStart_2539359 : Nat := 118140960795 + 2539359 * 2 ^ 59
def prefixEnd_2539359 : Nat := 4983230072969 + 3 ^ 40 * 2539359 * 2
def baseEnd_2539359 : Nat := 869274480880423653289471

theorem tailTrace_2539359 : CollatzResearch.WordTrace tailWord_2539359 prefixEnd_2539359 869274480880423653289471 := by
  unfold tailWord_2539359
  simp only [CollatzResearch.WordTrace]
  refine ⟨92618031607343505834645131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61745354404895670556430087 92618031607343505834645131)
  ·
    refine ⟨138927047411015258751967697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92618031607343505834645131 138927047411015258751967697)
    ·
      refine ⟨104195285558261444063975773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138927047411015258751967697 104195285558261444063975773)
      ·
        refine ⟨39073232084348041523990915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104195285558261444063975773 39073232084348041523990915)
        ·
          refine ⟨58609848126522062285986373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39073232084348041523990915 58609848126522062285986373)
          ·
            refine ⟨10989346523722886678622445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58609848126522062285986373 10989346523722886678622445)
            ·
              refine ⟨4121004946396082504483417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10989346523722886678622445 4121004946396082504483417)
              ·
                refine ⟨3090753709797061878362563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4121004946396082504483417 3090753709797061878362563)
                ·
                  refine ⟨4636130564695592817543845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090753709797061878362563 4636130564695592817543845)
                  ·
                    refine ⟨869274480880423653289471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4636130564695592817543845 869274480880423653289471)
                    ·
                      rfl

theorem cell22_2539359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_2539359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539359 prefixEnd_2539359 := by exact prefixLift 2539359
  have htrace : WordTrace (prefixWord ++ tailWord_2539359) baseStart_2539359 baseEnd_2539359 := by
    simpa [prefixWord, tailWord_2539359, baseEnd_2539359] using wordTrace_append hprefix tailTrace_2539359
  have hstable : (prefixWord ++ tailWord_2539359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539359).length < 2 ^ (prefixWord ++ tailWord_2539359).sum := by decide
  have hdescent : baseEnd_2539359 < baseStart_2539359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539372 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_2539372 : Nat := 118140960795 + 2539372 * 2 ^ 59
def prefixEnd_2539372 : Nat := 4983230072969 + 3 ^ 40 * 2539372 * 2
def baseEnd_2539372 : Nat := 869278931046095952714431

theorem tailTrace_2539372 : CollatzResearch.WordTrace tailWord_2539372 prefixEnd_2539372 869278931046095952714431 := by
  unfold tailWord_2539372
  simp only [CollatzResearch.WordTrace]
  refine ⟨46309252878148204527434185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61745670504197606036578913 46309252878148204527434185)
  ·
    refine ⟨34731939658611153395575639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46309252878148204527434185 34731939658611153395575639)
    ·
      refine ⟨52097909487916730093363459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34731939658611153395575639 52097909487916730093363459)
      ·
        refine ⟨78146864231875095140045189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52097909487916730093363459 78146864231875095140045189)
        ·
          refine ⟨14652537043476580338758473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78146864231875095140045189 14652537043476580338758473)
          ·
            refine ⟨10989402782607435254068855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14652537043476580338758473 10989402782607435254068855)
            ·
              refine ⟨16484104173911152881103283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10989402782607435254068855 16484104173911152881103283)
              ·
                refine ⟨24726156260866729321654925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16484104173911152881103283 24726156260866729321654925)
                ·
                  refine ⟨9272308597825023495620597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24726156260866729321654925 9272308597825023495620597)
                  ·
                    refine ⟨869278931046095952714431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9272308597825023495620597 869278931046095952714431)
                    ·
                      rfl

theorem cell22_2539372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_2539372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539372 prefixEnd_2539372 := by exact prefixLift 2539372
  have htrace : WordTrace (prefixWord ++ tailWord_2539372) baseStart_2539372 baseEnd_2539372 := by
    simpa [prefixWord, tailWord_2539372, baseEnd_2539372] using wordTrace_append hprefix tailTrace_2539372
  have hstable : (prefixWord ++ tailWord_2539372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539372).length < 2 ^ (prefixWord ++ tailWord_2539372).sum := by decide
  have hdescent : baseEnd_2539372 < baseStart_2539372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539421 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_2539421 : Nat := 118140960795 + 2539421 * 2 ^ 59
def prefixEnd_2539421 : Nat := 4983230072969 + 3 ^ 40 * 2539421 * 2
def baseEnd_2539421 : Nat := 869295704747476158239281

theorem tailTrace_2539421 : CollatzResearch.WordTrace tailWord_2539421 prefixEnd_2539421 869295704747476158239281 := by
  unfold tailWord_2539421
  simp only [CollatzResearch.WordTrace]
  refine ⟨92620292933118890423402117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61746861955412593615601411 92620292933118890423402117)
  ·
    refine ⟨17366304924959791954387897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92620292933118890423402117 17366304924959791954387897)
    ·
      refine ⟨13024728693719843965790923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17366304924959791954387897 13024728693719843965790923)
      ·
        refine ⟨19537093040579765948686385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13024728693719843965790923 19537093040579765948686385)
        ·
          refine ⟨14652819780434824461514789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19537093040579765948686385 14652819780434824461514789)
          ·
            refine ⟨2747403708831529586534023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14652819780434824461514789 2747403708831529586534023)
            ·
              refine ⟨4121105563247294379801035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747403708831529586534023 4121105563247294379801035)
              ·
                refine ⟨6181658344870941569701553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121105563247294379801035 6181658344870941569701553)
                ·
                  refine ⟨4636243758653206177276165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6181658344870941569701553 4636243758653206177276165)
                  ·
                    refine ⟨869295704747476158239281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4636243758653206177276165 869295704747476158239281)
                    ·
                      rfl

theorem cell22_2539421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_2539421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539421 prefixEnd_2539421 := by exact prefixLift 2539421
  have htrace : WordTrace (prefixWord ++ tailWord_2539421) baseStart_2539421 baseEnd_2539421 := by
    simpa [prefixWord, tailWord_2539421, baseEnd_2539421] using wordTrace_append hprefix tailTrace_2539421
  have hstable : (prefixWord ++ tailWord_2539421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539421).length < 2 ^ (prefixWord ++ tailWord_2539421).sum := by decide
  have hdescent : baseEnd_2539421 < baseStart_2539421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539539 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 2, 4]
def baseStart_2539539 : Nat := 118140960795 + 2539539 * 2 ^ 59
def prefixEnd_2539539 : Nat := 4983230072969 + 3 ^ 40 * 2539539 * 2
def baseEnd_2539539 : Nat := 869336098558963183788919

theorem tailTrace_2539539 : CollatzResearch.WordTrace tailWord_2539539 prefixEnd_2539539 869336098558963183788919 := by
  unfold tailWord_2539539
  simp only [CollatzResearch.WordTrace]
  refine ⟨92624596746691396576197671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61749731164460931050798447 92624596746691396576197671)
  ·
    refine ⟨138936895120037094864296507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92624596746691396576197671 138936895120037094864296507)
    ·
      refine ⟨208405342680055642296444761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138936895120037094864296507 208405342680055642296444761)
      ·
        refine ⟨156304007010041731722333571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208405342680055642296444761 156304007010041731722333571)
        ·
          refine ⟨234456010515062597583500357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156304007010041731722333571 234456010515062597583500357)
          ·
            refine ⟨43960501971574237046906317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234456010515062597583500357 43960501971574237046906317)
            ·
              refine ⟨16485188239340338892589869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43960501971574237046906317 16485188239340338892589869)
              ·
                refine ⟨6181945589752627084721201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16485188239340338892589869 6181945589752627084721201)
                ·
                  refine ⟨4636459192314470313540901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6181945589752627084721201 4636459192314470313540901)
                  ·
                    refine ⟨869336098558963183788919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4636459192314470313540901 869336098558963183788919)
                    ·
                      rfl

theorem cell22_2539539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 4].length) (baseStart_2539539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539539 prefixEnd_2539539 := by exact prefixLift 2539539
  have htrace : WordTrace (prefixWord ++ tailWord_2539539) baseStart_2539539 baseEnd_2539539 := by
    simpa [prefixWord, tailWord_2539539, baseEnd_2539539] using wordTrace_append hprefix tailTrace_2539539
  have hstable : (prefixWord ++ tailWord_2539539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539539).length < 2 ^ (prefixWord ++ tailWord_2539539).sum := by decide
  have hdescent : baseEnd_2539539 < baseStart_2539539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539541 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2539541 : Nat := 118140960795 + 2539541 * 2 ^ 59
def prefixEnd_2539541 : Nat := 4983230072969 + 3 ^ 40 * 2539541 * 2
def baseEnd_2539541 : Nat := 869336783199835845238913

theorem tailTrace_2539541 : CollatzResearch.WordTrace tailWord_2539541 prefixEnd_2539541 869336783199835845238913 := by
  unfold tailWord_2539541
  simp only [CollatzResearch.WordTrace]
  refine ⟨92624669692684150917770477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61749779795122767278513651 92624669692684150917770477)
  ·
    refine ⟨34734251134756556594163929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92624669692684150917770477 34734251134756556594163929)
    ·
      refine ⟨26050688351067417445622947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34734251134756556594163929 26050688351067417445622947)
      ·
        refine ⟨39076032526601126168434421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26050688351067417445622947 39076032526601126168434421)
        ·
          refine ⟨3663378049368855578290727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39076032526601126168434421 3663378049368855578290727)
          ·
            refine ⟨5495067074053283367436091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663378049368855578290727 5495067074053283367436091)
            ·
              refine ⟨8242600611079925051154137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5495067074053283367436091 8242600611079925051154137)
              ·
                refine ⟨6181950458309943788365603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8242600611079925051154137 6181950458309943788365603)
                ·
                  refine ⟨9272925687464915682548405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181950458309943788365603 9272925687464915682548405)
                  ·
                    refine ⟨869336783199835845238913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9272925687464915682548405 869336783199835845238913)
                    ·
                      rfl

theorem cell22_2539541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2539541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539541 prefixEnd_2539541 := by exact prefixLift 2539541
  have htrace : WordTrace (prefixWord ++ tailWord_2539541) baseStart_2539541 baseEnd_2539541 := by
    simpa [prefixWord, tailWord_2539541, baseEnd_2539541] using wordTrace_append hprefix tailTrace_2539541
  have hstable : (prefixWord ++ tailWord_2539541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539541).length < 2 ^ (prefixWord ++ tailWord_2539541).sum := by decide
  have hdescent : baseEnd_2539541 < baseStart_2539541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539560 : List Nat := [2, 1, 5, 3, 1, 1, 1, 4, 4]
def baseStart_2539560 : Nat := 118140960795 + 2539560 * 2 ^ 59
def prefixEnd_2539560 : Nat := 4983230072969 + 3 ^ 40 * 2539560 * 2
def baseEnd_2539560 : Nat := 289781095762708709671285

theorem tailTrace_2539560 : CollatzResearch.WordTrace tailWord_2539560 prefixEnd_2539560 289781095762708709671285 := by
  unfold tailWord_2539560
  simp only [CollatzResearch.WordTrace]
  refine ⟨46312681339807658581356067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61750241786410211441808089 46312681339807658581356067)
  ·
    refine ⟨69469022009711487872034101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46312681339807658581356067 69469022009711487872034101)
    ·
      refine ⟨6512720813410451988003197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69469022009711487872034101 6512720813410451988003197)
      ·
        refine ⟨2442270305028919495501199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6512720813410451988003197 2442270305028919495501199)
        ·
          refine ⟨3663405457543379243251799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442270305028919495501199 3663405457543379243251799)
          ·
            refine ⟨5495108186315068864877699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663405457543379243251799 5495108186315068864877699)
            ·
              refine ⟨8242662279472603297316549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5495108186315068864877699 8242662279472603297316549)
              ·
                refine ⟨1545499177401113118246853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8242662279472603297316549 1545499177401113118246853)
                ·
                  refine ⟨289781095762708709671285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1545499177401113118246853 289781095762708709671285)
                  ·
                    rfl

theorem cell22_2539560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 4].length) (baseStart_2539560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539560 prefixEnd_2539560 := by exact prefixLift 2539560
  have htrace : WordTrace (prefixWord ++ tailWord_2539560) baseStart_2539560 baseEnd_2539560 := by
    simpa [prefixWord, tailWord_2539560, baseEnd_2539560] using wordTrace_append hprefix tailTrace_2539560
  have hstable : (prefixWord ++ tailWord_2539560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539560).length < 2 ^ (prefixWord ++ tailWord_2539560).sum := by decide
  have hdescent : baseEnd_2539560 < baseStart_2539560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539616 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 5]
def baseStart_2539616 : Nat := 118140960795 + 2539616 * 2 ^ 59
def prefixEnd_2539616 : Nat := 4983230072969 + 3 ^ 40 * 2539616 * 2
def baseEnd_2539616 : Nat := 289787485744186883204561

theorem tailTrace_2539616 : CollatzResearch.WordTrace tailWord_2539616 prefixEnd_2539616 289787485744186883204561 := by
  unfold tailWord_2539616
  simp only [CollatzResearch.WordTrace]
  refine ⟨46313702583706219363375351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61751603444941625817833801 46313702583706219363375351)
  ·
    refine ⟨69470553875559329045063027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46313702583706219363375351 69470553875559329045063027)
    ·
      refine ⟨104205830813338993567594541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69470553875559329045063027 104205830813338993567594541)
      ·
        refine ⟨39077186555002122587847953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104205830813338993567594541 39077186555002122587847953)
        ·
          refine ⟨29307889916251591940885965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39077186555002122587847953 29307889916251591940885965)
          ·
            refine ⟨10990458718594346977832237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29307889916251591940885965 10990458718594346977832237)
            ·
              refine ⟨4121422019472880116687089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10990458718594346977832237 4121422019472880116687089)
              ·
                refine ⟨3091066514604660087515317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4121422019472880116687089 3091066514604660087515317)
                ·
                  refine ⟨289787485744186883204561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3091066514604660087515317 289787485744186883204561)
                  ·
                    rfl

theorem cell22_2539616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_2539616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539616 prefixEnd_2539616 := by exact prefixLift 2539616
  have htrace : WordTrace (prefixWord ++ tailWord_2539616) baseStart_2539616 baseEnd_2539616 := by
    simpa [prefixWord, tailWord_2539616, baseEnd_2539616] using wordTrace_append hprefix tailTrace_2539616
  have hstable : (prefixWord ++ tailWord_2539616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539616).length < 2 ^ (prefixWord ++ tailWord_2539616).sum := by decide
  have hdescent : baseEnd_2539616 < baseStart_2539616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539697 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 1, 4]
def baseStart_2539697 : Nat := 118140960795 + 2539697 * 2 ^ 59
def prefixEnd_2539697 : Nat := 4983230072969 + 3 ^ 40 * 2539697 * 2
def baseEnd_2539697 : Nat := 869390185187903438338435

theorem tailTrace_2539697 : CollatzResearch.WordTrace tailWord_2539697 prefixEnd_2539697 869390185187903438338435 := by
  unfold tailWord_2539697
  simp only [CollatzResearch.WordTrace]
  refine ⟨92630359480118989560449345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61753572986745993040299563 92630359480118989560449345)
  ·
    refine ⟨69472769610089242170337009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92630359480118989560449345 69472769610089242170337009)
    ·
      refine ⟨52104577207566931627752757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69472769610089242170337009 52104577207566931627752757)
      ·
        refine ⟨4884804113209399840101821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52104577207566931627752757 4884804113209399840101821)
        ·
          refine ⟨1831801542453524940038183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4884804113209399840101821 1831801542453524940038183)
          ·
            refine ⟨2747702313680287410057275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831801542453524940038183 2747702313680287410057275)
            ·
              refine ⟨4121553470520431115085913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747702313680287410057275 4121553470520431115085913)
              ·
                refine ⟨3091165102890323336314435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4121553470520431115085913 3091165102890323336314435)
                ·
                  refine ⟨4636747654335485004471653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091165102890323336314435 4636747654335485004471653)
                  ·
                    refine ⟨869390185187903438338435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4636747654335485004471653 869390185187903438338435)
                    ·
                      rfl

theorem cell22_2539697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_2539697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539697 prefixEnd_2539697 := by exact prefixLift 2539697
  have htrace : WordTrace (prefixWord ++ tailWord_2539697) baseStart_2539697 baseEnd_2539697 := by
    simpa [prefixWord, tailWord_2539697, baseEnd_2539697] using wordTrace_append hprefix tailTrace_2539697
  have hstable : (prefixWord ++ tailWord_2539697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539697).length < 2 ^ (prefixWord ++ tailWord_2539697).sum := by decide
  have hdescent : baseEnd_2539697 < baseStart_2539697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539714 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2539714 : Nat := 118140960795 + 2539714 * 2 ^ 59
def prefixEnd_2539714 : Nat := 4983230072969 + 3 ^ 40 * 2539714 * 2
def baseEnd_2539714 : Nat := 869396004635321060663383

theorem tailTrace_2539714 : CollatzResearch.WordTrace tailWord_2539714 prefixEnd_2539714 869396004635321060663383 := by
  unfold tailWord_2539714
  simp only [CollatzResearch.WordTrace]
  refine ⟨23157744880264350365954549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61753986347371600975878797 23157744880264350365954549)
  ·
    refine ⟨2171038582524782846808239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23157744880264350365954549 2171038582524782846808239)
    ·
      refine ⟨3256557873787174270212359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171038582524782846808239 3256557873787174270212359)
      ·
        refine ⟨4884836810680761405318539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3256557873787174270212359 4884836810680761405318539)
        ·
          refine ⟨7327255216021142107977809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4884836810680761405318539 7327255216021142107977809)
          ·
            refine ⟨5495441412015856580983357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7327255216021142107977809 5495441412015856580983357)
            ·
              refine ⟨2060790529505946217868759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5495441412015856580983357 2060790529505946217868759)
              ·
                refine ⟨3091185794258919326803139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060790529505946217868759 3091185794258919326803139)
                ·
                  refine ⟨4636778691388378990204709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091185794258919326803139 4636778691388378990204709)
                  ·
                    refine ⟨869396004635321060663383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4636778691388378990204709 869396004635321060663383)
                    ·
                      rfl

theorem cell22_2539714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2539714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539714 prefixEnd_2539714 := by exact prefixLift 2539714
  have htrace : WordTrace (prefixWord ++ tailWord_2539714) baseStart_2539714 baseEnd_2539714 := by
    simpa [prefixWord, tailWord_2539714, baseEnd_2539714] using wordTrace_append hprefix tailTrace_2539714
  have hstable : (prefixWord ++ tailWord_2539714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539714).length < 2 ^ (prefixWord ++ tailWord_2539714).sum := by decide
  have hdescent : baseEnd_2539714 < baseStart_2539714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539721 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 7, 3]
def baseStart_2539721 : Nat := 118140960795 + 2539721 * 2 ^ 59
def prefixEnd_2539721 : Nat := 4983230072969 + 3 ^ 40 * 2539721 * 2
def baseEnd_2539721 : Nat := 869398400878375375738361

theorem tailTrace_2539721 : CollatzResearch.WordTrace tailWord_2539721 prefixEnd_2539721 869398400878375375738361 := by
  unfold tailWord_2539721
  simp only [CollatzResearch.WordTrace]
  refine ⟨92631234832032041659323017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61754156554688027772882011 92631234832032041659323017)
  ·
    refine ⟨69473426124024031244492263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92631234832032041659323017 69473426124024031244492263)
    ·
      refine ⟨104210139186036046866738395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69473426124024031244492263 104210139186036046866738395)
      ·
        refine ⟨156315208779054070300107593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104210139186036046866738395 156315208779054070300107593)
        ·
          refine ⟨117236406584290552725080695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156315208779054070300107593 117236406584290552725080695)
          ·
            refine ⟨175854609876435829087621043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117236406584290552725080695 175854609876435829087621043)
            ·
              refine ⟨263781914814653743631431565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175854609876435829087621043 263781914814653743631431565)
              ·
                refine ⟨98918218055495153861786837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263781914814653743631431565 98918218055495153861786837)
                ·
                  refine ⟨2318395735675667668635629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 98918218055495153861786837 2318395735675667668635629)
                  ·
                    refine ⟨869398400878375375738361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2318395735675667668635629 869398400878375375738361)
                    ·
                      rfl

theorem cell22_2539721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 3].length) (baseStart_2539721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539721 prefixEnd_2539721 := by exact prefixLift 2539721
  have htrace : WordTrace (prefixWord ++ tailWord_2539721) baseStart_2539721 baseEnd_2539721 := by
    simpa [prefixWord, tailWord_2539721, baseEnd_2539721] using wordTrace_append hprefix tailTrace_2539721
  have hstable : (prefixWord ++ tailWord_2539721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539721).length < 2 ^ (prefixWord ++ tailWord_2539721).sum := by decide
  have hdescent : baseEnd_2539721 < baseStart_2539721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539736 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_2539736 : Nat := 118140960795 + 2539736 * 2 ^ 59
def prefixEnd_2539736 : Nat := 4983230072969 + 3 ^ 40 * 2539736 * 2
def baseEnd_2539736 : Nat := 869403535684920336613315

theorem tailTrace_2539736 : CollatzResearch.WordTrace tailWord_2539736 prefixEnd_2539736 869403535684920336613315 := by
  unfold tailWord_2539736
  simp only [CollatzResearch.WordTrace]
  refine ⟨46315890963488849610559531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61754521284651799480746041 46315890963488849610559531)
  ·
    refine ⟨69473836445233274415839297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46315890963488849610559531 69473836445233274415839297)
    ·
      refine ⟨52105377333924955811879473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69473836445233274415839297 52105377333924955811879473)
      ·
        refine ⟨39079033000443716858909605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52105377333924955811879473 39079033000443716858909605)
        ·
          refine ⟨7327318687583196911045551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39079033000443716858909605 7327318687583196911045551)
          ·
            refine ⟨10990978031374795366568327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7327318687583196911045551 10990978031374795366568327)
            ·
              refine ⟨16486467047062193049852491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10990978031374795366568327 16486467047062193049852491)
              ·
                refine ⟨24729700570593289574778737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16486467047062193049852491 24729700570593289574778737)
                ·
                  refine ⟨18547275427944967181084053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24729700570593289574778737 18547275427944967181084053)
                  ·
                    refine ⟨869403535684920336613315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18547275427944967181084053 869403535684920336613315)
                    ·
                      rfl

theorem cell22_2539736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_2539736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539736 prefixEnd_2539736 := by exact prefixLift 2539736
  have htrace : WordTrace (prefixWord ++ tailWord_2539736) baseStart_2539736 baseEnd_2539736 := by
    simpa [prefixWord, tailWord_2539736, baseEnd_2539736] using wordTrace_append hprefix tailTrace_2539736
  have hstable : (prefixWord ++ tailWord_2539736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539736).length < 2 ^ (prefixWord ++ tailWord_2539736).sum := by decide
  have hdescent : baseEnd_2539736 < baseStart_2539736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539772 : List Nat := [2, 2, 2, 1, 4, 2, 2, 3, 1, 3]
def baseStart_2539772 : Nat := 118140960795 + 2539772 * 2 ^ 59
def prefixEnd_2539772 : Nat := 4983230072969 + 3 ^ 40 * 2539772 * 2
def baseEnd_2539772 : Nat := 869415859220628242713205

theorem tailTrace_2539772 : CollatzResearch.WordTrace tailWord_2539772 prefixEnd_2539772 869415859220628242713205 := by
  unfold tailWord_2539772
  simp only [CollatzResearch.WordTrace]
  refine ⟨46316547477423638684714785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61755396636564851579619713 46316547477423638684714785)
  ·
    refine ⟨34737410608067729013536089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46316547477423638684714785 34737410608067729013536089)
    ·
      refine ⟨26053057956050796760152067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34737410608067729013536089 26053057956050796760152067)
      ·
        refine ⟨39079586934076195140228101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26053057956050796760152067 39079586934076195140228101)
        ·
          refine ⟨7327422550139286588792769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39079586934076195140228101 7327422550139286588792769)
          ·
            refine ⟨5495566912604464941594577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7327422550139286588792769 5495566912604464941594577)
            ·
              refine ⟨4121675184453348706195933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5495566912604464941594577 4121675184453348706195933)
              ·
                refine ⟨1545628194170005764823475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4121675184453348706195933 1545628194170005764823475)
                ·
                  refine ⟨2318442291255008647235213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545628194170005764823475 2318442291255008647235213)
                  ·
                    refine ⟨869415859220628242713205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2318442291255008647235213 869415859220628242713205)
                    ·
                      rfl

theorem cell22_2539772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_2539772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539772 prefixEnd_2539772 := by exact prefixLift 2539772
  have htrace : WordTrace (prefixWord ++ tailWord_2539772) baseStart_2539772 baseEnd_2539772 := by
    simpa [prefixWord, tailWord_2539772, baseEnd_2539772] using wordTrace_append hprefix tailTrace_2539772
  have hstable : (prefixWord ++ tailWord_2539772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539772).length < 2 ^ (prefixWord ++ tailWord_2539772).sum := by decide
  have hdescent : baseEnd_2539772 < baseStart_2539772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539781 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_2539781 : Nat := 118140960795 + 2539781 * 2 ^ 59
def prefixEnd_2539781 : Nat := 4983230072969 + 3 ^ 40 * 2539781 * 2
def baseEnd_2539781 : Nat := 869418940104555219238177

theorem tailTrace_2539781 : CollatzResearch.WordTrace tailWord_2539781 prefixEnd_2539781 869418940104555219238177 := by
  unfold tailWord_2539781
  simp only [CollatzResearch.WordTrace]
  refine ⟨92633423211814671906507197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61755615474543114604338131 92633423211814671906507197)
  ·
    refine ⟨34737533704430501964940199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92633423211814671906507197 34737533704430501964940199)
    ·
      refine ⟨52106300556645752947410299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34737533704430501964940199 52106300556645752947410299)
      ·
        refine ⟨78159450834968629421115449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52106300556645752947410299 78159450834968629421115449)
        ·
          refine ⟨58619588126226472065836587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78159450834968629421115449 58619588126226472065836587)
          ·
            refine ⟨87929382189339708098754881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58619588126226472065836587 87929382189339708098754881)
            ·
              refine ⟨65947036642004781074066161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87929382189339708098754881 65947036642004781074066161)
              ·
                refine ⟨49460277481503585805549621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65947036642004781074066161 49460277481503585805549621)
                ·
                  refine ⟨4636901013890961169270277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49460277481503585805549621 4636901013890961169270277)
                  ·
                    refine ⟨869418940104555219238177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4636901013890961169270277 869418940104555219238177)
                    ·
                      rfl

theorem cell22_2539781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_2539781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539781 prefixEnd_2539781 := by exact prefixLift 2539781
  have htrace : WordTrace (prefixWord ++ tailWord_2539781) baseStart_2539781 baseEnd_2539781 := by
    simpa [prefixWord, tailWord_2539781, baseEnd_2539781] using wordTrace_append hprefix tailTrace_2539781
  have hstable : (prefixWord ++ tailWord_2539781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539781).length < 2 ^ (prefixWord ++ tailWord_2539781).sum := by decide
  have hdescent : baseEnd_2539781 < baseStart_2539781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539926 : List Nat := [5, 3, 1, 2, 1, 1, 3, 6]
def baseStart_2539926 : Nat := 118140960795 + 2539926 * 2 ^ 59
def prefixEnd_2539926 : Nat := 4983230072969 + 3 ^ 40 * 2539926 * 2
def baseEnd_2539926 : Nat := 96607619618647019373637

theorem tailTrace_2539926 : CollatzResearch.WordTrace tailWord_2539926 prefixEnd_2539926 96607619618647019373637 := by
  unfold tailWord_2539926
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789919487268085104408477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61759141197526241113690421 5789919487268085104408477)
  ·
    refine ⟨2171219807725531914153179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5789919487268085104408477 2171219807725531914153179)
    ·
      refine ⟨3256829711588297871229769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171219807725531914153179 3256829711588297871229769)
      ·
        refine ⟨2442622283691223403422327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3256829711588297871229769 2442622283691223403422327)
        ·
          refine ⟨3663933425536835105133491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442622283691223403422327 3663933425536835105133491)
          ·
            refine ⟨5495900138305252657700237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663933425536835105133491 5495900138305252657700237)
            ·
              refine ⟨2060962551864469746637589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5495900138305252657700237 2060962551864469746637589)
              ·
                refine ⟨96607619618647019373637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2060962551864469746637589 96607619618647019373637)
                ·
                  rfl

theorem cell22_2539926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_2539926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539926 prefixEnd_2539926 := by exact prefixLift 2539926
  have htrace : WordTrace (prefixWord ++ tailWord_2539926) baseStart_2539926 baseEnd_2539926 := by
    simpa [prefixWord, tailWord_2539926, baseEnd_2539926] using wordTrace_append hprefix tailTrace_2539926
  have hstable : (prefixWord ++ tailWord_2539926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539926).length < 2 ^ (prefixWord ++ tailWord_2539926).sum := by decide
  have hdescent : baseEnd_2539926 < baseStart_2539926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539965 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 6]
def baseStart_2539965 : Nat := 118140960795 + 2539965 * 2 ^ 59
def prefixEnd_2539965 : Nat := 4983230072969 + 3 ^ 40 * 2539965 * 2
def baseEnd_2539965 : Nat := 289827309021613357545871

theorem tailTrace_2539965 : CollatzResearch.WordTrace tailWord_2539965 prefixEnd_2539965 289827309021613357545871 := by
  unfold tailWord_2539965
  simp only [CollatzResearch.WordTrace]
  refine ⟨92640134243148071331205349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61760089495432047554136899 92640134243148071331205349)
  ·
    refine ⟨17370025170590263374601003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92640134243148071331205349 17370025170590263374601003)
    ·
      refine ⟨26055037755885395061901505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17370025170590263374601003 26055037755885395061901505)
      ·
        refine ⟨19541278316914046296426129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26055037755885395061901505 19541278316914046296426129)
        ·
          refine ⟨14655958737685534722319597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19541278316914046296426129 14655958737685534722319597)
          ·
            refine ⟨5495984526632075520869849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14655958737685534722319597 5495984526632075520869849)
            ·
              refine ⟨4121988394974056640652387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5495984526632075520869849 4121988394974056640652387)
              ·
                refine ⟨6182982592461084960978581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121988394974056640652387 6182982592461084960978581)
                ·
                  refine ⟨289827309021613357545871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6182982592461084960978581 289827309021613357545871)
                  ·
                    rfl

theorem cell22_2539965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_2539965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539965 prefixEnd_2539965 := by exact prefixLift 2539965
  have htrace : WordTrace (prefixWord ++ tailWord_2539965) baseStart_2539965 baseEnd_2539965 := by
    simpa [prefixWord, tailWord_2539965, baseEnd_2539965] using wordTrace_append hprefix tailTrace_2539965
  have hstable : (prefixWord ++ tailWord_2539965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539965).length < 2 ^ (prefixWord ++ tailWord_2539965).sum := by decide
  have hdescent : baseEnd_2539965 < baseStart_2539965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539978 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_2539978 : Nat := 118140960795 + 2539978 * 2 ^ 59
def prefixEnd_2539978 : Nat := 4983230072969 + 3 ^ 40 * 2539978 * 2
def baseEnd_2539978 : Nat := 869486377230512372062573

theorem tailTrace_2539978 : CollatzResearch.WordTrace tailWord_2539978 prefixEnd_2539978 869486377230512372062573 := by
  unfold tailWord_2539978
  simp only [CollatzResearch.WordTrace]
  refine ⟨23160152098025243637857147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61760405594733983034285725 23160152098025243637857147)
  ·
    refine ⟨34740228147037865456785721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23160152098025243637857147 34740228147037865456785721)
    ·
      refine ⟨26055171110278399092589291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34740228147037865456785721 26055171110278399092589291)
      ·
        refine ⟨39082756665417598638883937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26055171110278399092589291 39082756665417598638883937)
        ·
          refine ⟨29312067499063198979162953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39082756665417598638883937 29312067499063198979162953)
          ·
            refine ⟨21984050624297399234372215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29312067499063198979162953 21984050624297399234372215)
            ·
              refine ⟨32976075936446098851558323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21984050624297399234372215 32976075936446098851558323)
              ·
                refine ⟨49464113904669148277337485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32976075936446098851558323 49464113904669148277337485)
                ·
                  refine ⟨18549042714250930604001557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49464113904669148277337485 18549042714250930604001557)
                  ·
                    refine ⟨869486377230512372062573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18549042714250930604001557 869486377230512372062573)
                    ·
                      rfl

theorem cell22_2539978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_2539978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539978 prefixEnd_2539978 := by exact prefixLift 2539978
  have htrace : WordTrace (prefixWord ++ tailWord_2539978) baseStart_2539978 baseEnd_2539978 := by
    simpa [prefixWord, tailWord_2539978, baseEnd_2539978] using wordTrace_append hprefix tailTrace_2539978
  have hstable : (prefixWord ++ tailWord_2539978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539978).length < 2 ^ (prefixWord ++ tailWord_2539978).sum := by decide
  have hdescent : baseEnd_2539978 < baseStart_2539978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539993 : List Nat := [1, 2, 1, 2, 4, 1, 3, 8]
def baseStart_2539993 : Nat := 118140960795 + 2539993 * 2 ^ 59
def prefixEnd_2539993 : Nat := 4983230072969 + 3 ^ 40 * 2539993 * 2
def baseEnd_2539993 : Nat := 96610168004117481437503

theorem tailTrace_2539993 : CollatzResearch.WordTrace tailWord_2539993 prefixEnd_2539993 96610168004117481437503 := by
  unfold tailWord_2539993
  simp only [CollatzResearch.WordTrace]
  refine ⟨92641155487046632113224633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61760770324697754742149755 92641155487046632113224633)
  ·
    refine ⟨69480866615284974084918475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92641155487046632113224633 69480866615284974084918475)
    ·
      refine ⟨104221299922927461127377713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69480866615284974084918475 104221299922927461127377713)
      ·
        refine ⟨78165974942195595845533285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104221299922927461127377713 78165974942195595845533285)
        ·
          refine ⟨14656120301661674221037491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78165974942195595845533285 14656120301661674221037491)
          ·
            refine ⟨21984180452492511331556237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14656120301661674221037491 21984180452492511331556237)
            ·
              refine ⟨8244067669684691749333589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21984180452492511331556237 8244067669684691749333589)
              ·
                refine ⟨96610168004117481437503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8244067669684691749333589 96610168004117481437503)
                ·
                  rfl

theorem cell22_2539993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 8].length) (baseStart_2539993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2539993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2539993 prefixEnd_2539993 := by exact prefixLift 2539993
  have htrace : WordTrace (prefixWord ++ tailWord_2539993) baseStart_2539993 baseEnd_2539993 := by
    simpa [prefixWord, tailWord_2539993, baseEnd_2539993] using wordTrace_append hprefix tailTrace_2539993
  have hstable : (prefixWord ++ tailWord_2539993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539993).length < 2 ^ (prefixWord ++ tailWord_2539993).sum := by decide
  have hdescent : baseEnd_2539993 < baseStart_2539993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540010 : List Nat := [3, 1, 3, 1, 3, 3, 8]
def baseStart_2540010 : Nat := 118140960795 + 2540010 * 2 ^ 59
def prefixEnd_2540010 : Nat := 4983230072969 + 3 ^ 40 * 2540010 * 2
def baseEnd_2540010 : Nat := 32203604869795368713425

theorem tailTrace_2540010 : CollatzResearch.WordTrace tailWord_2540010 prefixEnd_2540010 32203604869795368713425 := by
  unfold tailWord_2540010
  simp only [CollatzResearch.WordTrace]
  refine ⟨23160443881996261004148371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61761183685323362677728989 23160443881996261004148371)
  ·
    refine ⟨34740665822994391506222557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23160443881996261004148371 34740665822994391506222557)
    ·
      refine ⟨13027749683622896814833459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34740665822994391506222557 13027749683622896814833459)
      ·
        refine ⟨19541624525434345222250189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13027749683622896814833459 19541624525434345222250189)
        ·
          refine ⟨7328109197037879458343821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19541624525434345222250189 7328109197037879458343821)
          ·
            refine ⟨2748040948889204796878933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7328109197037879458343821 2748040948889204796878933)
            ·
              refine ⟨32203604869795368713425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2748040948889204796878933 32203604869795368713425)
              ·
                rfl

theorem cell22_2540010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 8].length) (baseStart_2540010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540010 prefixEnd_2540010 := by exact prefixLift 2540010
  have htrace : WordTrace (prefixWord ++ tailWord_2540010) baseStart_2540010 baseEnd_2540010 := by
    simpa [prefixWord, tailWord_2540010, baseEnd_2540010] using wordTrace_append hprefix tailTrace_2540010
  have hstable : (prefixWord ++ tailWord_2540010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540010).length < 2 ^ (prefixWord ++ tailWord_2540010).sum := by decide
  have hdescent : baseEnd_2540010 < baseStart_2540010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540072 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 5]
def baseStart_2540072 : Nat := 118140960795 + 2540072 * 2 ^ 59
def prefixEnd_2540072 : Nat := 4983230072969 + 3 ^ 40 * 2540072 * 2
def baseEnd_2540072 : Nat := 289839518450509153404095

theorem tailTrace_2540072 : CollatzResearch.WordTrace tailWord_2540072 prefixEnd_2540072 289839518450509153404095 := by
  unfold tailWord_2540072
  simp only [CollatzResearch.WordTrace]
  refine ⟨46322018426880214302675235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61762691235840285736900313 46322018426880214302675235)
  ·
    refine ⟨69483027640320321454012853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46322018426880214302675235 69483027640320321454012853)
    ·
      refine ⟨6514033841280030136313705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69483027640320321454012853 6514033841280030136313705)
      ·
        refine ⟨4885525380960022602235279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6514033841280030136313705 4885525380960022602235279)
        ·
          refine ⟨7328288071440033903352919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4885525380960022602235279 7328288071440033903352919)
          ·
            refine ⟨10992432107160050855029379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7328288071440033903352919 10992432107160050855029379)
            ·
              refine ⟨16488648160740076282544069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10992432107160050855029379 16488648160740076282544069)
              ·
                refine ⟨3091621530138764302977013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16488648160740076282544069 3091621530138764302977013)
                ·
                  refine ⟨289839518450509153404095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3091621530138764302977013 289839518450509153404095)
                  ·
                    rfl

theorem cell22_2540072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_2540072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540072 prefixEnd_2540072 := by exact prefixLift 2540072
  have htrace : WordTrace (prefixWord ++ tailWord_2540072) baseStart_2540072 baseEnd_2540072 := by
    simpa [prefixWord, tailWord_2540072, baseEnd_2540072] using wordTrace_append hprefix tailTrace_2540072
  have hstable : (prefixWord ++ tailWord_2540072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540072).length < 2 ^ (prefixWord ++ tailWord_2540072).sum := by decide
  have hdescent : baseEnd_2540072 < baseStart_2540072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540085 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2540085 : Nat := 118140960795 + 2540085 * 2 ^ 59
def prefixEnd_2540085 : Nat := 4983230072969 + 3 ^ 40 * 2540085 * 2
def baseEnd_2540085 : Nat := 869523005517199759637245

theorem tailTrace_2540085 : CollatzResearch.WordTrace tailWord_2540085 prefixEnd_2540085 869523005517199759637245 := by
  unfold tailWord_2540085
  simp only [CollatzResearch.WordTrace]
  refine ⟨92644511002713331825573709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61763007335142221217049139 92644511002713331825573709)
  ·
    refine ⟨34741691626017499434590141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92644511002713331825573709 34741691626017499434590141)
    ·
      refine ⟨13028134359756562287971303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34741691626017499434590141 13028134359756562287971303)
      ·
        refine ⟨19542201539634843431956955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13028134359756562287971303 19542201539634843431956955)
        ·
          refine ⟨29313302309452265147935433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19542201539634843431956955 29313302309452265147935433)
          ·
            refine ⟨21984976732089198860951575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29313302309452265147935433 21984976732089198860951575)
            ·
              refine ⟨32977465098133798291427363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21984976732089198860951575 32977465098133798291427363)
              ·
                refine ⟨49466197647200697437141045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32977465098133798291427363 49466197647200697437141045)
                ·
                  refine ⟨4637456029425065384731973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49466197647200697437141045 4637456029425065384731973)
                  ·
                    refine ⟨869523005517199759637245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4637456029425065384731973 869523005517199759637245)
                    ·
                      rfl

theorem cell22_2540085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2540085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540085 prefixEnd_2540085 := by exact prefixLift 2540085
  have htrace : WordTrace (prefixWord ++ tailWord_2540085) baseStart_2540085 baseEnd_2540085 := by
    simpa [prefixWord, tailWord_2540085, baseEnd_2540085] using wordTrace_append hprefix tailTrace_2540085
  have hstable : (prefixWord ++ tailWord_2540085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540085).length < 2 ^ (prefixWord ++ tailWord_2540085).sum := by decide
  have hdescent : baseEnd_2540085 < baseStart_2540085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540117 : List Nat := [1, 3, 2, 2, 1, 1, 3, 5, 4]
def baseStart_2540117 : Nat := 118140960795 + 2540117 * 2 ^ 59
def prefixEnd_2540117 : Nat := 4983230072969 + 3 ^ 40 * 2540117 * 2
def baseEnd_2540117 : Nat := 289844653257054114279049

theorem tailTrace_2540117 : CollatzResearch.WordTrace tailWord_2540117 prefixEnd_2540117 289844653257054114279049 := by
  unfold tailWord_2540117
  simp only [CollatzResearch.WordTrace]
  refine ⟨92645678138597401290738605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61763785425731600860492403 92645678138597401290738605)
  ·
    refine ⟨34742129301974025484026977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92645678138597401290738605 34742129301974025484026977)
    ·
      refine ⟨26056596976480519113020233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34742129301974025484026977 26056596976480519113020233)
      ·
        refine ⟨19542447732360389334765175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26056596976480519113020233 19542447732360389334765175)
        ·
          refine ⟨29313671598540584002147763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19542447732360389334765175 29313671598540584002147763)
          ·
            refine ⟨43970507397810876003221645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29313671598540584002147763 43970507397810876003221645)
            ·
              refine ⟨16488940274179078501208117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43970507397810876003221645 16488940274179078501208117)
              ·
                refine ⟨1545838150704288609488261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16488940274179078501208117 1545838150704288609488261)
                ·
                  refine ⟨289844653257054114279049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1545838150704288609488261 289844653257054114279049)
                  ·
                    rfl

theorem cell22_2540117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_2540117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540117 prefixEnd_2540117 := by exact prefixLift 2540117
  have htrace : WordTrace (prefixWord ++ tailWord_2540117) baseStart_2540117 baseEnd_2540117 := by
    simpa [prefixWord, tailWord_2540117, baseEnd_2540117] using wordTrace_append hprefix tailTrace_2540117
  have hstable : (prefixWord ++ tailWord_2540117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540117).length < 2 ^ (prefixWord ++ tailWord_2540117).sum := by decide
  have hdescent : baseEnd_2540117 < baseStart_2540117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540132 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_2540132 : Nat := 118140960795 + 2540132 * 2 ^ 59
def prefixEnd_2540132 : Nat := 4983230072969 + 3 ^ 40 * 2540132 * 2
def baseEnd_2540132 : Nat := 869539094577707303712101

theorem tailTrace_2540132 : CollatzResearch.WordTrace tailWord_2540132 prefixEnd_2540132 869539094577707303712101 := by
  unfold tailWord_2540132
  simp only [CollatzResearch.WordTrace]
  refine ⟨46323112616771529426267325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61764150155695372568356433 46323112616771529426267325)
  ·
    refine ⟨17371167231289323534850247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46323112616771529426267325 17371167231289323534850247)
    ·
      refine ⟨26056750846933985302275371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17371167231289323534850247 26056750846933985302275371)
      ·
        refine ⟨39085126270400977953413057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26056750846933985302275371 39085126270400977953413057)
        ·
          refine ⟨29313844702800733465059793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39085126270400977953413057 29313844702800733465059793)
          ·
            refine ⟨21985383527100550098794845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29313844702800733465059793 21985383527100550098794845)
            ·
              refine ⟨8244518822662706287048067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21985383527100550098794845 8244518822662706287048067)
              ·
                refine ⟨12366778233994059430572101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8244518822662706287048067 12366778233994059430572101)
                ·
                  refine ⟨2318770918873886143232269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12366778233994059430572101 2318770918873886143232269)
                  ·
                    refine ⟨869539094577707303712101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2318770918873886143232269 869539094577707303712101)
                    ·
                      rfl

theorem cell22_2540132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_2540132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540132 prefixEnd_2540132 := by exact prefixLift 2540132
  have htrace : WordTrace (prefixWord ++ tailWord_2540132) baseStart_2540132 baseEnd_2540132 := by
    simpa [prefixWord, tailWord_2540132, baseEnd_2540132] using wordTrace_append hprefix tailTrace_2540132
  have hstable : (prefixWord ++ tailWord_2540132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540132).length < 2 ^ (prefixWord ++ tailWord_2540132).sum := by decide
  have hdescent : baseEnd_2540132 < baseStart_2540132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540207 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 5]
def baseStart_2540207 : Nat := 118140960795 + 2540207 * 2 ^ 59
def prefixEnd_2540207 : Nat := 4983230072969 + 3 ^ 40 * 2540207 * 2
def baseEnd_2540207 : Nat := 289854922870144036028957

theorem tailTrace_2540207 : CollatzResearch.WordTrace tailWord_2540207 prefixEnd_2540207 289854922870144036028957 := by
  unfold tailWord_2540207
  simp only [CollatzResearch.WordTrace]
  refine ⟨92648960708271346661514875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61765973805514231107676583 92648960708271346661514875)
  ·
    refine ⟨138973441062407019992272313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92648960708271346661514875 138973441062407019992272313)
    ·
      refine ⟨104230080796805264994204235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138973441062407019992272313 104230080796805264994204235)
      ·
        refine ⟨156345121195207897491306353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104230080796805264994204235 156345121195207897491306353)
        ·
          refine ⟨117258840896405923118479765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156345121195207897491306353 117258840896405923118479765)
          ·
            refine ⟨5496508167019027646178739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117258840896405923118479765 5496508167019027646178739)
            ·
              refine ⟨8244762250528541469268109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496508167019027646178739 8244762250528541469268109)
              ·
                refine ⟨3091785843948203050975541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8244762250528541469268109 3091785843948203050975541)
                ·
                  refine ⟨289854922870144036028957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3091785843948203050975541 289854922870144036028957)
                  ·
                    rfl

theorem cell22_2540207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 5].length) (baseStart_2540207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540207 prefixEnd_2540207 := by exact prefixLift 2540207
  have htrace : WordTrace (prefixWord ++ tailWord_2540207) baseStart_2540207 baseEnd_2540207 := by
    simpa [prefixWord, tailWord_2540207, baseEnd_2540207] using wordTrace_append hprefix tailTrace_2540207
  have hstable : (prefixWord ++ tailWord_2540207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540207).length < 2 ^ (prefixWord ++ tailWord_2540207).sum := by decide
  have hdescent : baseEnd_2540207 < baseStart_2540207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540267 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 6, 3]
def baseStart_2540267 : Nat := 118140960795 + 2540267 * 2 ^ 59
def prefixEnd_2540267 : Nat := 4983230072969 + 3 ^ 40 * 2540267 * 2
def baseEnd_2540267 : Nat := 869585307836611951586687

theorem tailTrace_2540267 : CollatzResearch.WordTrace tailWord_2540267 prefixEnd_2540267 869585307836611951586687 := by
  unfold tailWord_2540267
  simp only [CollatzResearch.WordTrace]
  refine ⟨92651149088053976908699055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61767432725369317939132703 92651149088053976908699055)
  ·
    refine ⟨138976723632080965363048583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92651149088053976908699055 138976723632080965363048583)
    ·
      refine ⟨208465085448121448044572875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138976723632080965363048583 208465085448121448044572875)
      ·
        refine ⟨312697628172182172066859313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208465085448121448044572875 312697628172182172066859313)
        ·
          refine ⟨234523221129136629050144485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312697628172182172066859313 234523221129136629050144485)
          ·
            refine ⟨43973103961713117946902091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234523221129136629050144485 43973103961713117946902091)
            ·
              refine ⟨65959655942569676920353137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43973103961713117946902091 65959655942569676920353137)
              ·
                refine ⟨49469741956927257690264853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65959655942569676920353137 49469741956927257690264853)
                ·
                  refine ⟨2318894154230965204231165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49469741956927257690264853 2318894154230965204231165)
                  ·
                    refine ⟨869585307836611951586687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2318894154230965204231165 869585307836611951586687)
                    ·
                      rfl

theorem cell22_2540267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 3].length) (baseStart_2540267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540267 prefixEnd_2540267 := by exact prefixLift 2540267
  have htrace : WordTrace (prefixWord ++ tailWord_2540267) baseStart_2540267 baseEnd_2540267 := by
    simpa [prefixWord, tailWord_2540267, baseEnd_2540267] using wordTrace_append hprefix tailTrace_2540267
  have hstable : (prefixWord ++ tailWord_2540267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540267).length < 2 ^ (prefixWord ++ tailWord_2540267).sum := by decide
  have hdescent : baseEnd_2540267 < baseStart_2540267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540286 : List Nat := [4, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_2540286 : Nat := 118140960795 + 2540286 * 2 ^ 59
def prefixEnd_2540286 : Nat := 4983230072969 + 3 ^ 40 * 2540286 * 2
def baseEnd_2540286 : Nat := 289863937308300745120543

theorem tailTrace_2540286 : CollatzResearch.WordTrace tailWord_2540286 prefixEnd_2540286 289863937308300745120543 := by
  unfold tailWord_2540286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11581480259373142894205089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61767894716656762102427141 11581480259373142894205089)
  ·
    refine ⟨8686110194529857170653817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11581480259373142894205089 8686110194529857170653817)
    ·
      refine ⟨6514582645897392877990363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8686110194529857170653817 6514582645897392877990363)
      ·
        refine ⟨9771873968846089316985545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6514582645897392877990363 9771873968846089316985545)
        ·
          refine ⟨7328905476634566987739159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9771873968846089316985545 7328905476634566987739159)
          ·
            refine ⟨10993358214951850481608739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7328905476634566987739159 10993358214951850481608739)
            ·
              refine ⟨16490037322427775722413109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10993358214951850481608739 16490037322427775722413109)
              ·
                refine ⟨1545940998977603973976229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16490037322427775722413109 1545940998977603973976229)
                ·
                  refine ⟨289863937308300745120543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1545940998977603973976229 289863937308300745120543)
                  ·
                    rfl

theorem cell22_2540286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_2540286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540286 prefixEnd_2540286 := by exact prefixLift 2540286
  have htrace : WordTrace (prefixWord ++ tailWord_2540286) baseStart_2540286 baseEnd_2540286 := by
    simpa [prefixWord, tailWord_2540286, baseEnd_2540286] using wordTrace_append hprefix tailTrace_2540286
  have hstable : (prefixWord ++ tailWord_2540286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540286).length < 2 ^ (prefixWord ++ tailWord_2540286).sum := by decide
  have hdescent : baseEnd_2540286 < baseStart_2540286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540357 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_2540357 : Nat := 118140960795 + 2540357 * 2 ^ 59
def prefixEnd_2540357 : Nat := 4983230072969 + 3 ^ 40 * 2540357 * 2
def baseEnd_2540357 : Nat := 869616116675881716836411

theorem tailTrace_2540357 : CollatzResearch.WordTrace tailWord_2540357 prefixEnd_2540357 869616116675881716836411 := by
  unfold tailWord_2540357
  simp only [CollatzResearch.WordTrace]
  refine ⟨92654431657727922279475325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61769621105151948186316883 92654431657727922279475325)
  ·
    refine ⟨34745411871647970854803247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92654431657727922279475325 34745411871647970854803247)
    ·
      refine ⟨52118117807471956282204871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34745411871647970854803247 52118117807471956282204871)
      ·
        refine ⟨78177176711207934423307307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52118117807471956282204871 78177176711207934423307307)
        ·
          refine ⟨117265765066811901634960961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78177176711207934423307307 117265765066811901634960961)
          ·
            refine ⟨87949323800108926226220721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117265765066811901634960961 87949323800108926226220721)
            ·
              refine ⟨65961992850081694669665541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87949323800108926226220721 65961992850081694669665541)
              ·
                refine ⟨12367873659390317750562289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65961992850081694669665541 12367873659390317750562289)
                ·
                  refine ⟨9275905244542738312921717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12367873659390317750562289 9275905244542738312921717)
                  ·
                    refine ⟨869616116675881716836411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9275905244542738312921717 869616116675881716836411)
                    ·
                      rfl

theorem cell22_2540357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_2540357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540357 prefixEnd_2540357 := by exact prefixLift 2540357
  have htrace : WordTrace (prefixWord ++ tailWord_2540357) baseStart_2540357 baseEnd_2540357 := by
    simpa [prefixWord, tailWord_2540357, baseEnd_2540357] using wordTrace_append hprefix tailTrace_2540357
  have hstable : (prefixWord ++ tailWord_2540357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540357).length < 2 ^ (prefixWord ++ tailWord_2540357).sum := by decide
  have hdescent : baseEnd_2540357 < baseStart_2540357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540414 : List Nat := [4, 2, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2540414 : Nat := 118140960795 + 2540414 * 2 ^ 59
def prefixEnd_2540414 : Nat := 4983230072969 + 3 ^ 40 * 2540414 * 2
def baseEnd_2540414 : Nat := 869635628940752568161237

theorem tailTrace_2540414 : CollatzResearch.WordTrace tailWord_2540414 prefixEnd_2540414 869635628940752568161237 := by
  unfold tailWord_2540414
  simp only [CollatzResearch.WordTrace]
  refine ⟨11582063827315177626787537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61771007079014280676200197 11582063827315177626787537)
  ·
    refine ⟨8686547870486383220090653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11582063827315177626787537 8686547870486383220090653)
    ·
      refine ⟨3257455451432393707533995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8686547870486383220090653 3257455451432393707533995)
      ·
        refine ⟨4886183177148590561300993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257455451432393707533995 4886183177148590561300993)
        ·
          refine ⟨3664637382861442920975745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4886183177148590561300993 3664637382861442920975745)
          ·
            refine ⟨2748478037146082190731809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3664637382861442920975745 2748478037146082190731809)
            ·
              refine ⟨2061358527859561643048857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748478037146082190731809 2061358527859561643048857)
              ·
                refine ⟨1546018895894671232286643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061358527859561643048857 1546018895894671232286643)
                ·
                  refine ⟨2319028343842006848429965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1546018895894671232286643 2319028343842006848429965)
                  ·
                    refine ⟨869635628940752568161237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2319028343842006848429965 869635628940752568161237)
                    ·
                      rfl

theorem cell22_2540414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2540414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540414 prefixEnd_2540414 := by exact prefixLift 2540414
  have htrace : WordTrace (prefixWord ++ tailWord_2540414) baseStart_2540414 baseEnd_2540414 := by
    simpa [prefixWord, tailWord_2540414, baseEnd_2540414] using wordTrace_append hprefix tailTrace_2540414
  have hstable : (prefixWord ++ tailWord_2540414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540414).length < 2 ^ (prefixWord ++ tailWord_2540414).sum := by decide
  have hdescent : baseEnd_2540414 < baseStart_2540414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540421 : List Nat := [1, 3, 1, 1, 3, 4, 1, 4, 4]
def baseStart_2540421 : Nat := 118140960795 + 2540421 * 2 ^ 59
def prefixEnd_2540421 : Nat := 4983230072969 + 3 ^ 40 * 2540421 * 2
def baseEnd_2540421 : Nat := 289879341727935627745405

theorem tailTrace_2540421 : CollatzResearch.WordTrace tailWord_2540421 prefixEnd_2540421 289879341727935627745405 := by
  unfold tailWord_2540421
  simp only [CollatzResearch.WordTrace]
  refine ⟨92656765929496061209805117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61771177286330707473203411 92656765929496061209805117)
  ·
    refine ⟨34746287223561022953676919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92656765929496061209805117 34746287223561022953676919)
    ·
      refine ⟨52119430835341534430515379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34746287223561022953676919 52119430835341534430515379)
      ·
        refine ⟨78179146253012301645773069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52119430835341534430515379 78179146253012301645773069)
        ·
          refine ⟨29317179844879613117164901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78179146253012301645773069 29317179844879613117164901)
          ·
            refine ⟨5496971220914927459468419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29317179844879613117164901 5496971220914927459468419)
            ·
              refine ⟨8245456831372391189202629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496971220914927459468419 8245456831372391189202629)
              ·
                refine ⟨1546023155882323347975493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8245456831372391189202629 1546023155882323347975493)
                ·
                  refine ⟨289879341727935627745405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546023155882323347975493 289879341727935627745405)
                  ·
                    rfl

theorem cell22_2540421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_2540421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540421 prefixEnd_2540421 := by exact prefixLift 2540421
  have htrace : WordTrace (prefixWord ++ tailWord_2540421) baseStart_2540421 baseEnd_2540421 := by
    simpa [prefixWord, tailWord_2540421, baseEnd_2540421] using wordTrace_append hprefix tailTrace_2540421
  have hstable : (prefixWord ++ tailWord_2540421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540421).length < 2 ^ (prefixWord ++ tailWord_2540421).sum := by decide
  have hdescent : baseEnd_2540421 < baseStart_2540421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540436 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2540436 : Nat := 118140960795 + 2540436 * 2 ^ 59
def prefixEnd_2540436 : Nat := 4983230072969 + 3 ^ 40 * 2540436 * 2
def baseEnd_2540436 : Nat := 869643159990351844111169

theorem tailTrace_2540436 : CollatzResearch.WordTrace tailWord_2540436 prefixEnd_2540436 869643159990351844111169 := by
  unfold tailWord_2540436
  simp only [CollatzResearch.WordTrace]
  refine ⟨46328656512220859385800581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61771542016294479181067441 46328656512220859385800581)
  ·
    refine ⟨8686623096041411134837609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46328656512220859385800581 8686623096041411134837609)
    ·
      refine ⟨6514967322031058351128207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8686623096041411134837609 6514967322031058351128207)
      ·
        refine ⟨9772450983046587526692311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6514967322031058351128207 9772450983046587526692311)
        ·
          refine ⟨14658676474569881290038467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9772450983046587526692311 14658676474569881290038467)
          ·
            refine ⟨21988014711854821935057701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14658676474569881290038467 21988014711854821935057701)
            ·
              refine ⟨4122752758472779112823319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21988014711854821935057701 4122752758472779112823319)
              ·
                refine ⟨6184129137709168669234979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122752758472779112823319 6184129137709168669234979)
                ·
                  refine ⟨9276193706563753003852469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6184129137709168669234979 9276193706563753003852469)
                  ·
                    refine ⟨869643159990351844111169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9276193706563753003852469 869643159990351844111169)
                    ·
                      rfl

theorem cell22_2540436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2540436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540436 prefixEnd_2540436 := by exact prefixLift 2540436
  have htrace : WordTrace (prefixWord ++ tailWord_2540436) baseStart_2540436 baseEnd_2540436 := by
    simpa [prefixWord, tailWord_2540436, baseEnd_2540436] using wordTrace_append hprefix tailTrace_2540436
  have hstable : (prefixWord ++ tailWord_2540436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540436).length < 2 ^ (prefixWord ++ tailWord_2540436).sum := by decide
  have hdescent : baseEnd_2540436 < baseStart_2540436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540438 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2540438 : Nat := 118140960795 + 2540438 * 2 ^ 59
def prefixEnd_2540438 : Nat := 4983230072969 + 3 ^ 40 * 2540438 * 2
def baseEnd_2540438 : Nat := 289881281543741501853721

theorem tailTrace_2540438 : CollatzResearch.WordTrace tailWord_2540438 prefixEnd_2540438 289881281543741501853721 := by
  unfold tailWord_2540438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5791086623152154569573373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61771590646956315408782645 5791086623152154569573373)
  ·
    refine ⟨2171657483682057963590015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5791086623152154569573373 2171657483682057963590015)
    ·
      refine ⟨3257486225523086945385023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171657483682057963590015 3257486225523086945385023)
      ·
        refine ⟨4886229338284630418077535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257486225523086945385023 4886229338284630418077535)
        ·
          refine ⟨7329344007426945627116303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4886229338284630418077535 7329344007426945627116303)
          ·
            refine ⟨10994016011140418440674455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7329344007426945627116303 10994016011140418440674455)
            ·
              refine ⟨16491024016710627661011683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10994016011140418440674455 16491024016710627661011683)
              ·
                refine ⟨24736536025065941491517525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16491024016710627661011683 24736536025065941491517525)
                ·
                  refine ⟨289881281543741501853721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24736536025065941491517525 289881281543741501853721)
                  ·
                    rfl

theorem cell22_2540438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2540438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540438 prefixEnd_2540438 := by exact prefixLift 2540438
  have htrace : WordTrace (prefixWord ++ tailWord_2540438) baseStart_2540438 baseEnd_2540438 := by
    simpa [prefixWord, tailWord_2540438, baseEnd_2540438] using wordTrace_append hprefix tailTrace_2540438
  have hstable : (prefixWord ++ tailWord_2540438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540438).length < 2 ^ (prefixWord ++ tailWord_2540438).sum := by decide
  have hdescent : baseEnd_2540438 < baseStart_2540438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540498 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_2540498 : Nat := 118140960795 + 2540498 * 2 ^ 59
def prefixEnd_2540498 : Nat := 4983230072969 + 3 ^ 40 * 2540498 * 2
def baseEnd_2540498 : Nat := 869664383857404349060979

theorem tailTrace_2540498 : CollatzResearch.WordTrace tailWord_2540498 prefixEnd_2540498 869664383857404349060979 := by
  unfold tailWord_2540498
  simp only [CollatzResearch.WordTrace]
  refine ⟨23164893587554275840089537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61773049566811402240238765 23164893587554275840089537)
  ·
    refine ⟨17373670190665706880067153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23164893587554275840089537 17373670190665706880067153)
    ·
      refine ⟨13030252642999280160050365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17373670190665706880067153 13030252642999280160050365)
      ·
        refine ⟨4886344741124730060018887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13030252642999280160050365 4886344741124730060018887)
        ·
          refine ⟨7329517111687095090028331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4886344741124730060018887 7329517111687095090028331)
          ·
            refine ⟨10994275667530642635042497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7329517111687095090028331 10994275667530642635042497)
            ·
              refine ⟨8245706750647981976281873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10994275667530642635042497 8245706750647981976281873)
              ·
                refine ⟨6184280062985986482211405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8245706750647981976281873 6184280062985986482211405)
                ·
                  refine ⟨2319105023619744930829277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6184280062985986482211405 2319105023619744930829277)
                  ·
                    refine ⟨869664383857404349060979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2319105023619744930829277 869664383857404349060979)
                    ·
                      rfl

theorem cell22_2540498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_2540498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540498 prefixEnd_2540498 := by exact prefixLift 2540498
  have htrace : WordTrace (prefixWord ++ tailWord_2540498) baseStart_2540498 baseEnd_2540498 := by
    simpa [prefixWord, tailWord_2540498, baseEnd_2540498] using wordTrace_append hprefix tailTrace_2540498
  have hstable : (prefixWord ++ tailWord_2540498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540498).length < 2 ^ (prefixWord ++ tailWord_2540498).sum := by decide
  have hdescent : baseEnd_2540498 < baseStart_2540498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540524 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_2540524 : Nat := 118140960795 + 2540524 * 2 ^ 59
def prefixEnd_2540524 : Nat := 4983230072969 + 3 ^ 40 * 2540524 * 2
def baseEnd_2540524 : Nat := 869673284188748947910899

theorem tailTrace_2540524 : CollatzResearch.WordTrace tailWord_2540524 prefixEnd_2540524 869673284188748947910899 := by
  unfold tailWord_2540524
  simp only [CollatzResearch.WordTrace]
  refine ⟨46330261324061454900402313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61773681765415273200536417 46330261324061454900402313)
  ·
    refine ⟨34747695993046091175301735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46330261324061454900402313 34747695993046091175301735)
    ·
      refine ⟨52121543989569136762952603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34747695993046091175301735 52121543989569136762952603)
      ·
        refine ⟨78182315984353705144428905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52121543989569136762952603 78182315984353705144428905)
        ·
          refine ⟨58636736988265278858321679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78182315984353705144428905 58636736988265278858321679)
          ·
            refine ⟨87955105482397918287482519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58636736988265278858321679 87955105482397918287482519)
            ·
              refine ⟨131932658223596877431223779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87955105482397918287482519 131932658223596877431223779)
              ·
                refine ⟨197898987335395316146835669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131932658223596877431223779 197898987335395316146835669)
                ·
                  refine ⟨4638257515673327722191461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 197898987335395316146835669 4638257515673327722191461)
                  ·
                    refine ⟨869673284188748947910899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4638257515673327722191461 869673284188748947910899)
                    ·
                      rfl

theorem cell22_2540524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_2540524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540524 prefixEnd_2540524 := by exact prefixLift 2540524
  have htrace : WordTrace (prefixWord ++ tailWord_2540524) baseStart_2540524 baseEnd_2540524 := by
    simpa [prefixWord, tailWord_2540524, baseEnd_2540524] using wordTrace_append hprefix tailTrace_2540524
  have hstable : (prefixWord ++ tailWord_2540524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540524).length < 2 ^ (prefixWord ++ tailWord_2540524).sum := by decide
  have hdescent : baseEnd_2540524 < baseStart_2540524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540558 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_2540558 : Nat := 118140960795 + 2540558 * 2 ^ 59
def prefixEnd_2540558 : Nat := 4983230072969 + 3 ^ 40 * 2540558 * 2
def baseEnd_2540558 : Nat := 869684923083584192560795

theorem tailTrace_2540558 : CollatzResearch.WordTrace tailWord_2540558 prefixEnd_2540558 869684923083584192560795 := by
  unfold tailWord_2540558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11582720341249966700942791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61774508486666489071694885 11582720341249966700942791)
  ·
    refine ⟨17374080511874950051414187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11582720341249966700942791 17374080511874950051414187)
    ·
      refine ⟨26061120767812425077121281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17374080511874950051414187 26061120767812425077121281)
      ·
        refine ⟨19545840575859318807840961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26061120767812425077121281 19545840575859318807840961)
        ·
          refine ⟨14659380431894489105880721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19545840575859318807840961 14659380431894489105880721)
          ·
            refine ⟨10994535323920866829410541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14659380431894489105880721 10994535323920866829410541)
            ·
              refine ⟨4122950746470325061028953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10994535323920866829410541 4122950746470325061028953)
              ·
                refine ⟨3092213059852743795771715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122950746470325061028953 3092213059852743795771715)
                ·
                  refine ⟨4638319589779115693657573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3092213059852743795771715 4638319589779115693657573)
                  ·
                    refine ⟨869684923083584192560795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4638319589779115693657573 869684923083584192560795)
                    ·
                      rfl

theorem cell22_2540558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_2540558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540558 prefixEnd_2540558 := by exact prefixLift 2540558
  have htrace : WordTrace (prefixWord ++ tailWord_2540558) baseStart_2540558 baseEnd_2540558 := by
    simpa [prefixWord, tailWord_2540558, baseEnd_2540558] using wordTrace_append hprefix tailTrace_2540558
  have hstable : (prefixWord ++ tailWord_2540558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540558).length < 2 ^ (prefixWord ++ tailWord_2540558).sum := by decide
  have hdescent : baseEnd_2540558 < baseStart_2540558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540569 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_2540569 : Nat := 118140960795 + 2540569 * 2 ^ 59
def prefixEnd_2540569 : Nat := 4983230072969 + 3 ^ 40 * 2540569 * 2
def baseEnd_2540569 : Nat := 869688688608383830535761

theorem tailTrace_2540569 : CollatzResearch.WordTrace tailWord_2540569 prefixEnd_2540569 869688688608383830535761 := by
  unfold tailWord_2540569
  simp only [CollatzResearch.WordTrace]
  refine ⟨92662163932959882486192761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61774775955306588324128507 92662163932959882486192761)
  ·
    refine ⟨69496622949719911864644571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92662163932959882486192761 69496622949719911864644571)
    ·
      refine ⟨104244934424579867796966857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69496622949719911864644571 104244934424579867796966857)
      ·
        refine ⟨78183700818434900847725143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104244934424579867796966857 78183700818434900847725143)
        ·
          refine ⟨117275551227652351271587715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78183700818434900847725143 117275551227652351271587715)
          ·
            refine ⟨175913326841478526907381573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117275551227652351271587715 175913326841478526907381573)
            ·
              refine ⟨32983748782777223795134045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175913326841478526907381573 32983748782777223795134045)
              ·
                refine ⟨12368905793541458923175267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32983748782777223795134045 12368905793541458923175267)
                ·
                  refine ⟨18553358690312188384762901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12368905793541458923175267 18553358690312188384762901)
                  ·
                    refine ⟨869688688608383830535761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18553358690312188384762901 869688688608383830535761)
                    ·
                      rfl

theorem cell22_2540569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_2540569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540569 prefixEnd_2540569 := by exact prefixLift 2540569
  have htrace : WordTrace (prefixWord ++ tailWord_2540569) baseStart_2540569 baseEnd_2540569 := by
    simpa [prefixWord, tailWord_2540569, baseEnd_2540569] using wordTrace_append hprefix tailTrace_2540569
  have hstable : (prefixWord ++ tailWord_2540569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540569).length < 2 ^ (prefixWord ++ tailWord_2540569).sum := by decide
  have hdescent : baseEnd_2540569 < baseStart_2540569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540584 : List Nat := [2, 1, 5, 14]
def baseStart_2540584 : Nat := 118140960795 + 2540584 * 2 ^ 59
def prefixEnd_2540584 : Nat := 4983230072969 + 3 ^ 40 * 2540584 * 2
def baseEnd_2540584 : Nat := 1192995642544483938835

theorem tailTrace_2540584 : CollatzResearch.WordTrace tailWord_2540584 prefixEnd_2540584 1192995642544483938835 := by
  unfold tailWord_2540584
  simp only [CollatzResearch.WordTrace]
  refine ⟨46331355513952770023994403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61775140685270360031992537 46331355513952770023994403)
  ·
    refine ⟨69497033270929155035991605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46331355513952770023994403 69497033270929155035991605)
    ·
      refine ⟨6515346869149608284624213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69497033270929155035991605 6515346869149608284624213)
      ·
        refine ⟨1192995642544483938835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 6515346869149608284624213 1192995642544483938835)
        ·
          rfl

theorem cell22_2540584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 14].length) (baseStart_2540584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540584 prefixEnd_2540584 := by exact prefixLift 2540584
  have htrace : WordTrace (prefixWord ++ tailWord_2540584) baseStart_2540584 baseEnd_2540584 := by
    simpa [prefixWord, tailWord_2540584, baseEnd_2540584] using wordTrace_append hprefix tailTrace_2540584
  have hstable : (prefixWord ++ tailWord_2540584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540584).length < 2 ^ (prefixWord ++ tailWord_2540584).sum := by decide
  have hdescent : baseEnd_2540584 < baseStart_2540584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540588 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 2, 3]
def baseStart_2540588 : Nat := 118140960795 + 2540588 * 2 ^ 59
def prefixEnd_2540588 : Nat := 4983230072969 + 3 ^ 40 * 2540588 * 2
def baseEnd_2540588 : Nat := 869695192696674114310703

theorem tailTrace_2540588 : CollatzResearch.WordTrace tailWord_2540588 prefixEnd_2540588 869695192696674114310703 := by
  unfold tailWord_2540588
  simp only [CollatzResearch.WordTrace]
  refine ⟨46331428459945524365567209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61775237946594032487422945 46331428459945524365567209)
  ·
    refine ⟨34748571344959143274175407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46331428459945524365567209 34748571344959143274175407)
    ·
      refine ⟨52122857017438714911263111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34748571344959143274175407 52122857017438714911263111)
      ·
        refine ⟨78184285526158072366894667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52122857017438714911263111 78184285526158072366894667)
        ·
          refine ⟨117276428289237108550342001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78184285526158072366894667 117276428289237108550342001)
          ·
            refine ⟨87957321216927831412756501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117276428289237108550342001 87957321216927831412756501)
            ·
              refine ⟨4122999432043492097472961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87957321216927831412756501 4122999432043492097472961)
              ·
                refine ⟨3092249574032619073104721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122999432043492097472961 3092249574032619073104721)
                ·
                  refine ⟨2319187180524464304828541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3092249574032619073104721 2319187180524464304828541)
                  ·
                    refine ⟨869695192696674114310703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2319187180524464304828541 869695192696674114310703)
                    ·
                      rfl

theorem cell22_2540588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_2540588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540588 prefixEnd_2540588 := by exact prefixLift 2540588
  have htrace : WordTrace (prefixWord ++ tailWord_2540588) baseStart_2540588 baseEnd_2540588 := by
    simpa [prefixWord, tailWord_2540588, baseEnd_2540588] using wordTrace_append hprefix tailTrace_2540588
  have hstable : (prefixWord ++ tailWord_2540588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540588).length < 2 ^ (prefixWord ++ tailWord_2540588).sum := by decide
  have hdescent : baseEnd_2540588 < baseStart_2540588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540599 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 2, 7]
def baseStart_2540599 : Nat := 118140960795 + 2540599 * 2 ^ 59
def prefixEnd_2540599 : Nat := 4983230072969 + 3 ^ 40 * 2540599 * 2
def baseEnd_2540599 : Nat := 869698958221473752285669

theorem tailTrace_2540599 : CollatzResearch.WordTrace tailWord_2540599 prefixEnd_2540599 869698958221473752285669 := by
  unfold tailWord_2540599
  simp only [CollatzResearch.WordTrace]
  refine ⟨92663258122851197609784851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61775505415234131739856567 92663258122851197609784851)
  ·
    refine ⟨138994887184276796414677277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92663258122851197609784851 138994887184276796414677277)
    ·
      refine ⟨52123082694103798655503979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138994887184276796414677277 52123082694103798655503979)
      ·
        refine ⟨78184624041155697983255969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52123082694103798655503979 78184624041155697983255969)
        ·
          refine ⟨58638468030866773487441977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78184624041155697983255969 58638468030866773487441977)
          ·
            refine ⟨43978851023150080115581483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58638468030866773487441977 43978851023150080115581483)
            ·
              refine ⟨65968276534725120173372225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43978851023150080115581483 65968276534725120173372225)
              ·
                refine ⟨49476207401043840130029169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65968276534725120173372225 49476207401043840130029169)
                ·
                  refine ⟨37107155550782880097521877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49476207401043840130029169 37107155550782880097521877)
                  ·
                    refine ⟨869698958221473752285669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37107155550782880097521877 869698958221473752285669)
                    ·
                      rfl

theorem cell22_2540599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_2540599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540599 prefixEnd_2540599 := by exact prefixLift 2540599
  have htrace : WordTrace (prefixWord ++ tailWord_2540599) baseStart_2540599 baseEnd_2540599 := by
    simpa [prefixWord, tailWord_2540599, baseEnd_2540599] using wordTrace_append hprefix tailTrace_2540599
  have hstable : (prefixWord ++ tailWord_2540599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540599).length < 2 ^ (prefixWord ++ tailWord_2540599).sum := by decide
  have hdescent : baseEnd_2540599 < baseStart_2540599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540601 : List Nat := [1, 2, 1, 5, 2, 1, 3, 7]
def baseStart_2540601 : Nat := 118140960795 + 2540601 * 2 ^ 59
def prefixEnd_2540601 : Nat := 4983230072969 + 3 ^ 40 * 2540601 * 2
def baseEnd_2540601 : Nat := 96633293651371823748407

theorem tailTrace_2540601 : CollatzResearch.WordTrace tailWord_2540601 prefixEnd_2540601 96633293651371823748407 := by
  unfold tailWord_2540601
  simp only [CollatzResearch.WordTrace]
  refine ⟨92663331068843951951357657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61775554045895967967571771 92663331068843951951357657)
  ·
    refine ⟨69497498301632963963518243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92663331068843951951357657 69497498301632963963518243)
    ·
      refine ⟨104246247452449445945277365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69497498301632963963518243 104246247452449445945277365)
      ·
        refine ⟨9773085698667135557369753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104246247452449445945277365 9773085698667135557369753)
        ·
          refine ⟨7329814274000351668027315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9773085698667135557369753 7329814274000351668027315)
          ·
            refine ⟨10994721411000527502040973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7329814274000351668027315 10994721411000527502040973)
            ·
              refine ⟨4123020529125197813265365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10994721411000527502040973 4123020529125197813265365)
              ·
                refine ⟨96633293651371823748407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4123020529125197813265365 96633293651371823748407)
                ·
                  rfl

theorem cell22_2540601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 7].length) (baseStart_2540601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540601 prefixEnd_2540601 := by exact prefixLift 2540601
  have htrace : WordTrace (prefixWord ++ tailWord_2540601) baseStart_2540601 baseEnd_2540601 := by
    simpa [prefixWord, tailWord_2540601, baseEnd_2540601] using wordTrace_append hprefix tailTrace_2540601
  have hstable : (prefixWord ++ tailWord_2540601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540601).length < 2 ^ (prefixWord ++ tailWord_2540601).sum := by decide
  have hdescent : baseEnd_2540601 < baseStart_2540601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540650 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 3, 3]
def baseStart_2540650 : Nat := 118140960795 + 2540650 * 2 ^ 59
def prefixEnd_2540650 : Nat := 4983230072969 + 3 ^ 40 * 2540650 * 2
def baseEnd_2540650 : Nat := 869716416563726619260513

theorem tailTrace_2540650 : CollatzResearch.WordTrace tailWord_2540650 prefixEnd_2540650 869716416563726619260513 := by
  unfold tailWord_2540650
  simp only [CollatzResearch.WordTrace]
  refine ⟨23166279561416608329972851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61776745497110955546594269 23166279561416608329972851)
  ·
    refine ⟨34749419342124912494959277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23166279561416608329972851 34749419342124912494959277)
    ·
      refine ⟨13031032253296842185609729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34749419342124912494959277 13031032253296842185609729)
      ·
        refine ⟨9773274189972631639207297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13031032253296842185609729 9773274189972631639207297)
        ·
          refine ⟨7329955642479473729405473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9773274189972631639207297 7329955642479473729405473)
          ·
            refine ⟨5497466731859605297054105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7329955642479473729405473 5497466731859605297054105)
            ·
              refine ⟨4123100048894703972790579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5497466731859605297054105 4123100048894703972790579)
              ·
                refine ⟨6184650073342055959185869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123100048894703972790579 6184650073342055959185869)
                ·
                  refine ⟨2319243777503270984694701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6184650073342055959185869 2319243777503270984694701)
                  ·
                    refine ⟨869716416563726619260513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2319243777503270984694701 869716416563726619260513)
                    ·
                      rfl

theorem cell22_2540650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_2540650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540650 prefixEnd_2540650 := by exact prefixLift 2540650
  have htrace : WordTrace (prefixWord ++ tailWord_2540650) baseStart_2540650 baseEnd_2540650 := by
    simpa [prefixWord, tailWord_2540650, baseEnd_2540650] using wordTrace_append hprefix tailTrace_2540650
  have hstable : (prefixWord ++ tailWord_2540650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540650).length < 2 ^ (prefixWord ++ tailWord_2540650).sum := by decide
  have hdescent : baseEnd_2540650 < baseStart_2540650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540663 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 5]
def baseStart_2540663 : Nat := 118140960795 + 2540663 * 2 ^ 59
def prefixEnd_2540663 : Nat := 4983230072969 + 3 ^ 40 * 2540663 * 2
def baseEnd_2540663 : Nat := 289906955576466306228491

theorem tailTrace_2540663 : CollatzResearch.WordTrace tailWord_2540663 prefixEnd_2540663 289906955576466306228491 := by
  unfold tailWord_2540663
  simp only [CollatzResearch.WordTrace]
  refine ⟨92665592394619336540114643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61777061596412891026743095 92665592394619336540114643)
  ·
    refine ⟨138998388591929004810171965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92665592394619336540114643 138998388591929004810171965)
    ·
      refine ⟨52124395721973376803814487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138998388591929004810171965 52124395721973376803814487)
      ·
        refine ⟨78186593582960065205721731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52124395721973376803814487 78186593582960065205721731)
        ·
          refine ⟨117279890374440097808582597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78186593582960065205721731 117279890374440097808582597)
          ·
            refine ⟨21989979445207518339109237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117279890374440097808582597 21989979445207518339109237)
            ·
              refine ⟨2061560572988204844291491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21989979445207518339109237 2061560572988204844291491)
              ·
                refine ⟨3092340859482307266437237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061560572988204844291491 3092340859482307266437237)
                ·
                  refine ⟨289906955576466306228491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3092340859482307266437237 289906955576466306228491)
                  ·
                    rfl

theorem cell22_2540663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 5].length) (baseStart_2540663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540663 prefixEnd_2540663 := by exact prefixLift 2540663
  have htrace : WordTrace (prefixWord ++ tailWord_2540663) baseStart_2540663 baseEnd_2540663 := by
    simpa [prefixWord, tailWord_2540663, baseEnd_2540663] using wordTrace_append hprefix tailTrace_2540663
  have hstable : (prefixWord ++ tailWord_2540663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540663).length < 2 ^ (prefixWord ++ tailWord_2540663).sum := by decide
  have hdescent : baseEnd_2540663 < baseStart_2540663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540708 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 6]
def baseStart_2540708 : Nat := 118140960795 + 2540708 * 2 ^ 59
def prefixEnd_2540708 : Nat := 4983230072969 + 3 ^ 40 * 2540708 * 2
def baseEnd_2540708 : Nat := 289912090383011267103445

theorem tailTrace_2540708 : CollatzResearch.WordTrace tailWord_2540708 prefixEnd_2540708 289912090383011267103445 := by
  unfold tailWord_2540708
  simp only [CollatzResearch.WordTrace]
  refine ⟨46333616839728154612751389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61778155786304206150335185 46333616839728154612751389)
  ·
    refine ⟨17375106314898057979781771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46333616839728154612751389 17375106314898057979781771)
    ·
      refine ⟨26062659472347086969672657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17375106314898057979781771 26062659472347086969672657)
      ·
        refine ⟨19546994604260315227254493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26062659472347086969672657 19546994604260315227254493)
        ·
          refine ⟨7330122976597618210220435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19546994604260315227254493 7330122976597618210220435)
          ·
            refine ⟨10995184464896427315330653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7330122976597618210220435 10995184464896427315330653)
            ·
              refine ⟨4123194174336160243248995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10995184464896427315330653 4123194174336160243248995)
              ·
                refine ⟨6184791261504240364873493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123194174336160243248995 6184791261504240364873493)
                ·
                  refine ⟨289912090383011267103445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6184791261504240364873493 289912090383011267103445)
                  ·
                    rfl

theorem cell22_2540708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_2540708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540708 prefixEnd_2540708 := by exact prefixLift 2540708
  have htrace : WordTrace (prefixWord ++ tailWord_2540708) baseStart_2540708 baseEnd_2540708 := by
    simpa [prefixWord, tailWord_2540708, baseEnd_2540708] using wordTrace_append hprefix tailTrace_2540708
  have hstable : (prefixWord ++ tailWord_2540708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540708).length < 2 ^ (prefixWord ++ tailWord_2540708).sum := by decide
  have hdescent : baseEnd_2540708 < baseStart_2540708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540740 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2540740 : Nat := 118140960795 + 2540740 * 2 ^ 59
def prefixEnd_2540740 : Nat := 4983230072969 + 3 ^ 40 * 2540740 * 2
def baseEnd_2540740 : Nat := 869747225402996384510237

theorem tailTrace_2540740 : CollatzResearch.WordTrace tailWord_2540740 prefixEnd_2540740 869747225402996384510237 := by
  unfold tailWord_2540740
  simp only [CollatzResearch.WordTrace]
  refine ⟨46334200407670189345333837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61778933876893585793778449 46334200407670189345333837)
  ·
    refine ⟨17375325152876321004500189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46334200407670189345333837 17375325152876321004500189)
    ·
      refine ⟨6515746932328620376687571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17375325152876321004500189 6515746932328620376687571)
      ·
        refine ⟨9773620398492930565031357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6515746932328620376687571 9773620398492930565031357)
        ·
          refine ⟨3665107649434848961886759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9773620398492930565031357 3665107649434848961886759)
          ·
            refine ⟨5497661474152273442830139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665107649434848961886759 5497661474152273442830139)
            ·
              refine ⟨8246492211228410164245209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497661474152273442830139 8246492211228410164245209)
              ·
                refine ⟨6184869158421307623183907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8246492211228410164245209 6184869158421307623183907)
                ·
                  refine ⟨9277303737631961434775861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6184869158421307623183907 9277303737631961434775861)
                  ·
                    refine ⟨869747225402996384510237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9277303737631961434775861 869747225402996384510237)
                    ·
                      rfl

theorem cell22_2540740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2540740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540740 prefixEnd_2540740 := by exact prefixLift 2540740
  have htrace : WordTrace (prefixWord ++ tailWord_2540740) baseStart_2540740 baseEnd_2540740 := by
    simpa [prefixWord, tailWord_2540740, baseEnd_2540740] using wordTrace_append hprefix tailTrace_2540740
  have hstable : (prefixWord ++ tailWord_2540740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540740).length < 2 ^ (prefixWord ++ tailWord_2540740).sum := by decide
  have hdescent : baseEnd_2540740 < baseStart_2540740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540757 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 2, 3]
def baseStart_2540757 : Nat := 118140960795 + 2540757 * 2 ^ 59
def prefixEnd_2540757 : Nat := 4983230072969 + 3 ^ 40 * 2540757 * 2
def baseEnd_2540757 : Nat := 869753044850414006835185

theorem tailTrace_2540757 : CollatzResearch.WordTrace tailWord_2540757 prefixEnd_2540757 869753044850414006835185 := by
  unfold tailWord_2540757
  simp only [CollatzResearch.WordTrace]
  refine ⟨92669020856278790594036525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61779347237519193729357683 92669020856278790594036525)
  ·
    refine ⟨34750882821104546472763697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92669020856278790594036525 34750882821104546472763697)
    ·
      refine ⟨26063162115828409854572773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34750882821104546472763697 26063162115828409854572773)
      ·
        refine ⟨4886842896717826847732395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26063162115828409854572773 4886842896717826847732395)
        ·
          refine ⟨7330264345076740271598593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4886842896717826847732395 7330264345076740271598593)
          ·
            refine ⟨5497698258807555203698945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7330264345076740271598593 5497698258807555203698945)
            ·
              refine ⟨4123273694105666402774209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5497698258807555203698945 4123273694105666402774209)
              ·
                refine ⟨3092455270579249802080657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4123273694105666402774209 3092455270579249802080657)
                ·
                  refine ⟨2319341452934437351560493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3092455270579249802080657 2319341452934437351560493)
                  ·
                    refine ⟨869753044850414006835185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2319341452934437351560493 869753044850414006835185)
                    ·
                      rfl

theorem cell22_2540757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_2540757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540757 prefixEnd_2540757 := by exact prefixLift 2540757
  have htrace : WordTrace (prefixWord ++ tailWord_2540757) baseStart_2540757 baseEnd_2540757 := by
    simpa [prefixWord, tailWord_2540757, baseEnd_2540757] using wordTrace_append hprefix tailTrace_2540757
  have hstable : (prefixWord ++ tailWord_2540757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540757).length < 2 ^ (prefixWord ++ tailWord_2540757).sum := by decide
  have hdescent : baseEnd_2540757 < baseStart_2540757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540828 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2540828 : Nat := 118140960795 + 2540828 * 2 ^ 59
def prefixEnd_2540828 : Nat := 4983230072969 + 3 ^ 40 * 2540828 * 2
def baseEnd_2540828 : Nat := 869777349601393488309967

theorem tailTrace_2540828 : CollatzResearch.WordTrace tailWord_2540828 prefixEnd_2540828 869777349601393488309967 := by
  unfold tailWord_2540828
  simp only [CollatzResearch.WordTrace]
  refine ⟨46335805219510784859935569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61781073626014379813247425 46335805219510784859935569)
  ·
    refine ⟨34751853914633088644951677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46335805219510784859935569 34751853914633088644951677)
    ·
      refine ⟨13031945217987408241856879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34751853914633088644951677 13031945217987408241856879)
      ·
        refine ⟨19547917826981112362785319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13031945217987408241856879 19547917826981112362785319)
        ·
          refine ⟨29321876740471668544177979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19547917826981112362785319 29321876740471668544177979)
          ·
            refine ⟨43982815110707502816266969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29321876740471668544177979 43982815110707502816266969)
            ·
              refine ⟨32987111333030627112200227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43982815110707502816266969 32987111333030627112200227)
              ·
                refine ⟨49480666999545940668300341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32987111333030627112200227 49480666999545940668300341)
                ·
                  refine ⟨4638812531207431937653157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49480666999545940668300341 4638812531207431937653157)
                  ·
                    refine ⟨869777349601393488309967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4638812531207431937653157 869777349601393488309967)
                    ·
                      rfl

theorem cell22_2540828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2540828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540828 prefixEnd_2540828 := by exact prefixLift 2540828
  have htrace : WordTrace (prefixWord ++ tailWord_2540828) baseStart_2540828 baseEnd_2540828 := by
    simpa [prefixWord, tailWord_2540828, baseEnd_2540828] using wordTrace_append hprefix tailTrace_2540828
  have hstable : (prefixWord ++ tailWord_2540828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540828).length < 2 ^ (prefixWord ++ tailWord_2540828).sum := by decide
  have hdescent : baseEnd_2540828 < baseStart_2540828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540832 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 5]
def baseStart_2540832 : Nat := 118140960795 + 2540832 * 2 ^ 59
def prefixEnd_2540832 : Nat := 4983230072969 + 3 ^ 40 * 2540832 * 2
def baseEnd_2540832 : Nat := 289926239627712937069985

theorem tailTrace_2540832 : CollatzResearch.WordTrace tailWord_2540832 prefixEnd_2540832 289926239627712937069985 := by
  unfold tailWord_2540832
  simp only [CollatzResearch.WordTrace]
  refine ⟨46335878165503539201508375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61781170887338052268677833 46335878165503539201508375)
  ·
    refine ⟨69503817248255308802262563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46335878165503539201508375 69503817248255308802262563)
    ·
      refine ⟨104255725872382963203393845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69503817248255308802262563 104255725872382963203393845)
      ·
        refine ⟨9773974300535902800318173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104255725872382963203393845 9773974300535902800318173)
        ·
          refine ⟨3665240362700963550119315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9773974300535902800318173 3665240362700963550119315)
          ·
            refine ⟨5497860544051445325178973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665240362700963550119315 5497860544051445325178973)
            ·
              refine ⟨2061697704019291996942115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5497860544051445325178973 2061697704019291996942115)
              ·
                refine ⟨3092546556028937995413173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061697704019291996942115 3092546556028937995413173)
                ·
                  refine ⟨289926239627712937069985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3092546556028937995413173 289926239627712937069985)
                  ·
                    rfl

theorem cell22_2540832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 5].length) (baseStart_2540832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540832 prefixEnd_2540832 := by exact prefixLift 2540832
  have htrace : WordTrace (prefixWord ++ tailWord_2540832) baseStart_2540832 baseEnd_2540832 := by
    simpa [prefixWord, tailWord_2540832, baseEnd_2540832] using wordTrace_append hprefix tailTrace_2540832
  have hstable : (prefixWord ++ tailWord_2540832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540832).length < 2 ^ (prefixWord ++ tailWord_2540832).sum := by decide
  have hdescent : baseEnd_2540832 < baseStart_2540832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540858 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_2540858 : Nat := 118140960795 + 2540858 * 2 ^ 59
def prefixEnd_2540858 : Nat := 4983230072969 + 3 ^ 40 * 2540858 * 2
def baseEnd_2540858 : Nat := 869787619214483410059875

theorem tailTrace_2540858 : CollatzResearch.WordTrace tailWord_2540858 prefixEnd_2540858 869787619214483410059875 := by
  unfold tailWord_2540858
  simp only [CollatzResearch.WordTrace]
  refine ⟨23168176157228221210865807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61781803085941923228975485 23168176157228221210865807)
  ·
    refine ⟨34752264235842331816298711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23168176157228221210865807 34752264235842331816298711)
    ·
      refine ⟨52128396353763497724448067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34752264235842331816298711 52128396353763497724448067)
      ·
        refine ⟨78192594530645246586672101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52128396353763497724448067 78192594530645246586672101)
        ·
          refine ⟨14661111474495983735001019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78192594530645246586672101 14661111474495983735001019)
          ·
            refine ⟨21991667211743975602501529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14661111474495983735001019 21991667211743975602501529)
            ·
              refine ⟨16493750408807981701876147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21991667211743975602501529 16493750408807981701876147)
              ·
                refine ⟨24740625613211972552814221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16493750408807981701876147 24740625613211972552814221)
                ·
                  refine ⟨9277734604954489707305333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24740625613211972552814221 9277734604954489707305333)
                  ·
                    refine ⟨869787619214483410059875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9277734604954489707305333 869787619214483410059875)
                    ·
                      rfl

theorem cell22_2540858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_2540858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540858 prefixEnd_2540858 := by exact prefixLift 2540858
  have htrace : WordTrace (prefixWord ++ tailWord_2540858) baseStart_2540858 baseEnd_2540858 := by
    simpa [prefixWord, tailWord_2540858, baseEnd_2540858] using wordTrace_append hprefix tailTrace_2540858
  have hstable : (prefixWord ++ tailWord_2540858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540858).length < 2 ^ (prefixWord ++ tailWord_2540858).sum := by decide
  have hdescent : baseEnd_2540858 < baseStart_2540858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540870 : List Nat := [6, 1, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2540870 : Nat := 118140960795 + 2540870 * 2 ^ 59
def prefixEnd_2540870 : Nat := 4983230072969 + 3 ^ 40 * 2540870 * 2
def baseEnd_2540870 : Nat := 869791727059719378759839

theorem tailTrace_2540870 : CollatzResearch.WordTrace tailWord_2540870 prefixEnd_2540870 869791727059719378759839 := by
  unfold tailWord_2540870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896035697027169090403127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61782094869912940595266709 2896035697027169090403127)
  ·
    refine ⟨4344053545540753635604691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2896035697027169090403127 4344053545540753635604691)
    ·
      refine ⟨6516080318311130453407037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4344053545540753635604691 6516080318311130453407037)
      ·
        refine ⟨2443530119366673920027639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6516080318311130453407037 2443530119366673920027639)
        ·
          refine ⟨3665295179050010880041459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443530119366673920027639 3665295179050010880041459)
          ·
            refine ⟨5497942768575016320062189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665295179050010880041459 5497942768575016320062189)
            ·
              refine ⟨2061728538215631120023321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5497942768575016320062189 2061728538215631120023321)
              ·
                refine ⟨1546296403661723340017491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061728538215631120023321 1546296403661723340017491)
                ·
                  refine ⟨2319444605492585010026237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1546296403661723340017491 2319444605492585010026237)
                  ·
                    refine ⟨869791727059719378759839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2319444605492585010026237 869791727059719378759839)
                    ·
                      rfl

theorem cell22_2540870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2540870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540870 prefixEnd_2540870 := by exact prefixLift 2540870
  have htrace : WordTrace (prefixWord ++ tailWord_2540870) baseStart_2540870 baseEnd_2540870 := by
    simpa [prefixWord, tailWord_2540870, baseEnd_2540870] using wordTrace_append hprefix tailTrace_2540870
  have hstable : (prefixWord ++ tailWord_2540870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540870).length < 2 ^ (prefixWord ++ tailWord_2540870).sum := by decide
  have hdescent : baseEnd_2540870 < baseStart_2540870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540873 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_2540873 : Nat := 118140960795 + 2540873 * 2 ^ 59
def prefixEnd_2540873 : Nat := 4983230072969 + 3 ^ 40 * 2540873 * 2
def baseEnd_2540873 : Nat := 869792754021028370934829

theorem tailTrace_2540873 : CollatzResearch.WordTrace tailWord_2540873 prefixEnd_2540873 869792754021028370934829 := by
  unfold tailWord_2540873
  simp only [CollatzResearch.WordTrace]
  refine ⟨92673251723858542405259273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61782167815905694936839515 92673251723858542405259273)
  ·
    refine ⟨69504938792893906803944455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92673251723858542405259273 69504938792893906803944455)
    ·
      refine ⟨104257408189340860205916683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69504938792893906803944455 104257408189340860205916683)
      ·
        refine ⟨156386112284011290308875025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104257408189340860205916683 156386112284011290308875025)
        ·
          refine ⟨117289584213008467731656269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156386112284011290308875025 117289584213008467731656269)
          ·
            refine ⟨43983594079878175399371101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117289584213008467731656269 43983594079878175399371101)
            ·
              refine ⟨16493847779954315774764163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43983594079878175399371101 16493847779954315774764163)
              ·
                refine ⟨24740771669931473662146245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16493847779954315774764163 24740771669931473662146245)
                ·
                  refine ⟨4638894688112151311652421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24740771669931473662146245 4638894688112151311652421)
                  ·
                    refine ⟨869792754021028370934829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4638894688112151311652421 869792754021028370934829)
                    ·
                      rfl

theorem cell22_2540873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_2540873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540873 prefixEnd_2540873 := by exact prefixLift 2540873
  have htrace : WordTrace (prefixWord ++ tailWord_2540873) baseStart_2540873 baseEnd_2540873 := by
    simpa [prefixWord, tailWord_2540873, baseEnd_2540873] using wordTrace_append hprefix tailTrace_2540873
  have hstable : (prefixWord ++ tailWord_2540873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540873).length < 2 ^ (prefixWord ++ tailWord_2540873).sum := by decide
  have hdescent : baseEnd_2540873 < baseStart_2540873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540888 : List Nat := [2, 1, 2, 2, 1, 1, 6, 7]
def baseStart_2540888 : Nat := 118140960795 + 2540888 * 2 ^ 59
def prefixEnd_2540888 : Nat := 4983230072969 + 3 ^ 40 * 2540888 * 2
def baseEnd_2540888 : Nat := 96644209869730370201087

theorem tailTrace_2540888 : CollatzResearch.WordTrace tailWord_2540888 prefixEnd_2540888 96644209869730370201087 := by
  unfold tailWord_2540888
  simp only [CollatzResearch.WordTrace]
  refine ⟨46336899409402099983527659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61782532545869466644703545 46336899409402099983527659)
  ·
    refine ⟨69505349114103149975291489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46336899409402099983527659 69505349114103149975291489)
    ·
      refine ⟨52129011835577362481468617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69505349114103149975291489 52129011835577362481468617)
      ·
        refine ⟨39096758876683021861101463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52129011835577362481468617 39096758876683021861101463)
        ·
          refine ⟨58645138315024532791652195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39096758876683021861101463 58645138315024532791652195)
          ·
            refine ⟨87967707472536799187478293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58645138315024532791652195 87967707472536799187478293)
            ·
              refine ⟨4123486287775162461913045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87967707472536799187478293 4123486287775162461913045)
              ·
                refine ⟨96644209869730370201087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4123486287775162461913045 96644209869730370201087)
                ·
                  rfl

theorem cell22_2540888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 7].length) (baseStart_2540888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540888 prefixEnd_2540888 := by exact prefixLift 2540888
  have htrace : WordTrace (prefixWord ++ tailWord_2540888) baseStart_2540888 baseEnd_2540888 := by
    simpa [prefixWord, tailWord_2540888, baseEnd_2540888] using wordTrace_append hprefix tailTrace_2540888
  have hstable : (prefixWord ++ tailWord_2540888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540888).length < 2 ^ (prefixWord ++ tailWord_2540888).sum := by decide
  have hdescent : baseEnd_2540888 < baseStart_2540888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540933 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 7]
def baseStart_2540933 : Nat := 118140960795 + 2540933 * 2 ^ 59
def prefixEnd_2540933 : Nat := 4983230072969 + 3 ^ 40 * 2540933 * 2
def baseEnd_2540933 : Nat := 289937764415736071478215

theorem tailTrace_2540933 : CollatzResearch.WordTrace tailWord_2540933 prefixEnd_2540933 289937764415736071478215 := by
  unfold tailWord_2540933
  simp only [CollatzResearch.WordTrace]
  refine ⟨92675440103641172652443453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61783626735760781768295635 92675440103641172652443453)
  ·
    refine ⟨34753290038865439744666295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92675440103641172652443453 34753290038865439744666295)
    ·
      refine ⟨52129935058298159616999443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34753290038865439744666295 52129935058298159616999443)
      ·
        refine ⟨78194902587447239425499165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52129935058298159616999443 78194902587447239425499165)
        ·
          refine ⟨29323088470292714784562187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78194902587447239425499165 29323088470292714784562187)
          ·
            refine ⟨43984632705439072176843281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29323088470292714784562187 43984632705439072176843281)
            ·
              refine ⟨32988474529079304132632461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43984632705439072176843281 32988474529079304132632461)
              ·
                refine ⟨12370677948404739049737173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32988474529079304132632461 12370677948404739049737173)
                ·
                  refine ⟨289937764415736071478215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12370677948404739049737173 289937764415736071478215)
                  ·
                    rfl

theorem cell22_2540933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_2540933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2540933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2540933 prefixEnd_2540933 := by exact prefixLift 2540933
  have htrace : WordTrace (prefixWord ++ tailWord_2540933) baseStart_2540933 baseEnd_2540933 := by
    simpa [prefixWord, tailWord_2540933, baseEnd_2540933] using wordTrace_append hprefix tailTrace_2540933
  have hstable : (prefixWord ++ tailWord_2540933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540933).length < 2 ^ (prefixWord ++ tailWord_2540933).sum := by decide
  have hdescent : baseEnd_2540933 < baseStart_2540933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541014 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2541014 : Nat := 118140960795 + 2541014 * 2 ^ 59
def prefixEnd_2541014 : Nat := 4983230072969 + 3 ^ 40 * 2541014 * 2
def baseEnd_2541014 : Nat := 869841021202551003159397

theorem tailTrace_2541014 : CollatzResearch.WordTrace tailWord_2541014 prefixEnd_2541014 869841021202551003159397 := by
  unfold tailWord_2541014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792399651021732717883881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61785596277565148990761397 5792399651021732717883881)
  ·
    refine ⟨4344299738266299538412911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5792399651021732717883881 4344299738266299538412911)
    ·
      refine ⟨6516449607399449307619367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4344299738266299538412911 6516449607399449307619367)
      ·
        refine ⟨9774674411099173961429051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6516449607399449307619367 9774674411099173961429051)
        ·
          refine ⟨14662011616648760942143577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9774674411099173961429051 14662011616648760942143577)
          ·
            refine ⟨10996508712486570706607683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14662011616648760942143577 10996508712486570706607683)
            ·
              refine ⟨16494763068729856059911525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10996508712486570706607683 16494763068729856059911525)
              ·
                refine ⟨3092768075386848011233411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16494763068729856059911525 3092768075386848011233411)
                ·
                  refine ⟨4639152113080272016850117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3092768075386848011233411 4639152113080272016850117)
                  ·
                    refine ⟨869841021202551003159397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4639152113080272016850117 869841021202551003159397)
                    ·
                      rfl

theorem cell22_2541014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2541014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541014 prefixEnd_2541014 := by exact prefixLift 2541014
  have htrace : WordTrace (prefixWord ++ tailWord_2541014) baseStart_2541014 baseEnd_2541014 := by
    simpa [prefixWord, tailWord_2541014, baseEnd_2541014] using wordTrace_append hprefix tailTrace_2541014
  have hstable : (prefixWord ++ tailWord_2541014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541014).length < 2 ^ (prefixWord ++ tailWord_2541014).sum := by decide
  have hdescent : baseEnd_2541014 < baseStart_2541014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541025 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2541025 : Nat := 118140960795 + 2541025 * 2 ^ 59
def prefixEnd_2541025 : Nat := 4983230072969 + 3 ^ 40 * 2541025 * 2
def baseEnd_2541025 : Nat := 869844786727350641134363

theorem tailTrace_2541025 : CollatzResearch.WordTrace tailWord_2541025 prefixEnd_2541025 869844786727350641134363 := by
  unfold tailWord_2541025
  simp only [CollatzResearch.WordTrace]
  refine ⟨92678795619307872364792529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61785863746205248243195019 92678795619307872364792529)
  ·
    refine ⟨69509096714480904273594397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92678795619307872364792529 69509096714480904273594397)
    ·
      refine ⟨26065911267930339102597899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69509096714480904273594397 26065911267930339102597899)
      ·
        refine ⟨39098866901895508653896849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26065911267930339102597899 39098866901895508653896849)
        ·
          refine ⟨29324150176421631490422637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39098866901895508653896849 29324150176421631490422637)
          ·
            refine ⟨10996556316158111808908489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29324150176421631490422637 10996556316158111808908489)
            ·
              refine ⟨8247417237118583856681367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10996556316158111808908489 8247417237118583856681367)
              ·
                refine ⟨12371125855677875785022051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8247417237118583856681367 12371125855677875785022051)
                ·
                  refine ⟨18556688783516813677533077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12371125855677875785022051 18556688783516813677533077)
                  ·
                    refine ⟨869844786727350641134363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18556688783516813677533077 869844786727350641134363)
                    ·
                      rfl

theorem cell22_2541025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2541025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541025 prefixEnd_2541025 := by exact prefixLift 2541025
  have htrace : WordTrace (prefixWord ++ tailWord_2541025) baseStart_2541025 baseEnd_2541025 := by
    simpa [prefixWord, tailWord_2541025, baseEnd_2541025] using wordTrace_append hprefix tailTrace_2541025
  have hstable : (prefixWord ++ tailWord_2541025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541025).length < 2 ^ (prefixWord ++ tailWord_2541025).sum := by decide
  have hdescent : baseEnd_2541025 < baseStart_2541025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541027 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 4, 3]
def baseStart_2541027 : Nat := 118140960795 + 2541027 * 2 ^ 59
def prefixEnd_2541027 : Nat := 4983230072969 + 3 ^ 40 * 2541027 * 2
def baseEnd_2541027 : Nat := 869845471368223302584357

theorem tailTrace_2541027 : CollatzResearch.WordTrace tailWord_2541027 prefixEnd_2541027 869845471368223302584357 := by
  unfold tailWord_2541027
  simp only [CollatzResearch.WordTrace]
  refine ⟨92678868565300626706365335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61785912376867084470910223 92678868565300626706365335)
  ·
    refine ⟨139018302847950940059548003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92678868565300626706365335 139018302847950940059548003)
    ·
      refine ⟨208527454271926410089322005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139018302847950940059548003 208527454271926410089322005)
      ·
        refine ⟨9774724418996550472936969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 208527454271926410089322005 9774724418996550472936969)
        ·
          refine ⟨7331043314247412854702727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9774724418996550472936969 7331043314247412854702727)
          ·
            refine ⟨10996564971371119282054091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7331043314247412854702727 10996564971371119282054091)
            ·
              refine ⟨16494847457056678923081137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10996564971371119282054091 16494847457056678923081137)
              ·
                refine ⟨12371135592792509192310853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16494847457056678923081137 12371135592792509192310853)
                ·
                  refine ⟨2319587923648595473558285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12371135592792509192310853 2319587923648595473558285)
                  ·
                    refine ⟨869845471368223302584357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2319587923648595473558285 869845471368223302584357)
                    ·
                      rfl

theorem cell22_2541027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 3].length) (baseStart_2541027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541027 prefixEnd_2541027 := by exact prefixLift 2541027
  have htrace : WordTrace (prefixWord ++ tailWord_2541027) baseStart_2541027 baseEnd_2541027 := by
    simpa [prefixWord, tailWord_2541027, baseEnd_2541027] using wordTrace_append hprefix tailTrace_2541027
  have hstable : (prefixWord ++ tailWord_2541027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541027).length < 2 ^ (prefixWord ++ tailWord_2541027).sum := by decide
  have hdescent : baseEnd_2541027 < baseStart_2541027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541029 : List Nat := [1, 3, 1, 5, 1, 1, 3, 3, 4]
def baseStart_2541029 : Nat := 118140960795 + 2541029 * 2 ^ 59
def prefixEnd_2541029 : Nat := 4983230072969 + 3 ^ 40 * 2541029 * 2
def baseEnd_2541029 : Nat := 289948718669698654678117

theorem tailTrace_2541029 : CollatzResearch.WordTrace tailWord_2541029 prefixEnd_2541029 289948718669698654678117 := by
  unfold tailWord_2541029
  simp only [CollatzResearch.WordTrace]
  refine ⟨92678941511293381047938141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61785961007528920698625427 92678941511293381047938141)
  ·
    refine ⟨34754603066735017892976803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92678941511293381047938141 34754603066735017892976803)
    ·
      refine ⟨52131904600102526839465205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34754603066735017892976803 52131904600102526839465205)
      ·
        refine ⟨4887366056259611891199863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52131904600102526839465205 4887366056259611891199863)
        ·
          refine ⟨7331049084389417836799795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4887366056259611891199863 7331049084389417836799795)
          ·
            refine ⟨10996573626584126755199693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7331049084389417836799795 10996573626584126755199693)
            ·
              refine ⟨4123715109969047533199885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10996573626584126755199693 4123715109969047533199885)
              ·
                refine ⟨1546393166238392824949957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4123715109969047533199885 1546393166238392824949957)
                ·
                  refine ⟨289948718669698654678117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546393166238392824949957 289948718669698654678117)
                  ·
                    rfl

theorem cell22_2541029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_2541029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541029 prefixEnd_2541029 := by exact prefixLift 2541029
  have htrace : WordTrace (prefixWord ++ tailWord_2541029) baseStart_2541029 baseEnd_2541029 := by
    simpa [prefixWord, tailWord_2541029, baseEnd_2541029] using wordTrace_append hprefix tailTrace_2541029
  have hstable : (prefixWord ++ tailWord_2541029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541029).length < 2 ^ (prefixWord ++ tailWord_2541029).sum := by decide
  have hdescent : baseEnd_2541029 < baseStart_2541029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541040 : List Nat := [2, 1, 1, 1, 3, 6, 8]
def baseStart_2541040 : Nat := 118140960795 + 2541040 * 2 ^ 59
def prefixEnd_2541040 : Nat := 4983230072969 + 3 ^ 40 * 2541040 * 2
def baseEnd_2541040 : Nat := 32216663760514651926271

theorem tailTrace_2541040 : CollatzResearch.WordTrace tailWord_2541040 prefixEnd_2541040 32216663760514651926271 := by
  unfold tailWord_2541040
  simp only [CollatzResearch.WordTrace]
  refine ⟨46339671357126764963294287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61786228476169019951059049 46339671357126764963294287)
  ·
    refine ⟨69509507035690147444941431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46339671357126764963294287 69509507035690147444941431)
    ·
      refine ⟨104264260553535221167412147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69509507035690147444941431 104264260553535221167412147)
      ·
        refine ⟨156396390830302831751118221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104264260553535221167412147 156396390830302831751118221)
        ·
          refine ⟨58648646561363561906669333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156396390830302831751118221 58648646561363561906669333)
          ·
            refine ⟨2749155307563916964375125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58648646561363561906669333 2749155307563916964375125)
            ·
              refine ⟨32216663760514651926271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2749155307563916964375125 32216663760514651926271)
              ·
                rfl

theorem cell22_2541040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 8].length) (baseStart_2541040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541040 prefixEnd_2541040 := by exact prefixLift 2541040
  have htrace : WordTrace (prefixWord ++ tailWord_2541040) baseStart_2541040 baseEnd_2541040 := by
    simpa [prefixWord, tailWord_2541040, baseEnd_2541040] using wordTrace_append hprefix tailTrace_2541040
  have hstable : (prefixWord ++ tailWord_2541040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541040).length < 2 ^ (prefixWord ++ tailWord_2541040).sum := by decide
  have hdescent : baseEnd_2541040 < baseStart_2541040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541042 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_2541042 : Nat := 118140960795 + 2541042 * 2 ^ 59
def prefixEnd_2541042 : Nat := 4983230072969 + 3 ^ 40 * 2541042 * 2
def baseEnd_2541042 : Nat := 869850606174768263459311

theorem tailTrace_2541042 : CollatzResearch.WordTrace tailWord_2541042 prefixEnd_2541042 869850606174768263459311 := by
  unfold tailWord_2541042
  simp only [CollatzResearch.WordTrace]
  refine ⟨23169853915061571067040345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61786277106830856178774253 23169853915061571067040345)
  ·
    refine ⟨17377390436296178300280259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23169853915061571067040345 17377390436296178300280259)
    ·
      refine ⟨26066085654444267450420389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17377390436296178300280259 26066085654444267450420389)
      ·
        refine ⟨4887391060208300146953823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26066085654444267450420389 4887391060208300146953823)
        ·
          refine ⟨7331086590312450220430735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4887391060208300146953823 7331086590312450220430735)
          ·
            refine ⟨10996629885468675330646103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7331086590312450220430735 10996629885468675330646103)
            ·
              refine ⟨16494944828203012995969155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10996629885468675330646103 16494944828203012995969155)
              ·
                refine ⟨24742417242304519493953733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16494944828203012995969155 24742417242304519493953733)
                ·
                  refine ⟨4639203232932097405116325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24742417242304519493953733 4639203232932097405116325)
                  ·
                    refine ⟨869850606174768263459311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4639203232932097405116325 869850606174768263459311)
                    ·
                      rfl

theorem cell22_2541042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_2541042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541042 prefixEnd_2541042 := by exact prefixLift 2541042
  have htrace : WordTrace (prefixWord ++ tailWord_2541042) baseStart_2541042 baseEnd_2541042 := by
    simpa [prefixWord, tailWord_2541042, baseEnd_2541042] using wordTrace_append hprefix tailTrace_2541042
  have hstable : (prefixWord ++ tailWord_2541042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541042).length < 2 ^ (prefixWord ++ tailWord_2541042).sum := by decide
  have hdescent : baseEnd_2541042 < baseStart_2541042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541046 : List Nat := [5, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2541046 : Nat := 118140960795 + 2541046 * 2 ^ 59
def prefixEnd_2541046 : Nat := 4983230072969 + 3 ^ 40 * 2541046 * 2
def baseEnd_2541046 : Nat := 289950658485504528786433

theorem tailTrace_2541046 : CollatzResearch.WordTrace tailWord_2541046 prefixEnd_2541046 289950658485504528786433 := by
  unfold tailWord_2541046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792472597014487059456687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61786374368154528634204661 5792472597014487059456687)
  ·
    refine ⟨8688708895521730589185031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5792472597014487059456687 8688708895521730589185031)
    ·
      refine ⟨13033063343282595883777547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8688708895521730589185031 13033063343282595883777547)
      ·
        refine ⟨19549595014923893825666321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13033063343282595883777547 19549595014923893825666321)
        ·
          refine ⟨14662196261192920369249741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19549595014923893825666321 14662196261192920369249741)
          ·
            refine ⟨5498323597947345138468653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14662196261192920369249741 5498323597947345138468653)
            ·
              refine ⟨2061871349230254426925745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5498323597947345138468653 2061871349230254426925745)
              ·
                refine ⟨1546403511922690820194309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061871349230254426925745 1546403511922690820194309)
                ·
                  refine ⟨289950658485504528786433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546403511922690820194309 289950658485504528786433)
                  ·
                    rfl

theorem cell22_2541046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2541046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541046 prefixEnd_2541046 := by exact prefixLift 2541046
  have htrace : WordTrace (prefixWord ++ tailWord_2541046) baseStart_2541046 baseEnd_2541046 := by
    simpa [prefixWord, tailWord_2541046, baseEnd_2541046] using wordTrace_append hprefix tailTrace_2541046
  have hstable : (prefixWord ++ tailWord_2541046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541046).length < 2 ^ (prefixWord ++ tailWord_2541046).sum := by decide
  have hdescent : baseEnd_2541046 < baseStart_2541046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541057 : List Nat := [1, 2, 4, 1, 4, 1, 2, 7]
def baseStart_2541057 : Nat := 118140960795 + 2541057 * 2 ^ 59
def prefixEnd_2541057 : Nat := 4983230072969 + 3 ^ 40 * 2541057 * 2
def baseEnd_2541057 : Nat := 96650637886812580481585

theorem tailTrace_2541057 : CollatzResearch.WordTrace tailWord_2541057 prefixEnd_2541057 96650637886812580481585 := by
  unfold tailWord_2541057
  simp only [CollatzResearch.WordTrace]
  refine ⟨92679962755191941829957425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61786641836794627886638283 92679962755191941829957425)
  ·
    refine ⟨69509972066393956372468069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92679962755191941829957425 69509972066393956372468069)
    ·
      refine ⟨13033119762448866819837763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69509972066393956372468069 13033119762448866819837763)
      ·
        refine ⟨19549679643673300229756645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13033119762448866819837763 19549679643673300229756645)
        ·
          refine ⟨3665564933188743793079371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19549679643673300229756645 3665564933188743793079371)
          ·
            refine ⟨5498347399783115689619057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665564933188743793079371 5498347399783115689619057)
            ·
              refine ⟨4123760549837336767214293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5498347399783115689619057 4123760549837336767214293)
              ·
                refine ⟨96650637886812580481585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4123760549837336767214293 96650637886812580481585)
                ·
                  rfl

theorem cell22_2541057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 7].length) (baseStart_2541057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541057 prefixEnd_2541057 := by exact prefixLift 2541057
  have htrace : WordTrace (prefixWord ++ tailWord_2541057) baseStart_2541057 baseEnd_2541057 := by
    simpa [prefixWord, tailWord_2541057, baseEnd_2541057] using wordTrace_append hprefix tailTrace_2541057
  have hstable : (prefixWord ++ tailWord_2541057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541057).length < 2 ^ (prefixWord ++ tailWord_2541057).sum := by decide
  have hdescent : baseEnd_2541057 < baseStart_2541057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541076 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2541076 : Nat := 118140960795 + 2541076 * 2 ^ 59
def prefixEnd_2541076 : Nat := 4983230072969 + 3 ^ 40 * 2541076 * 2
def baseEnd_2541076 : Nat := 869862245069603508109207

theorem tailTrace_2541076 : CollatzResearch.WordTrace tailWord_2541076 prefixEnd_2541076 869862245069603508109207 := by
  unfold tailWord_2541076
  simp only [CollatzResearch.WordTrace]
  refine ⟨46340327871061554037449541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61787103828082072049932721 46340327871061554037449541)
  ·
    refine ⟨8688811475824041382021789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46340327871061554037449541 8688811475824041382021789)
    ·
      refine ⟨3258304303434015518258171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8688811475824041382021789 3258304303434015518258171)
      ·
        refine ⟨4887456455151023277387257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3258304303434015518258171 4887456455151023277387257)
        ·
          refine ⟨3665592341363267458040443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4887456455151023277387257 3665592341363267458040443)
          ·
            refine ⟨5498388512044901187060665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665592341363267458040443 5498388512044901187060665)
            ·
              refine ⟨4123791384033675890295499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5498388512044901187060665 4123791384033675890295499)
              ·
                refine ⟨6185687076050513835443249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123791384033675890295499 6185687076050513835443249)
                ·
                  refine ⟨4639265307037885376582437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6185687076050513835443249 4639265307037885376582437)
                  ·
                    refine ⟨869862245069603508109207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4639265307037885376582437 869862245069603508109207)
                    ·
                      rfl

theorem cell22_2541076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2541076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541076 prefixEnd_2541076 := by exact prefixLift 2541076
  have htrace : WordTrace (prefixWord ++ tailWord_2541076) baseStart_2541076 baseEnd_2541076 := by
    simpa [prefixWord, tailWord_2541076, baseEnd_2541076] using wordTrace_append hprefix tailTrace_2541076
  have hstable : (prefixWord ++ tailWord_2541076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541076).length < 2 ^ (prefixWord ++ tailWord_2541076).sum := by decide
  have hdescent : baseEnd_2541076 < baseStart_2541076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541132 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_2541132 : Nat := 118140960795 + 2541132 * 2 ^ 59
def prefixEnd_2541132 : Nat := 4983230072969 + 3 ^ 40 * 2541132 * 2
def baseEnd_2541132 : Nat := 869881415014038028709035

theorem tailTrace_2541132 : CollatzResearch.WordTrace tailWord_2541132 prefixEnd_2541132 869881415014038028709035 := by
  unfold tailWord_2541132
  simp only [CollatzResearch.WordTrace]
  refine ⟨46341349114960114819468825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61788465486613486425958433 46341349114960114819468825)
  ·
    refine ⟨34756011836220086114601619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46341349114960114819468825 34756011836220086114601619)
    ·
      refine ⟨52134017754330129171902429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34756011836220086114601619 52134017754330129171902429)
      ·
        refine ⟨19550256657873798439463411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52134017754330129171902429 19550256657873798439463411)
        ·
          refine ⟨29325384986810697659195117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19550256657873798439463411 29325384986810697659195117)
          ·
            refine ⟨10997019370054011622198169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29325384986810697659195117 10997019370054011622198169)
            ·
              refine ⟨8247764527540508716648627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10997019370054011622198169 8247764527540508716648627)
              ·
                refine ⟨12371646791310763074972941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8247764527540508716648627 12371646791310763074972941)
                ·
                  refine ⟨4639367546741536153114853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12371646791310763074972941 4639367546741536153114853)
                  ·
                    refine ⟨869881415014038028709035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4639367546741536153114853 869881415014038028709035)
                    ·
                      rfl

theorem cell22_2541132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_2541132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541132 prefixEnd_2541132 := by exact prefixLift 2541132
  have htrace : WordTrace (prefixWord ++ tailWord_2541132) baseStart_2541132 baseEnd_2541132 := by
    simpa [prefixWord, tailWord_2541132, baseEnd_2541132] using wordTrace_append hprefix tailTrace_2541132
  have hstable : (prefixWord ++ tailWord_2541132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541132).length < 2 ^ (prefixWord ++ tailWord_2541132).sum := by decide
  have hdescent : baseEnd_2541132 < baseStart_2541132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541175 : List Nat := [1, 1, 3, 1, 1, 3, 1, 11]
def baseStart_2541175 : Nat := 118140960795 + 2541175 * 2 ^ 59
def prefixEnd_2541175 : Nat := 4983230072969 + 3 ^ 40 * 2541175 * 2
def baseEnd_2541175 : Nat := 96655126088088916653767

theorem tailTrace_2541175 : CollatzResearch.WordTrace tailWord_2541175 prefixEnd_2541175 96655126088088916653767 := by
  unfold tailWord_2541175
  simp only [CollatzResearch.WordTrace]
  refine ⟨92684266568764447982752979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61789511045842965321835319 92684266568764447982752979)
  ·
    refine ⟨139026399853146671974129469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92684266568764447982752979 139026399853146671974129469)
    ·
      refine ⟨52134899944930001990298551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139026399853146671974129469 52134899944930001990298551)
      ·
        refine ⟨78202349917395002985447827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52134899944930001990298551 78202349917395002985447827)
        ·
          refine ⟨117303524876092504478171741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78202349917395002985447827 117303524876092504478171741)
          ·
            refine ⟨43988821828534689179314403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117303524876092504478171741 43988821828534689179314403)
            ·
              refine ⟨65983232742802033768971605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43988821828534689179314403 65983232742802033768971605)
              ·
                refine ⟨96655126088088916653767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 65983232742802033768971605 96655126088088916653767)
                ·
                  rfl

theorem cell22_2541175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 11].length) (baseStart_2541175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541175 prefixEnd_2541175 := by exact prefixLift 2541175
  have htrace : WordTrace (prefixWord ++ tailWord_2541175) baseStart_2541175 baseEnd_2541175 := by
    simpa [prefixWord, tailWord_2541175, baseEnd_2541175] using wordTrace_append hprefix tailTrace_2541175
  have hstable : (prefixWord ++ tailWord_2541175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541175).length < 2 ^ (prefixWord ++ tailWord_2541175).sum := by decide
  have hdescent : baseEnd_2541175 < baseStart_2541175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541312 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_2541312 : Nat := 118140960795 + 2541312 * 2 ^ 59
def prefixEnd_2541312 : Nat := 4983230072969 + 3 ^ 40 * 2541312 * 2
def baseEnd_2541312 : Nat := 869943032692577559208483

theorem tailTrace_2541312 : CollatzResearch.WordTrace tailWord_2541312 prefixEnd_2541312 869943032692577559208483 := by
  unfold tailWord_2541312
  simp only [CollatzResearch.WordTrace]
  refine ⟨46344631684634060190245095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61792842246178746920326793 46344631684634060190245095)
  ·
    refine ⟨69516947526951090285367643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46344631684634060190245095 69516947526951090285367643)
    ·
      refine ⟨104275421290426635428051465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69516947526951090285367643 104275421290426635428051465)
      ·
        refine ⟨78206565967819976571038599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104275421290426635428051465 78206565967819976571038599)
        ·
          refine ⟨117309848951729964856557899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78206565967819976571038599 117309848951729964856557899)
          ·
            refine ⟨175964773427594947284836849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117309848951729964856557899 175964773427594947284836849)
            ·
              refine ⟨131973580070696210463627637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175964773427594947284836849 131973580070696210463627637)
              ·
                refine ⟨12372523131627769730965091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131973580070696210463627637 12372523131627769730965091)
                ·
                  refine ⟨18558784697441654596447637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12372523131627769730965091 18558784697441654596447637)
                  ·
                    refine ⟨869943032692577559208483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18558784697441654596447637 869943032692577559208483)
                    ·
                      rfl

theorem cell22_2541312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_2541312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541312 prefixEnd_2541312 := by exact prefixLift 2541312
  have htrace : WordTrace (prefixWord ++ tailWord_2541312) baseStart_2541312 baseEnd_2541312 := by
    simpa [prefixWord, tailWord_2541312, baseEnd_2541312] using wordTrace_append hprefix tailTrace_2541312
  have hstable : (prefixWord ++ tailWord_2541312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541312).length < 2 ^ (prefixWord ++ tailWord_2541312).sum := by decide
  have hdescent : baseEnd_2541312 < baseStart_2541312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541316 : List Nat := [2, 3, 2, 2, 1, 2, 1, 5, 4]
def baseStart_2541316 : Nat := 118140960795 + 2541316 * 2 ^ 59
def prefixEnd_2541316 : Nat := 4983230072969 + 3 ^ 40 * 2541316 * 2
def baseEnd_2541316 : Nat := 289981467324774294036157

theorem tailTrace_2541316 : CollatzResearch.WordTrace tailWord_2541316 prefixEnd_2541316 289981467324774294036157 := by
  unfold tailWord_2541316
  simp only [CollatzResearch.WordTrace]
  refine ⟨46344704630626814531817901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61792939507502419375757201 46344704630626814531817901)
  ·
    refine ⟨17379264236485055449431713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46344704630626814531817901 17379264236485055449431713)
    ·
      refine ⟨13034448177363791587073785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17379264236485055449431713 13034448177363791587073785)
      ·
        refine ⟨9775836133022843690305339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13034448177363791587073785 9775836133022843690305339)
        ·
          refine ⟨14663754199534265535458009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9775836133022843690305339 14663754199534265535458009)
          ·
            refine ⟨10997815649650699151593507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14663754199534265535458009 10997815649650699151593507)
            ·
              refine ⟨16496723474476048727390261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10997815649650699151593507 16496723474476048727390261)
              ·
                refine ⟨1546567825732129568192837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16496723474476048727390261 1546567825732129568192837)
                ·
                  refine ⟨289981467324774294036157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546567825732129568192837 289981467324774294036157)
                  ·
                    rfl

theorem cell22_2541316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_2541316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541316 prefixEnd_2541316 := by exact prefixLift 2541316
  have htrace : WordTrace (prefixWord ++ tailWord_2541316) baseStart_2541316 baseEnd_2541316 := by
    simpa [prefixWord, tailWord_2541316, baseEnd_2541316] using wordTrace_append hprefix tailTrace_2541316
  have hstable : (prefixWord ++ tailWord_2541316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541316).length < 2 ^ (prefixWord ++ tailWord_2541316).sum := by decide
  have hdescent : baseEnd_2541316 < baseStart_2541316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541361 : List Nat := [1, 2, 2, 3, 2, 4, 2, 6]
def baseStart_2541361 : Nat := 118140960795 + 2541361 * 2 ^ 59
def prefixEnd_2541361 : Nat := 4983230072969 + 3 ^ 40 * 2541361 * 2
def baseEnd_2541361 : Nat := 96662200710439751637037

theorem tailTrace_2541361 : CollatzResearch.WordTrace tailWord_2541361 prefixEnd_2541361 96662200710439751637037 := by
  unfold tailWord_2541361
  simp only [CollatzResearch.WordTrace]
  refine ⟨92691050546090601749023937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61794033697393734499349291 92691050546090601749023937)
  ·
    refine ⟨69518287909567951311767953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92691050546090601749023937 69518287909567951311767953)
    ·
      refine ⟨52138715932175963483825965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69518287909567951311767953 52138715932175963483825965)
      ·
        refine ⟨19552018474565986306434737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52138715932175963483825965 19552018474565986306434737)
        ·
          refine ⟨14664013855924489729826053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19552018474565986306434737 14664013855924489729826053)
          ·
            refine ⟨2749502597985841824342385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14664013855924489729826053 2749502597985841824342385)
            ·
              refine ⟨2062126948489381368256789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2749502597985841824342385 2062126948489381368256789)
              ·
                refine ⟨96662200710439751637037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2062126948489381368256789 96662200710439751637037)
                ·
                  rfl

theorem cell22_2541361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 6].length) (baseStart_2541361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541361 prefixEnd_2541361 := by exact prefixLift 2541361
  have htrace : WordTrace (prefixWord ++ tailWord_2541361) baseStart_2541361 baseEnd_2541361 := by
    simpa [prefixWord, tailWord_2541361, baseEnd_2541361] using wordTrace_append hprefix tailTrace_2541361
  have hstable : (prefixWord ++ tailWord_2541361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541361).length < 2 ^ (prefixWord ++ tailWord_2541361).sum := by decide
  have hdescent : baseEnd_2541361 < baseStart_2541361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541393 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 3, 3]
def baseStart_2541393 : Nat := 118140960795 + 2541393 * 2 ^ 59
def prefixEnd_2541393 : Nat := 4983230072969 + 3 ^ 40 * 2541393 * 2
def baseEnd_2541393 : Nat := 869970760647920347933235

theorem tailTrace_2541393 : CollatzResearch.WordTrace tailWord_2541393 prefixEnd_2541393 869970760647920347933235 := by
  unfold tailWord_2541393
  simp only [CollatzResearch.WordTrace]
  refine ⟨92692217681974671214188833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61794811787983114142792555 92692217681974671214188833)
  ·
    refine ⟨69519163261481003410641625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92692217681974671214188833 69519163261481003410641625)
    ·
      refine ⟨52139372446110752557981219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69519163261481003410641625 52139372446110752557981219)
      ·
        refine ⟨78209058669166128836971829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52139372446110752557981219 78209058669166128836971829)
        ·
          refine ⟨7332099250234324578466109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78209058669166128836971829 7332099250234324578466109)
          ·
            refine ⟨2749537218837871716924791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7332099250234324578466109 2749537218837871716924791)
            ·
              refine ⟨4124305828256807575387187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749537218837871716924791 4124305828256807575387187)
              ·
                refine ⟨6186458742385211363080781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124305828256807575387187 6186458742385211363080781)
                ·
                  refine ⟨2319922028394454261155293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6186458742385211363080781 2319922028394454261155293)
                  ·
                    refine ⟨869970760647920347933235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2319922028394454261155293 869970760647920347933235)
                    ·
                      rfl

theorem cell22_2541393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_2541393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541393 prefixEnd_2541393 := by exact prefixLift 2541393
  have htrace : WordTrace (prefixWord ++ tailWord_2541393) baseStart_2541393 baseEnd_2541393 := by
    simpa [prefixWord, tailWord_2541393, baseEnd_2541393] using wordTrace_append hprefix tailTrace_2541393
  have hstable : (prefixWord ++ tailWord_2541393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541393).length < 2 ^ (prefixWord ++ tailWord_2541393).sum := by decide
  have hdescent : baseEnd_2541393 < baseStart_2541393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541449 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_2541449 : Nat := 118140960795 + 2541449 * 2 ^ 59
def prefixEnd_2541449 : Nat := 4983230072969 + 3 ^ 40 * 2541449 * 2
def baseEnd_2541449 : Nat := 869989930592354868533063

theorem tailTrace_2541449 : CollatzResearch.WordTrace tailWord_2541449 prefixEnd_2541449 869989930592354868533063 := by
  unfold tailWord_2541449
  simp only [CollatzResearch.WordTrace]
  refine ⟨92694260169771792778227401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61796173446514528518818267 92694260169771792778227401)
  ·
    refine ⟨69520695127328844583670551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92694260169771792778227401 69520695127328844583670551)
    ·
      refine ⟨104281042690993266875505827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69520695127328844583670551 104281042690993266875505827)
      ·
        refine ⟨156421564036489900313258741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104281042690993266875505827 156421564036489900313258741)
        ·
          refine ⟨14664521628420928154368007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156421564036489900313258741 14664521628420928154368007)
          ·
            refine ⟨21996782442631392231552011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14664521628420928154368007 21996782442631392231552011)
            ·
              refine ⟨32995173663947088347328017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21996782442631392231552011 32995173663947088347328017)
              ·
                refine ⟨24746380247960316260496013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32995173663947088347328017 24746380247960316260496013)
                ·
                  refine ⟨9279892592985118597686005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24746380247960316260496013 9279892592985118597686005)
                  ·
                    refine ⟨869989930592354868533063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9279892592985118597686005 869989930592354868533063)
                    ·
                      rfl

theorem cell22_2541449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_2541449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541449 prefixEnd_2541449 := by exact prefixLift 2541449
  have htrace : WordTrace (prefixWord ++ tailWord_2541449) baseStart_2541449 baseEnd_2541449 := by
    simpa [prefixWord, tailWord_2541449, baseEnd_2541449] using wordTrace_append hprefix tailTrace_2541449
  have hstable : (prefixWord ++ tailWord_2541449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541449).length < 2 ^ (prefixWord ++ tailWord_2541449).sum := by decide
  have hdescent : baseEnd_2541449 < baseStart_2541449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541466 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_2541466 : Nat := 118140960795 + 2541466 * 2 ^ 59
def prefixEnd_2541466 : Nat := 4983230072969 + 3 ^ 40 * 2541466 * 2
def baseEnd_2541466 : Nat := 869995750039772490858011

theorem tailTrace_2541466 : CollatzResearch.WordTrace tailWord_2541466 prefixEnd_2541466 869995750039772490858011 := by
  unfold tailWord_2541466
  simp only [CollatzResearch.WordTrace]
  refine ⟨23173720052677551170399063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61796586807140136454397501 23173720052677551170399063)
  ·
    refine ⟨34760580079016326755598595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23173720052677551170399063 34760580079016326755598595)
    ·
      refine ⟨52140870118524490133397893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34760580079016326755598595 52140870118524490133397893)
      ·
        refine ⟨9776413147223341900012105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52140870118524490133397893 9776413147223341900012105)
        ·
          refine ⟨7332309860417506425009079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9776413147223341900012105 7332309860417506425009079)
          ·
            refine ⟨10998464790626259637513619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7332309860417506425009079 10998464790626259637513619)
            ·
              refine ⟨16497697185939389456270429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10998464790626259637513619 16497697185939389456270429)
              ·
                refine ⟨6186636444727271046101411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16497697185939389456270429 6186636444727271046101411)
                ·
                  refine ⟨9279954667090906569152117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6186636444727271046101411 9279954667090906569152117)
                  ·
                    refine ⟨869995750039772490858011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9279954667090906569152117 869995750039772490858011)
                    ·
                      rfl

theorem cell22_2541466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_2541466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541466 prefixEnd_2541466 := by exact prefixLift 2541466
  have htrace : WordTrace (prefixWord ++ tailWord_2541466) baseStart_2541466 baseEnd_2541466 := by
    simpa [prefixWord, tailWord_2541466, baseEnd_2541466] using wordTrace_append hprefix tailTrace_2541466
  have hstable : (prefixWord ++ tailWord_2541466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541466).length < 2 ^ (prefixWord ++ tailWord_2541466).sum := by decide
  have hdescent : baseEnd_2541466 < baseStart_2541466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541500 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 4, 3]
def baseStart_2541500 : Nat := 118140960795 + 2541500 * 2 ^ 59
def prefixEnd_2541500 : Nat := 4983230072969 + 3 ^ 40 * 2541500 * 2
def baseEnd_2541500 : Nat := 870007388934607735507907

theorem tailTrace_2541500 : CollatzResearch.WordTrace tailWord_2541500 prefixEnd_2541500 870007388934607735507907 := by
  unfold tailWord_2541500
  simp only [CollatzResearch.WordTrace]
  refine ⟨46348060146293514244166977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61797413528391352325555969 46348060146293514244166977)
  ·
    refine ⟨34761045109720135683125233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46348060146293514244166977 34761045109720135683125233)
    ·
      refine ⟨26070783832290101762343925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34761045109720135683125233 26070783832290101762343925)
      ·
        refine ⟨2444135984277197040219743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26070783832290101762343925 2444135984277197040219743)
        ·
          refine ⟨3666203976415795560329615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444135984277197040219743 3666203976415795560329615)
          ·
            refine ⟨5499305964623693340494423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666203976415795560329615 5499305964623693340494423)
            ·
              refine ⟨8248958946935540010741635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5499305964623693340494423 8248958946935540010741635)
              ·
                refine ⟨12373438420403310016112453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8248958946935540010741635 12373438420403310016112453)
                ·
                  refine ⟨2320019703825620628021085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12373438420403310016112453 2320019703825620628021085)
                  ·
                    refine ⟨870007388934607735507907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320019703825620628021085 870007388934607735507907)
                    ·
                      rfl

theorem cell22_2541500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_2541500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541500 prefixEnd_2541500 := by exact prefixLift 2541500
  have htrace : WordTrace (prefixWord ++ tailWord_2541500) baseStart_2541500 baseEnd_2541500 := by
    simpa [prefixWord, tailWord_2541500, baseEnd_2541500] using wordTrace_append hprefix tailTrace_2541500
  have hstable : (prefixWord ++ tailWord_2541500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541500).length < 2 ^ (prefixWord ++ tailWord_2541500).sum := by decide
  have hdescent : baseEnd_2541500 < baseStart_2541500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541509 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_2541509 : Nat := 118140960795 + 2541509 * 2 ^ 59
def prefixEnd_2541509 : Nat := 4983230072969 + 3 ^ 40 * 2541509 * 2
def baseEnd_2541509 : Nat := 870010469818534712032879

theorem tailTrace_2541509 : CollatzResearch.WordTrace tailWord_2541509 prefixEnd_2541509 870010469818534712032879 := by
  unfold tailWord_2541509
  simp only [CollatzResearch.WordTrace]
  refine ⟨92696448549554423025411581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61797632366369615350274387 92696448549554423025411581)
  ·
    refine ⟨34761168206082908634529343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92696448549554423025411581 34761168206082908634529343)
    ·
      refine ⟨52141752309124362951794015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34761168206082908634529343 52141752309124362951794015)
      ·
        refine ⟨78212628463686544427691023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52141752309124362951794015 78212628463686544427691023)
        ·
          refine ⟨117318942695529816641536535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78212628463686544427691023 117318942695529816641536535)
          ·
            refine ⟨175978414043294724962304803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117318942695529816641536535 175978414043294724962304803)
            ·
              refine ⟨263967621064942087443457205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175978414043294724962304803 263967621064942087443457205)
              ·
                refine ⟨24746964474838320697824113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 263967621064942087443457205 24746964474838320697824113)
                ·
                  refine ⟨18560223356128740523368085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24746964474838320697824113 18560223356128740523368085)
                  ·
                    refine ⟨870010469818534712032879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18560223356128740523368085 870010469818534712032879)
                    ·
                      rfl

theorem cell22_2541509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_2541509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541509 prefixEnd_2541509 := by exact prefixLift 2541509
  have htrace : WordTrace (prefixWord ++ tailWord_2541509) baseStart_2541509 baseEnd_2541509 := by
    simpa [prefixWord, tailWord_2541509, baseEnd_2541509] using wordTrace_append hprefix tailTrace_2541509
  have hstable : (prefixWord ++ tailWord_2541509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541509).length < 2 ^ (prefixWord ++ tailWord_2541509).sum := by decide
  have hdescent : baseEnd_2541509 < baseStart_2541509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541530 : List Nat := [3, 1, 1, 2, 6, 1, 2, 6]
def baseStart_2541530 : Nat := 118140960795 + 2541530 * 2 ^ 59
def prefixEnd_2541530 : Nat := 4983230072969 + 3 ^ 40 * 2541530 * 2
def baseEnd_2541530 : Nat := 96668628727521961917535

theorem tailTrace_2541530 : CollatzResearch.WordTrace tailWord_2541530 prefixEnd_2541530 96668628727521961917535 := by
  unfold tailWord_2541530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23174303620619585902981511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61798142988318895741284029 23174303620619585902981511)
  ·
    refine ⟨34761455430929378854472267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23174303620619585902981511 34761455430929378854472267)
    ·
      refine ⟨52142183146394068281708401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34761455430929378854472267 52142183146394068281708401)
      ·
        refine ⟨39106637359795551211281301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52142183146394068281708401 39106637359795551211281301)
        ·
          refine ⟨1833123626240416463028811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39106637359795551211281301 1833123626240416463028811)
          ·
            refine ⟨2749685439360624694543217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833123626240416463028811 2749685439360624694543217)
            ·
              refine ⟨2062264079520468520907413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2749685439360624694543217 2062264079520468520907413)
              ·
                refine ⟨96668628727521961917535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2062264079520468520907413 96668628727521961917535)
                ·
                  rfl

theorem cell22_2541530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_2541530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541530 prefixEnd_2541530 := by exact prefixLift 2541530
  have htrace : WordTrace (prefixWord ++ tailWord_2541530) baseStart_2541530 baseEnd_2541530 := by
    simpa [prefixWord, tailWord_2541530, baseEnd_2541530] using wordTrace_append hprefix tailTrace_2541530
  have hstable : (prefixWord ++ tailWord_2541530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541530).length < 2 ^ (prefixWord ++ tailWord_2541530).sum := by decide
  have hdescent : baseEnd_2541530 < baseStart_2541530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541575 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 5]
def baseStart_2541575 : Nat := 118140960795 + 2541575 * 2 ^ 59
def prefixEnd_2541575 : Nat := 4983230072969 + 3 ^ 40 * 2541575 * 2
def baseEnd_2541575 : Nat := 290011020989110846627559

theorem tailTrace_2541575 : CollatzResearch.WordTrace tailWord_2541575 prefixEnd_2541575 290011020989110846627559 := by
  unfold tailWord_2541575
  simp only [CollatzResearch.WordTrace]
  refine ⟨92698855767315316297314179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61799237178210210864876119 92698855767315316297314179)
  ·
    refine ⟨139048283650972974445971269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92698855767315316297314179 139048283650972974445971269)
    ·
      refine ⟨26071553184557432708619613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139048283650972974445971269 26071553184557432708619613)
      ·
        refine ⟨9776832444209037265732355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26071553184557432708619613 9776832444209037265732355)
        ·
          refine ⟨14665248666313555898598533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9776832444209037265732355 14665248666313555898598533)
          ·
            refine ⟨2749734124933791730987225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14665248666313555898598533 2749734124933791730987225)
            ·
              refine ⟨2062300593700343798240419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2749734124933791730987225 2062300593700343798240419)
              ·
                refine ⟨3093450890550515697360629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062300593700343798240419 3093450890550515697360629)
                ·
                  refine ⟨290011020989110846627559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3093450890550515697360629 290011020989110846627559)
                  ·
                    rfl

theorem cell22_2541575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 5].length) (baseStart_2541575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541575 prefixEnd_2541575 := by exact prefixLift 2541575
  have htrace : WordTrace (prefixWord ++ tailWord_2541575) baseStart_2541575 baseEnd_2541575 := by
    simpa [prefixWord, tailWord_2541575, baseEnd_2541575] using wordTrace_append hprefix tailTrace_2541575
  have hstable : (prefixWord ++ tailWord_2541575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541575).length < 2 ^ (prefixWord ++ tailWord_2541575).sum := by decide
  have hdescent : baseEnd_2541575 < baseStart_2541575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541603 : List Nat := [1, 1, 1, 4, 3, 1, 2, 5, 4]
def baseStart_2541603 : Nat := 118140960795 + 2541603 * 2 ^ 59
def prefixEnd_2541603 : Nat := 4983230072969 + 3 ^ 40 * 2541603 * 2
def baseEnd_2541603 : Nat := 290014215979849933394197

theorem tailTrace_2541603 : CollatzResearch.WordTrace tailWord_2541603 prefixEnd_2541603 290014215979849933394197 := by
  unfold tailWord_2541603
  simp only [CollatzResearch.WordTrace]
  refine ⟨92699877011213877079333463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61799918007475918052888975 92699877011213877079333463)
  ·
    refine ⟨139049815516820815619000195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92699877011213877079333463 139049815516820815619000195)
    ·
      refine ⟨208574723275231223428500293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139049815516820815619000195 208574723275231223428500293)
      ·
        refine ⟨39107760614105854392843805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208574723275231223428500293 39107760614105854392843805)
        ·
          refine ⟨14665410230289695397316427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39107760614105854392843805 14665410230289695397316427)
          ·
            refine ⟨21998115345434543095974641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14665410230289695397316427 21998115345434543095974641)
            ·
              refine ⟨16498586509075907321980981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21998115345434543095974641 16498586509075907321980981)
              ·
                refine ⟨1546742485225866311435717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16498586509075907321980981 1546742485225866311435717)
                ·
                  refine ⟨290014215979849933394197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546742485225866311435717 290014215979849933394197)
                  ·
                    rfl

theorem cell22_2541603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 4].length) (baseStart_2541603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541603 prefixEnd_2541603 := by exact prefixLift 2541603
  have htrace : WordTrace (prefixWord ++ tailWord_2541603) baseStart_2541603 baseEnd_2541603 := by
    simpa [prefixWord, tailWord_2541603, baseEnd_2541603] using wordTrace_append hprefix tailTrace_2541603
  have hstable : (prefixWord ++ tailWord_2541603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541603).length < 2 ^ (prefixWord ++ tailWord_2541603).sum := by decide
  have hdescent : baseEnd_2541603 < baseStart_2541603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541605 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 1, 4]
def baseStart_2541605 : Nat := 118140960795 + 2541605 * 2 ^ 59
def prefixEnd_2541605 : Nat := 4983230072969 + 3 ^ 40 * 2541605 * 2
def baseEnd_2541605 : Nat := 870043332580422461632585

theorem tailTrace_2541605 : CollatzResearch.WordTrace tailWord_2541605 prefixEnd_2541605 870043332580422461632585 := by
  unfold tailWord_2541605
  simp only [CollatzResearch.WordTrace]
  refine ⟨92699949957206631420906269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61799966638137754280604179 92699949957206631420906269)
  ·
    refine ⟨34762481233952486782839851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92699949957206631420906269 34762481233952486782839851)
    ·
      refine ⟨52143721850928730174259777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34762481233952486782839851 52143721850928730174259777)
      ·
        refine ⟨39107791388196547630694833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52143721850928730174259777 39107791388196547630694833)
        ·
          refine ⟨29330843541147410723021125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39107791388196547630694833 29330843541147410723021125)
          ·
            refine ⟨5499533163965139510566461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29330843541147410723021125 5499533163965139510566461)
            ·
              refine ⟨2062324936486927316462423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5499533163965139510566461 2062324936486927316462423)
              ·
                refine ⟨3093487404730390974693635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062324936486927316462423 3093487404730390974693635)
                ·
                  refine ⟨4640231107095586462040453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3093487404730390974693635 4640231107095586462040453)
                  ·
                    refine ⟨870043332580422461632585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4640231107095586462040453 870043332580422461632585)
                    ·
                      rfl

theorem cell22_2541605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_2541605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541605 prefixEnd_2541605 := by exact prefixLift 2541605
  have htrace : WordTrace (prefixWord ++ tailWord_2541605) baseStart_2541605 baseEnd_2541605 := by
    simpa [prefixWord, tailWord_2541605, baseEnd_2541605] using wordTrace_append hprefix tailTrace_2541605
  have hstable : (prefixWord ++ tailWord_2541605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541605).length < 2 ^ (prefixWord ++ tailWord_2541605).sum := by decide
  have hdescent : baseEnd_2541605 < baseStart_2541605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541631 : List Nat := [1, 1, 2, 2, 3, 1, 5, 7]
def baseStart_2541631 : Nat := 118140960795 + 2541631 * 2 ^ 59
def prefixEnd_2541631 : Nat := 4983230072969 + 3 ^ 40 * 2541631 * 2
def baseEnd_2541631 : Nat := 96672470323529673386945

theorem tailTrace_2541631 : CollatzResearch.WordTrace tailWord_2541631 prefixEnd_2541631 96672470323529673386945 := by
  unfold tailWord_2541631
  simp only [CollatzResearch.WordTrace]
  refine ⟨92700898255112437861352747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61800598836741625240901831 92700898255112437861352747)
  ·
    refine ⟨139051347382668656792029121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92700898255112437861352747 139051347382668656792029121)
    ·
      refine ⟨104288510537001492594021841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139051347382668656792029121 104288510537001492594021841)
      ·
        refine ⟨78216382902751119445516381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104288510537001492594021841 78216382902751119445516381)
        ·
          refine ⟨29331143588531669792068643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78216382902751119445516381 29331143588531669792068643)
          ·
            refine ⟨43996715382797504688102965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29331143588531669792068643 43996715382797504688102965)
            ·
              refine ⟨4124692067137266064509653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43996715382797504688102965 4124692067137266064509653)
              ·
                refine ⟨96672470323529673386945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4124692067137266064509653 96672470323529673386945)
                ·
                  rfl

theorem cell22_2541631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 7].length) (baseStart_2541631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541631 prefixEnd_2541631 := by exact prefixLift 2541631
  have htrace : WordTrace (prefixWord ++ tailWord_2541631) baseStart_2541631 baseEnd_2541631 := by
    simpa [prefixWord, tailWord_2541631, baseEnd_2541631] using wordTrace_append hprefix tailTrace_2541631
  have hstable : (prefixWord ++ tailWord_2541631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541631).length < 2 ^ (prefixWord ++ tailWord_2541631).sum := by decide
  have hdescent : baseEnd_2541631 < baseStart_2541631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541654 : List Nat := [5, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_2541654 : Nat := 118140960795 + 2541654 * 2 ^ 59
def prefixEnd_2541654 : Nat := 4983230072969 + 3 ^ 40 * 2541654 * 2
def baseEnd_2541654 : Nat := 290020035427267555719145

theorem tailTrace_2541654 : CollatzResearch.WordTrace tailWord_2541654 prefixEnd_2541654 290020035427267555719145 := by
  unfold tailWord_2541654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5793858570876819549340001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61801158089352741859626677 5793858570876819549340001)
  ·
    refine ⟨4345393928157614662005001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5793858570876819549340001 4345393928157614662005001)
    ·
      refine ⟨3259045446118210996503751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4345393928157614662005001 3259045446118210996503751)
      ·
        refine ⟨4888568169177316494755627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3259045446118210996503751 4888568169177316494755627)
        ·
          refine ⟨7332852253765974742133441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4888568169177316494755627 7332852253765974742133441)
          ·
            refine ⟨5499639190324481056600081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7332852253765974742133441 5499639190324481056600081)
            ·
              refine ⟨4124729392743360792450061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5499639190324481056600081 4124729392743360792450061)
              ·
                refine ⟨1546773522278760297168773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4124729392743360792450061 1546773522278760297168773)
                ·
                  refine ⟨290020035427267555719145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546773522278760297168773 290020035427267555719145)
                  ·
                    rfl

theorem cell22_2541654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_2541654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541654 prefixEnd_2541654 := by exact prefixLift 2541654
  have htrace : WordTrace (prefixWord ++ tailWord_2541654) baseStart_2541654 baseEnd_2541654 := by
    simpa [prefixWord, tailWord_2541654, baseEnd_2541654] using wordTrace_append hprefix tailTrace_2541654
  have hstable : (prefixWord ++ tailWord_2541654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541654).length < 2 ^ (prefixWord ++ tailWord_2541654).sum := by decide
  have hdescent : baseEnd_2541654 < baseStart_2541654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541680 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 3, 3]
def baseStart_2541680 : Nat := 118140960795 + 2541680 * 2 ^ 59
def prefixEnd_2541680 : Nat := 4983230072969 + 3 ^ 40 * 2541680 * 2
def baseEnd_2541680 : Nat := 870069006613147266007355

theorem tailTrace_2541680 : CollatzResearch.WordTrace tailWord_2541680 prefixEnd_2541680 870069006613147266007355 := by
  unfold tailWord_2541680
  simp only [CollatzResearch.WordTrace]
  refine ⟨46351342715967459614943247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61801790287956612819924329 46351342715967459614943247)
  ·
    refine ⟨69527014073951189422414871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46351342715967459614943247 69527014073951189422414871)
    ·
      refine ⟨104290521110926784133622307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69527014073951189422414871 104290521110926784133622307)
      ·
        refine ⟨156435781666390176200433461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104290521110926784133622307 156435781666390176200433461)
        ·
          refine ⟨14665854531224079018790637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156435781666390176200433461 14665854531224079018790637)
          ·
            refine ⟨5499695449209029632046489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14665854531224079018790637 5499695449209029632046489)
            ·
              refine ⟨4124771586906772224034867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5499695449209029632046489 4124771586906772224034867)
              ·
                refine ⟨6187157380360158336052301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124771586906772224034867 6187157380360158336052301)
                ·
                  refine ⟨2320184017635059376019613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6187157380360158336052301 2320184017635059376019613)
                  ·
                    refine ⟨870069006613147266007355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320184017635059376019613 870069006613147266007355)
                    ·
                      rfl

theorem cell22_2541680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3, 3].length) (baseStart_2541680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541680 prefixEnd_2541680 := by exact prefixLift 2541680
  have htrace : WordTrace (prefixWord ++ tailWord_2541680) baseStart_2541680 baseEnd_2541680 := by
    simpa [prefixWord, tailWord_2541680, baseEnd_2541680] using wordTrace_append hprefix tailTrace_2541680
  have hstable : (prefixWord ++ tailWord_2541680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541680).length < 2 ^ (prefixWord ++ tailWord_2541680).sum := by decide
  have hdescent : baseEnd_2541680 < baseStart_2541680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541721 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 8]
def baseStart_2541721 : Nat := 118140960795 + 2541721 * 2 ^ 59
def prefixEnd_2541721 : Nat := 4983230072969 + 3 ^ 40 * 2541721 * 2
def baseEnd_2541721 : Nat := 290027680583678941910743

theorem tailTrace_2541721 : CollatzResearch.WordTrace tailWord_2541721 prefixEnd_2541721 290027680583678941910743 := by
  unfold tailWord_2541721
  simp only [CollatzResearch.WordTrace]
  refine ⟨92704180824786383232129017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61802787216524255488086011 92704180824786383232129017)
  ·
    refine ⟨69528135618589787424096763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92704180824786383232129017 69528135618589787424096763)
    ·
      refine ⟨104292203427884681136145145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69528135618589787424096763 104292203427884681136145145)
      ·
        refine ⟨78219152570913510852108859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104292203427884681136145145 78219152570913510852108859)
        ·
          refine ⟨117328728856370266278163289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78219152570913510852108859 117328728856370266278163289)
          ·
            refine ⟨87996546642277699708622467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117328728856370266278163289 87996546642277699708622467)
            ·
              refine ⟨131994819963416549562933701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87996546642277699708622467 131994819963416549562933701)
              ·
                refine ⟨24749028743140603043050069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131994819963416549562933701 24749028743140603043050069)
                ·
                  refine ⟨290027680583678941910743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24749028743140603043050069 290027680583678941910743)
                  ·
                    rfl

theorem cell22_2541721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_2541721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541721 prefixEnd_2541721 := by exact prefixLift 2541721
  have htrace : WordTrace (prefixWord ++ tailWord_2541721) baseStart_2541721 baseEnd_2541721 := by
    simpa [prefixWord, tailWord_2541721, baseEnd_2541721] using wordTrace_append hprefix tailTrace_2541721
  have hstable : (prefixWord ++ tailWord_2541721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541721).length < 2 ^ (prefixWord ++ tailWord_2541721).sum := by decide
  have hdescent : baseEnd_2541721 < baseStart_2541721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541723 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 1, 4]
def baseStart_2541723 : Nat := 118140960795 + 2541723 * 2 ^ 59
def prefixEnd_2541723 : Nat := 4983230072969 + 3 ^ 40 * 2541723 * 2
def baseEnd_2541723 : Nat := 870083726391909487182223

theorem tailTrace_2541723 : CollatzResearch.WordTrace tailWord_2541723 prefixEnd_2541723 870083726391909487182223 := by
  unfold tailWord_2541723
  simp only [CollatzResearch.WordTrace]
  refine ⟨92704253770779137573701823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61802835847186091715801215 92704253770779137573701823)
  ·
    refine ⟨139056380656168706360552735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92704253770779137573701823 139056380656168706360552735)
    ·
      refine ⟨208584570984253059540829103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139056380656168706360552735 208584570984253059540829103)
      ·
        refine ⟨312876856476379589311243655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208584570984253059540829103 312876856476379589311243655)
        ·
          refine ⟨469315284714569383966865483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312876856476379589311243655 469315284714569383966865483)
          ·
            refine ⟨703972927071854075950298225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469315284714569383966865483 703972927071854075950298225)
            ·
              refine ⟨527979695303890556962723669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703972927071854075950298225 527979695303890556962723669)
              ·
                refine ⟨3093631027171233732203459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 527979695303890556962723669 3093631027171233732203459)
                ·
                  refine ⟨4640446540756850598305189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3093631027171233732203459 4640446540756850598305189)
                  ·
                    refine ⟨870083726391909487182223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4640446540756850598305189 870083726391909487182223)
                    ·
                      rfl

theorem cell22_2541723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 4].length) (baseStart_2541723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541723 prefixEnd_2541723 := by exact prefixLift 2541723
  have htrace : WordTrace (prefixWord ++ tailWord_2541723) baseStart_2541723 baseEnd_2541723 := by
    simpa [prefixWord, tailWord_2541723, baseEnd_2541723] using wordTrace_append hprefix tailTrace_2541723
  have hstable : (prefixWord ++ tailWord_2541723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541723).length < 2 ^ (prefixWord ++ tailWord_2541723).sum := by decide
  have hdescent : baseEnd_2541723 < baseStart_2541723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541753 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_2541753 : Nat := 118140960795 + 2541753 * 2 ^ 59
def prefixEnd_2541753 : Nat := 4983230072969 + 3 ^ 40 * 2541753 * 2
def baseEnd_2541753 : Nat := 870093996004999408932131

theorem tailTrace_2541753 : CollatzResearch.WordTrace tailWord_2541753 prefixEnd_2541753 870093996004999408932131 := by
  unfold tailWord_2541753
  simp only [CollatzResearch.WordTrace]
  refine ⟨92705347960670452697293913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61803565307113635131529275 92705347960670452697293913)
  ·
    refine ⟨69529010970502839522970435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92705347960670452697293913 69529010970502839522970435)
    ·
      refine ⟨104293516455754259284455653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69529010970502839522970435 104293516455754259284455653)
      ·
        refine ⟨19555034335453923615835435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104293516455754259284455653 19555034335453923615835435)
        ·
          refine ⟨29332551503180885423753153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19555034335453923615835435 29332551503180885423753153)
          ·
            refine ⟨21999413627385664067814865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29332551503180885423753153 21999413627385664067814865)
            ·
              refine ⟨16499560220539248050861149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21999413627385664067814865 16499560220539248050861149)
              ·
                refine ⟨6187335082702218019072931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16499560220539248050861149 6187335082702218019072931)
                ·
                  refine ⟨9281002624053327028609397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6187335082702218019072931 9281002624053327028609397)
                  ·
                    refine ⟨870093996004999408932131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9281002624053327028609397 870093996004999408932131)
                    ·
                      rfl

theorem cell22_2541753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_2541753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541753 prefixEnd_2541753 := by exact prefixLift 2541753
  have htrace : WordTrace (prefixWord ++ tailWord_2541753) baseStart_2541753 baseEnd_2541753 := by
    simpa [prefixWord, tailWord_2541753, baseEnd_2541753] using wordTrace_append hprefix tailTrace_2541753
  have hstable : (prefixWord ++ tailWord_2541753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541753).length < 2 ^ (prefixWord ++ tailWord_2541753).sum := by decide
  have hdescent : baseEnd_2541753 < baseStart_2541753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541789 : List Nat := [1, 4, 3, 2, 1, 1, 4, 2, 4]
def baseStart_2541789 : Nat := 118140960795 + 2541789 * 2 ^ 59
def prefixEnd_2541789 : Nat := 4983230072969 + 3 ^ 40 * 2541789 * 2
def baseEnd_2541789 : Nat := 290035439846902438344007

theorem tailTrace_2541789 : CollatzResearch.WordTrace tailWord_2541789 prefixEnd_2541789 290035439846902438344007 := by
  unfold tailWord_2541789
  simp only [CollatzResearch.WordTrace]
  refine ⟨92706660988540030845604421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61804440659026687230402947 92706660988540030845604421)
  ·
    refine ⟨17382498935351255783550829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92706660988540030845604421 17382498935351255783550829)
    ·
      refine ⟨6518437100756720918831561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17382498935351255783550829 6518437100756720918831561)
      ·
        refine ⟨4888827825567540689123671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6518437100756720918831561 4888827825567540689123671)
        ·
          refine ⟨7333241738351311033685507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4888827825567540689123671 7333241738351311033685507)
          ·
            refine ⟨10999862607526966550528261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7333241738351311033685507 10999862607526966550528261)
            ·
              refine ⟨2062474238911306228224049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10999862607526966550528261 2062474238911306228224049)
              ·
                refine ⟨1546855679183479671168037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2062474238911306228224049 1546855679183479671168037)
                ·
                  refine ⟨290035439846902438344007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546855679183479671168037 290035439846902438344007)
                  ·
                    rfl

theorem cell22_2541789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_2541789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541789 prefixEnd_2541789 := by exact prefixLift 2541789
  have htrace : WordTrace (prefixWord ++ tailWord_2541789) baseStart_2541789 baseEnd_2541789 := by
    simpa [prefixWord, tailWord_2541789, baseEnd_2541789] using wordTrace_append hprefix tailTrace_2541789
  have hstable : (prefixWord ++ tailWord_2541789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541789).length < 2 ^ (prefixWord ++ tailWord_2541789).sum := by decide
  have hdescent : baseEnd_2541789 < baseStart_2541789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541800 : List Nat := [2, 1, 4, 1, 2, 4, 1, 7]
def baseStart_2541800 : Nat := 118140960795 + 2541800 * 2 ^ 59
def prefixEnd_2541800 : Nat := 4983230072969 + 3 ^ 40 * 2541800 * 2
def baseEnd_2541800 : Nat := 96678898340611883667443

theorem tailTrace_2541800 : CollatzResearch.WordTrace tailWord_2541800 prefixEnd_2541800 96678898340611883667443 := by
  unfold tailWord_2541800
  simp only [CollatzResearch.WordTrace]
  refine ⟨46353531095750089862127427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61804708127666786482836569 46353531095750089862127427)
  ·
    refine ⟨69530296643625134793191141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46353531095750089862127427 69530296643625134793191141)
    ·
      refine ⟨13036930620679712773723339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69530296643625134793191141 13036930620679712773723339)
      ·
        refine ⟨19555395931019569160585009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13036930620679712773723339 19555395931019569160585009)
        ·
          refine ⟨14666546948264676870438757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19555395931019569160585009 14666546948264676870438757)
          ·
            refine ⟨2749977552799626913207267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14666546948264676870438757 2749977552799626913207267)
            ·
              refine ⟨4124966329199440369810901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749977552799626913207267 4124966329199440369810901)
              ·
                refine ⟨96678898340611883667443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4124966329199440369810901 96678898340611883667443)
                ·
                  rfl

theorem cell22_2541800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 7].length) (baseStart_2541800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541800 prefixEnd_2541800 := by exact prefixLift 2541800
  have htrace : WordTrace (prefixWord ++ tailWord_2541800) baseStart_2541800 baseEnd_2541800 := by
    simpa [prefixWord, tailWord_2541800, baseEnd_2541800] using wordTrace_append hprefix tailTrace_2541800
  have hstable : (prefixWord ++ tailWord_2541800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541800).length < 2 ^ (prefixWord ++ tailWord_2541800).sum := by decide
  have hdescent : baseEnd_2541800 < baseStart_2541800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541845 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 5]
def baseStart_2541845 : Nat := 118140960795 + 2541845 * 2 ^ 59
def prefixEnd_2541845 : Nat := 4983230072969 + 3 ^ 40 * 2541845 * 2
def baseEnd_2541845 : Nat := 290041829828380611877283

theorem tailTrace_2541845 : CollatzResearch.WordTrace tailWord_2541845 prefixEnd_2541845 290041829828380611877283 := by
  unfold tailWord_2541845
  simp only [CollatzResearch.WordTrace]
  refine ⟨92708703476337152409642989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61805802317558101606428659 92708703476337152409642989)
  ·
    refine ⟨34765763803626432153616121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92708703476337152409642989 34765763803626432153616121)
    ·
      refine ⟨26074322852719824115212091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34765763803626432153616121 26074322852719824115212091)
      ·
        refine ⟨39111484279079736172818137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26074322852719824115212091 39111484279079736172818137)
        ·
          refine ⟨29333613209309802129613603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39111484279079736172818137 29333613209309802129613603)
          ·
            refine ⟨44000419813964703194420405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29333613209309802129613603 44000419813964703194420405)
            ·
              refine ⟨4125039357559190924476913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44000419813964703194420405 4125039357559190924476913)
              ·
                refine ⟨3093779518169393193357685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4125039357559190924476913 3093779518169393193357685)
                ·
                  refine ⟨290041829828380611877283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3093779518169393193357685 290041829828380611877283)
                  ·
                    rfl

theorem cell22_2541845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_2541845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541845 prefixEnd_2541845 := by exact prefixLift 2541845
  have htrace : WordTrace (prefixWord ++ tailWord_2541845) baseStart_2541845 baseEnd_2541845 := by
    simpa [prefixWord, tailWord_2541845, baseEnd_2541845] using wordTrace_append hprefix tailTrace_2541845
  have hstable : (prefixWord ++ tailWord_2541845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541845).length < 2 ^ (prefixWord ++ tailWord_2541845).sum := by decide
  have hdescent : baseEnd_2541845 < baseStart_2541845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541860 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_2541860 : Nat := 118140960795 + 2541860 * 2 ^ 59
def prefixEnd_2541860 : Nat := 4983230072969 + 3 ^ 40 * 2541860 * 2
def baseEnd_2541860 : Nat := 870130624291686796506803

theorem tailTrace_2541860 : CollatzResearch.WordTrace tailWord_2541860 prefixEnd_2541860 870130624291686796506803 := by
  unfold tailWord_2541860
  simp only [CollatzResearch.WordTrace]
  refine ⟨46354625285641404985719517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61806167047521873314292689 46354625285641404985719517)
  ·
    refine ⟨17382984482115526869644819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46354625285641404985719517 17382984482115526869644819)
    ·
      refine ⟨26074476723173290304467229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17382984482115526869644819 26074476723173290304467229)
      ·
        refine ⟨9777928771189983864175211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26074476723173290304467229 9777928771189983864175211)
        ·
          refine ⟨14666893156784975796262817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9777928771189983864175211 14666893156784975796262817)
          ·
            refine ⟨11000169867588731847197113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14666893156784975796262817 11000169867588731847197113)
            ·
              refine ⟨8250127400691548885397835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11000169867588731847197113 8250127400691548885397835)
              ·
                refine ⟨12375191101037323328096753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8250127400691548885397835 12375191101037323328096753)
                ·
                  refine ⟨9281393325777992496072565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12375191101037323328096753 9281393325777992496072565)
                  ·
                    refine ⟨870130624291686796506803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9281393325777992496072565 870130624291686796506803)
                    ·
                      rfl

theorem cell22_2541860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_2541860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541860 prefixEnd_2541860 := by exact prefixLift 2541860
  have htrace : WordTrace (prefixWord ++ tailWord_2541860) baseStart_2541860 baseEnd_2541860 := by
    simpa [prefixWord, tailWord_2541860, baseEnd_2541860] using wordTrace_append hprefix tailTrace_2541860
  have hstable : (prefixWord ++ tailWord_2541860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541860).length < 2 ^ (prefixWord ++ tailWord_2541860).sum := by decide
  have hdescent : baseEnd_2541860 < baseStart_2541860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541903 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 3, 6]
def baseStart_2541903 : Nat := 118140960795 + 2541903 * 2 ^ 59
def prefixEnd_2541903 : Nat := 4983230072969 + 3 ^ 40 * 2541903 * 2
def baseEnd_2541903 : Nat := 870145344070449017681671

theorem tailTrace_2541903 : CollatzResearch.WordTrace tailWord_2541903 prefixEnd_2541903 870145344070449017681671 := by
  unfold tailWord_2541903
  simp only [CollatzResearch.WordTrace]
  refine ⟨92710818910127028315254363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61807212606751352210169575 92710818910127028315254363)
  ·
    refine ⟨139066228365190542472881545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92710818910127028315254363 139066228365190542472881545)
    ·
      refine ⟨104299671273892906854661159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139066228365190542472881545 104299671273892906854661159)
      ·
        refine ⟨156449506910839360281991739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104299671273892906854661159 156449506910839360281991739)
        ·
          refine ⟨234674260366259040422987609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156449506910839360281991739 234674260366259040422987609)
          ·
            refine ⟨176005695274694280317240707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234674260366259040422987609 176005695274694280317240707)
            ·
              refine ⟨264008542912041420475861061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176005695274694280317240707 264008542912041420475861061)
              ·
                refine ⟨49501601796007766339223949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264008542912041420475861061 49501601796007766339223949)
                ·
                  refine ⟨18563100673502912377208981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49501601796007766339223949 18563100673502912377208981)
                  ·
                    refine ⟨870145344070449017681671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18563100673502912377208981 870145344070449017681671)
                    ·
                      rfl

theorem cell22_2541903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_2541903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2541903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2541903 prefixEnd_2541903 := by exact prefixLift 2541903
  have htrace : WordTrace (prefixWord ++ tailWord_2541903) baseStart_2541903 baseEnd_2541903 := by
    simpa [prefixWord, tailWord_2541903, baseEnd_2541903] using wordTrace_append hprefix tailTrace_2541903
  have hstable : (prefixWord ++ tailWord_2541903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541903).length < 2 ^ (prefixWord ++ tailWord_2541903).sum := by decide
  have hdescent : baseEnd_2541903 < baseStart_2541903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542001 : List Nat := [1, 2, 2, 4, 1, 3, 2, 3, 1, 3]
def baseStart_2542001 : Nat := 118140960795 + 2542001 * 2 ^ 59
def prefixEnd_2542001 : Nat := 4983230072969 + 3 ^ 40 * 2542001 * 2
def baseEnd_2542001 : Nat := 870178891473209428731371

theorem tailTrace_2542001 : CollatzResearch.WordTrace tailWord_2542001 prefixEnd_2542001 870178891473209428731371 := by
  unfold tailWord_2542001
  simp only [CollatzResearch.WordTrace]
  refine ⟨92714393263771991052321857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61809595509181327368214571 92714393263771991052321857)
  ·
    refine ⟨69535794947828993289241393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92714393263771991052321857 69535794947828993289241393)
    ·
      refine ⟨52151846210871744966931045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69535794947828993289241393 52151846210871744966931045)
      ·
        refine ⟨9778471164538452181299571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52151846210871744966931045 9778471164538452181299571)
        ·
          refine ⟨14667706746807678271949357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9778471164538452181299571 14667706746807678271949357)
          ·
            refine ⟨5500390030052879351981009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14667706746807678271949357 5500390030052879351981009)
            ·
              refine ⟨4125292522539659513985757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5500390030052879351981009 4125292522539659513985757)
              ·
                refine ⟨1546984695952372317744659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4125292522539659513985757 1546984695952372317744659)
                ·
                  refine ⟨2320477043928558476616989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1546984695952372317744659 2320477043928558476616989)
                  ·
                    refine ⟨870178891473209428731371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320477043928558476616989 870178891473209428731371)
                    ·
                      rfl

theorem cell22_2542001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_2542001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542001 prefixEnd_2542001 := by exact prefixLift 2542001
  have htrace : WordTrace (prefixWord ++ tailWord_2542001) baseStart_2542001 baseEnd_2542001 := by
    simpa [prefixWord, tailWord_2542001, baseEnd_2542001] using wordTrace_append hprefix tailTrace_2542001
  have hstable : (prefixWord ++ tailWord_2542001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542001).length < 2 ^ (prefixWord ++ tailWord_2542001).sum := by decide
  have hdescent : baseEnd_2542001 < baseStart_2542001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542012 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_2542012 : Nat := 118140960795 + 2542012 * 2 ^ 59
def prefixEnd_2542012 : Nat := 4983230072969 + 3 ^ 40 * 2542012 * 2
def baseEnd_2542012 : Nat := 870182656998009066706337

theorem tailTrace_2542012 : CollatzResearch.WordTrace tailWord_2542012 prefixEnd_2542012 870182656998009066706337 := by
  unfold tailWord_2542012
  simp only [CollatzResearch.WordTrace]
  refine ⟨46357397233366069965486145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61809862977821426620648193 46357397233366069965486145)
  ·
    refine ⟨34768047925024552474114609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46357397233366069965486145 34768047925024552474114609)
    ·
      refine ⟨26076035943768414355585957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34768047925024552474114609 26076035943768414355585957)
      ·
        refine ⟨4889256739456577691672367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26076035943768414355585957 4889256739456577691672367)
        ·
          refine ⟨7333885109184866537508551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4889256739456577691672367 7333885109184866537508551)
          ·
            refine ⟨11000827663777299806262827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7333885109184866537508551 11000827663777299806262827)
            ·
              refine ⟨16501241495665949709394241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11000827663777299806262827 16501241495665949709394241)
              ·
                refine ⟨12375931121749462282045681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16501241495665949709394241 12375931121749462282045681)
                ·
                  refine ⟨9281948341312096711534261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12375931121749462282045681 9281948341312096711534261)
                  ·
                    refine ⟨870182656998009066706337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9281948341312096711534261 870182656998009066706337)
                    ·
                      rfl

theorem cell22_2542012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_2542012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542012 prefixEnd_2542012 := by exact prefixLift 2542012
  have htrace : WordTrace (prefixWord ++ tailWord_2542012) baseStart_2542012 baseEnd_2542012 := by
    simpa [prefixWord, tailWord_2542012, baseEnd_2542012] using wordTrace_append hprefix tailTrace_2542012
  have hstable : (prefixWord ++ tailWord_2542012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542012).length < 2 ^ (prefixWord ++ tailWord_2542012).sum := by decide
  have hdescent : baseEnd_2542012 < baseStart_2542012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542025 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 6]
def baseStart_2542025 : Nat := 118140960795 + 2542025 * 2 ^ 59
def prefixEnd_2542025 : Nat := 4983230072969 + 3 ^ 40 * 2542025 * 2
def baseEnd_2542025 : Nat := 290062369054560455377099

theorem tailTrace_2542025 : CollatzResearch.WordTrace tailWord_2542025 prefixEnd_2542025 290062369054560455377099 := by
  unfold tailWord_2542025
  simp only [CollatzResearch.WordTrace]
  refine ⟨92715268615685043151195529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61810179077123362100797019 92715268615685043151195529)
  ·
    refine ⟨69536451461763782363396647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92715268615685043151195529 69536451461763782363396647)
    ·
      refine ⟨104304677192645673545094971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69536451461763782363396647 104304677192645673545094971)
      ·
        refine ⟨156457015788968510317642457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104304677192645673545094971 156457015788968510317642457)
        ·
          refine ⟨117342761841726382738231843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156457015788968510317642457 117342761841726382738231843)
          ·
            refine ⟨176014142762589574107347765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117342761841726382738231843 176014142762589574107347765)
            ·
              refine ⟨16501325883992772572563853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176014142762589574107347765 16501325883992772572563853)
              ·
                refine ⟨6187997206497289714711445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16501325883992772572563853 6187997206497289714711445)
                ·
                  refine ⟨290062369054560455377099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6187997206497289714711445 290062369054560455377099)
                  ·
                    rfl

theorem cell22_2542025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_2542025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542025 prefixEnd_2542025 := by exact prefixLift 2542025
  have htrace : WordTrace (prefixWord ++ tailWord_2542025) baseStart_2542025 baseEnd_2542025 := by
    simpa [prefixWord, tailWord_2542025, baseEnd_2542025] using wordTrace_append hprefix tailTrace_2542025
  have hstable : (prefixWord ++ tailWord_2542025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542025).length < 2 ^ (prefixWord ++ tailWord_2542025).sum := by decide
  have hdescent : baseEnd_2542025 < baseStart_2542025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542072 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_2542072 : Nat := 118140960795 + 2542072 * 2 ^ 59
def prefixEnd_2542072 : Nat := 4983230072969 + 3 ^ 40 * 2542072 * 2
def baseEnd_2542072 : Nat := 870203196224188910206153

theorem tailTrace_2542072 : CollatzResearch.WordTrace tailWord_2542072 prefixEnd_2542072 870203196224188910206153 := by
  unfold tailWord_2542072
  simp only [CollatzResearch.WordTrace]
  refine ⟨46358491423257385089078235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61811321897676513452104313 46358491423257385089078235)
  ·
    refine ⟨69537737134886077633617353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46358491423257385089078235 69537737134886077633617353)
    ·
      refine ⟨52153302851164558225213015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69537737134886077633617353 52153302851164558225213015)
      ·
        refine ⟨78229954276746837337819523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52153302851164558225213015 78229954276746837337819523)
        ·
          refine ⟨117344931415120256006729285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78229954276746837337819523 117344931415120256006729285)
          ·
            refine ⟨22002174640335048001261741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117344931415120256006729285 22002174640335048001261741)
            ·
              refine ⟨8250815490125643000473153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22002174640335048001261741 8250815490125643000473153)
              ·
                refine ⟨6188111617594232250354865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8250815490125643000473153 6188111617594232250354865)
                ·
                  refine ⟨4641083713195674187766149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6188111617594232250354865 4641083713195674187766149)
                  ·
                    refine ⟨870203196224188910206153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641083713195674187766149 870203196224188910206153)
                    ·
                      rfl

theorem cell22_2542072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_2542072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542072 prefixEnd_2542072 := by exact prefixLift 2542072
  have htrace : WordTrace (prefixWord ++ tailWord_2542072) baseStart_2542072 baseEnd_2542072 := by
    simpa [prefixWord, tailWord_2542072, baseEnd_2542072] using wordTrace_append hprefix tailTrace_2542072
  have hstable : (prefixWord ++ tailWord_2542072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542072).length < 2 ^ (prefixWord ++ tailWord_2542072).sum := by decide
  have hdescent : baseEnd_2542072 < baseStart_2542072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542091 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 2, 3]
def baseStart_2542091 : Nat := 118140960795 + 2542091 * 2 ^ 59
def prefixEnd_2542091 : Nat := 4983230072969 + 3 ^ 40 * 2542091 * 2
def baseEnd_2542091 : Nat := 870209700312479193981095

theorem tailTrace_2542091 : CollatzResearch.WordTrace tailWord_2542091 prefixEnd_2542091 870209700312479193981095 := by
  unfold tailWord_2542091
  simp only [CollatzResearch.WordTrace]
  refine ⟨92717675833445936423098127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61811783888963957615398751 92717675833445936423098127)
  ·
    refine ⟨139076513750168904634647191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92717675833445936423098127 139076513750168904634647191)
    ·
      refine ⟨208614770625253356951970787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139076513750168904634647191 208614770625253356951970787)
      ·
        refine ⟨312922155937880035427956181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208614770625253356951970787 312922155937880035427956181)
        ·
          refine ⟨7334113029794063330342723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 312922155937880035427956181 7334113029794063330342723)
          ·
            refine ⟨11001169544691094995514085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7334113029794063330342723 11001169544691094995514085)
            ·
              refine ⟨2062719289629580311658891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11001169544691094995514085 2062719289629580311658891)
              ·
                refine ⟨3094078934444370467488337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062719289629580311658891 3094078934444370467488337)
                ·
                  refine ⟨2320559200833277850616253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3094078934444370467488337 2320559200833277850616253)
                  ·
                    refine ⟨870209700312479193981095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320559200833277850616253 870209700312479193981095)
                    ·
                      rfl

theorem cell22_2542091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 2, 3].length) (baseStart_2542091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542091 prefixEnd_2542091 := by exact prefixLift 2542091
  have htrace : WordTrace (prefixWord ++ tailWord_2542091) baseStart_2542091 baseEnd_2542091 := by
    simpa [prefixWord, tailWord_2542091, baseEnd_2542091] using wordTrace_append hprefix tailTrace_2542091
  have hstable : (prefixWord ++ tailWord_2542091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542091).length < 2 ^ (prefixWord ++ tailWord_2542091).sum := by decide
  have hdescent : baseEnd_2542091 < baseStart_2542091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542134 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2542134 : Nat := 118140960795 + 2542134 * 2 ^ 59
def prefixEnd_2542134 : Nat := 4983230072969 + 3 ^ 40 * 2542134 * 2
def baseEnd_2542134 : Nat := 870224420091241415155963

theorem tailTrace_2542134 : CollatzResearch.WordTrace tailWord_2542134 prefixEnd_2542134 870224420091241415155963 := by
  unfold tailWord_2542134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5794952760768134672932091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61812829448193436511275637 5794952760768134672932091)
  ·
    refine ⟨8692429141152202009398137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5794952760768134672932091 8692429141152202009398137)
    ·
      refine ⟨6519321855864151507048603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8692429141152202009398137 6519321855864151507048603)
      ·
        refine ⟨9778982783796227260572905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6519321855864151507048603 9778982783796227260572905)
        ·
          refine ⟨7334237087847170445429679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9778982783796227260572905 7334237087847170445429679)
          ·
            refine ⟨11001355631770755668144519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7334237087847170445429679 11001355631770755668144519)
            ·
              refine ⟨16502033447656133502216779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11001355631770755668144519 16502033447656133502216779)
              ·
                refine ⟨24753050171484200253325169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16502033447656133502216779 24753050171484200253325169)
                ·
                  refine ⟨18564787628613150189993877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24753050171484200253325169 18564787628613150189993877)
                  ·
                    refine ⟨870224420091241415155963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18564787628613150189993877 870224420091241415155963)
                    ·
                      rfl

theorem cell22_2542134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2542134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542134 prefixEnd_2542134 := by exact prefixLift 2542134
  have htrace : WordTrace (prefixWord ++ tailWord_2542134) baseStart_2542134 baseEnd_2542134 := by
    simpa [prefixWord, tailWord_2542134, baseEnd_2542134] using wordTrace_append hprefix tailTrace_2542134
  have hstable : (prefixWord ++ tailWord_2542134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542134).length < 2 ^ (prefixWord ++ tailWord_2542134).sum := by decide
  have hdescent : baseEnd_2542134 < baseStart_2542134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542136 : List Nat := [2, 1, 2, 1, 4, 1, 3, 4, 1, 3]
def baseStart_2542136 : Nat := 118140960795 + 2542136 * 2 ^ 59
def prefixEnd_2542136 : Nat := 4983230072969 + 3 ^ 40 * 2542136 * 2
def baseEnd_2542136 : Nat := 870225104732114076605957

theorem tailTrace_2542136 : CollatzResearch.WordTrace tailWord_2542136 prefixEnd_2542136 870225104732114076605957 := by
  unfold tailWord_2542136
  simp only [CollatzResearch.WordTrace]
  refine ⟨46359658559141454554243131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61812878078855272738990841 46359658559141454554243131)
  ·
    refine ⟨69539487838712181831364697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46359658559141454554243131 69539487838712181831364697)
    ·
      refine ⟨52154615879034136373523523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69539487838712181831364697 52154615879034136373523523)
      ·
        refine ⟨78231923818551204560285285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52154615879034136373523523 78231923818551204560285285)
        ·
          refine ⟨14668485715978350855053491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78231923818551204560285285 14668485715978350855053491)
          ·
            refine ⟨22002728573967526282580237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14668485715978350855053491 22002728573967526282580237)
            ·
              refine ⟨8251023215237822355967589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22002728573967526282580237 8251023215237822355967589)
              ·
                refine ⟨1547066852857091691743923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8251023215237822355967589 1547066852857091691743923)
                ·
                  refine ⟨2320600279285637537615885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547066852857091691743923 2320600279285637537615885)
                  ·
                    refine ⟨870225104732114076605957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320600279285637537615885 870225104732114076605957)
                    ·
                      rfl

theorem cell22_2542136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_2542136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542136 prefixEnd_2542136 := by exact prefixLift 2542136
  have htrace : WordTrace (prefixWord ++ tailWord_2542136) baseStart_2542136 baseEnd_2542136 := by
    simpa [prefixWord, tailWord_2542136, baseEnd_2542136] using wordTrace_append hprefix tailTrace_2542136
  have hstable : (prefixWord ++ tailWord_2542136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542136).length < 2 ^ (prefixWord ++ tailWord_2542136).sum := by decide
  have hdescent : baseEnd_2542136 < baseStart_2542136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542179 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 1, 4]
def baseStart_2542179 : Nat := 118140960795 + 2542179 * 2 ^ 59
def prefixEnd_2542179 : Nat := 4983230072969 + 3 ^ 40 * 2542179 * 2
def baseEnd_2542179 : Nat := 870239824510876297780825

theorem tailTrace_2542179 : CollatzResearch.WordTrace tailWord_2542179 prefixEnd_2542179 870239824510876297780825 := by
  unfold tailWord_2542179
  simp only [CollatzResearch.WordTrace]
  refine ⟨92720885457127127452301591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61813923638084751634867727 92720885457127127452301591)
  ·
    refine ⟨139081328185690691178452387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92720885457127127452301591 139081328185690691178452387)
    ·
      refine ⟨208621992278536036767678581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139081328185690691178452387 208621992278536036767678581)
      ·
        refine ⟨19558311776112753446969867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208621992278536036767678581 19558311776112753446969867)
        ·
          refine ⟨29337467664169130170454801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19558311776112753446969867 29337467664169130170454801)
          ·
            refine ⟨22003100748126847627841101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29337467664169130170454801 22003100748126847627841101)
            ·
              refine ⟨8251162780547567860440413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22003100748126847627841101 8251162780547567860440413)
              ·
                refine ⟨3094186042705337947665155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8251162780547567860440413 3094186042705337947665155)
                ·
                  refine ⟨4641279064058006921497733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094186042705337947665155 4641279064058006921497733)
                  ·
                    refine ⟨870239824510876297780825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641279064058006921497733 870239824510876297780825)
                    ·
                      rfl

theorem cell22_2542179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 4].length) (baseStart_2542179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542179 prefixEnd_2542179 := by exact prefixLift 2542179
  have htrace : WordTrace (prefixWord ++ tailWord_2542179) baseStart_2542179 baseEnd_2542179 := by
    simpa [prefixWord, tailWord_2542179, baseEnd_2542179] using wordTrace_append hprefix tailTrace_2542179
  have hstable : (prefixWord ++ tailWord_2542179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542179).length < 2 ^ (prefixWord ++ tailWord_2542179).sum := by decide
  have hdescent : baseEnd_2542179 < baseStart_2542179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542207 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 6, 4]
def baseStart_2542207 : Nat := 118140960795 + 2542207 * 2 ^ 59
def prefixEnd_2542207 : Nat := 4983230072969 + 3 ^ 40 * 2542207 * 2
def baseEnd_2542207 : Nat := 870249409483093558080739

theorem tailTrace_2542207 : CollatzResearch.WordTrace tailWord_2542207 prefixEnd_2542207 870249409483093558080739 := by
  unfold tailWord_2542207
  simp only [CollatzResearch.WordTrace]
  refine ⟨92721906701025688234320875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61814604467350458822880583 92721906701025688234320875)
  ·
    refine ⟨139082860051538532351481313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92721906701025688234320875 139082860051538532351481313)
    ·
      refine ⟨104312145038653899263610985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139082860051538532351481313 104312145038653899263610985)
      ·
        refine ⟨78234108778990424447708239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104312145038653899263610985 78234108778990424447708239)
        ·
          refine ⟨117351163168485636671562359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78234108778990424447708239 117351163168485636671562359)
          ·
            refine ⟨176026744752728455007343539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117351163168485636671562359 176026744752728455007343539)
            ·
              refine ⟨264040117129092682511015309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176026744752728455007343539 264040117129092682511015309)
              ·
                refine ⟨99015043923409755941630741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264040117129092682511015309 99015043923409755941630741)
                ·
                  refine ⟨4641330183909832309763941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99015043923409755941630741 4641330183909832309763941)
                  ·
                    refine ⟨870249409483093558080739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641330183909832309763941 870249409483093558080739)
                    ·
                      rfl

theorem cell22_2542207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_2542207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542207 prefixEnd_2542207 := by exact prefixLift 2542207
  have htrace : WordTrace (prefixWord ++ tailWord_2542207) baseStart_2542207 baseEnd_2542207 := by
    simpa [prefixWord, tailWord_2542207, baseEnd_2542207] using wordTrace_append hprefix tailTrace_2542207
  have hstable : (prefixWord ++ tailWord_2542207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542207).length < 2 ^ (prefixWord ++ tailWord_2542207).sum := by decide
  have hdescent : baseEnd_2542207 < baseStart_2542207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542226 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2542226 : Nat := 118140960795 + 2542226 * 2 ^ 59
def prefixEnd_2542226 : Nat := 4983230072969 + 3 ^ 40 * 2542226 * 2
def baseEnd_2542226 : Nat := 870255913571383841855681

theorem tailTrace_2542226 : CollatzResearch.WordTrace tailWord_2542226 prefixEnd_2542226 870255913571383841855681 := by
  unfold tailWord_2542226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23180649921989213619815633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61815066458637902986175021 23180649921989213619815633)
  ·
    refine ⟨17385487441491910214861725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23180649921989213619815633 17385487441491910214861725)
    ·
      refine ⟨6519557790559466330573147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17385487441491910214861725 6519557790559466330573147)
      ·
        refine ⟨9779336685839199495859721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6519557790559466330573147 9779336685839199495859721)
        ·
          refine ⟨7334502514379399621894791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9779336685839199495859721 7334502514379399621894791)
          ·
            refine ⟨11001753771569099432842187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7334502514379399621894791 11001753771569099432842187)
            ·
              refine ⟨16502630657353649149263281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11001753771569099432842187 16502630657353649149263281)
              ·
                refine ⟨12376972993015236861947461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16502630657353649149263281 12376972993015236861947461)
                ·
                  refine ⟨2320682436190356911615149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12376972993015236861947461 2320682436190356911615149)
                  ·
                    refine ⟨870255913571383841855681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320682436190356911615149 870255913571383841855681)
                    ·
                      rfl

theorem cell22_2542226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2542226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542226 prefixEnd_2542226 := by exact prefixLift 2542226
  have htrace : WordTrace (prefixWord ++ tailWord_2542226) baseStart_2542226 baseEnd_2542226 := by
    simpa [prefixWord, tailWord_2542226, baseEnd_2542226] using wordTrace_append hprefix tailTrace_2542226
  have hstable : (prefixWord ++ tailWord_2542226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542226).length < 2 ^ (prefixWord ++ tailWord_2542226).sum := by decide
  have hdescent : baseEnd_2542226 < baseStart_2542226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542228 : List Nat := [2, 4, 2, 2, 1, 1, 3, 3, 4]
def baseStart_2542228 : Nat := 118140960795 + 2542228 * 2 ^ 59
def prefixEnd_2542228 : Nat := 4983230072969 + 3 ^ 40 * 2542228 * 2
def baseEnd_2542228 : Nat := 290085532737418834435225

theorem tailTrace_2542228 : CollatzResearch.WordTrace tailWord_2542228 prefixEnd_2542228 290085532737418834435225 := by
  unfold tailWord_2542228
  simp only [CollatzResearch.WordTrace]
  refine ⟨46361336316974804410417669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61815115089299739213890225 46361336316974804410417669)
  ·
    refine ⟨8692750559432775826953313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46361336316974804410417669 8692750559432775826953313)
    ·
      refine ⟨6519562919574581870214985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8692750559432775826953313 6519562919574581870214985)
      ·
        refine ⟨4889672189680936402661239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6519562919574581870214985 4889672189680936402661239)
        ·
          refine ⟨7334508284521404603991859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4889672189680936402661239 7334508284521404603991859)
          ·
            refine ⟨11001762426782106905987789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7334508284521404603991859 11001762426782106905987789)
            ·
              refine ⟨4125660910043290089745421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11001762426782106905987789 4125660910043290089745421)
              ·
                refine ⟨1547122841266233783654533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4125660910043290089745421 1547122841266233783654533)
                ·
                  refine ⟨290085532737418834435225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547122841266233783654533 290085532737418834435225)
                  ·
                    rfl

theorem cell22_2542228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_2542228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542228 prefixEnd_2542228 := by exact prefixLift 2542228
  have htrace : WordTrace (prefixWord ++ tailWord_2542228) baseStart_2542228 baseEnd_2542228 := by
    simpa [prefixWord, tailWord_2542228, baseEnd_2542228] using wordTrace_append hprefix tailTrace_2542228
  have hstable : (prefixWord ++ tailWord_2542228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542228).length < 2 ^ (prefixWord ++ tailWord_2542228).sum := by decide
  have hdescent : baseEnd_2542228 < baseStart_2542228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542241 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 2, 4]
def baseStart_2542241 : Nat := 118140960795 + 2542241 * 2 ^ 59
def prefixEnd_2542241 : Nat := 4983230072969 + 3 ^ 40 * 2542241 * 2
def baseEnd_2542241 : Nat := 870261048377928802730635

theorem tailTrace_2542241 : CollatzResearch.WordTrace tailWord_2542241 prefixEnd_2542241 870261048377928802730635 := by
  unfold tailWord_2542241
  simp only [CollatzResearch.WordTrace]
  refine ⟨92723146782902512041058577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61815431188601674694039051 92723146782902512041058577)
  ·
    refine ⟨69542360087176884030793933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92723146782902512041058577 69542360087176884030793933)
    ·
      refine ⟨26078385032691331511547725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69542360087176884030793933 26078385032691331511547725)
      ·
        refine ⟨9779394387259249316830397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26078385032691331511547725 9779394387259249316830397)
        ·
          refine ⟨3667272895222218493811399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9779394387259249316830397 3667272895222218493811399)
          ·
            refine ⟨5500909342833327740717099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667272895222218493811399 5500909342833327740717099)
            ·
              refine ⟨8251364014249991611075649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5500909342833327740717099 8251364014249991611075649)
              ·
                refine ⟨6188523010687493708306737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8251364014249991611075649 6188523010687493708306737)
                ·
                  refine ⟨4641392258015620281230053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6188523010687493708306737 4641392258015620281230053)
                  ·
                    refine ⟨870261048377928802730635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641392258015620281230053 870261048377928802730635)
                    ·
                      rfl

theorem cell22_2542241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_2542241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542241 prefixEnd_2542241 := by exact prefixLift 2542241
  have htrace : WordTrace (prefixWord ++ tailWord_2542241) baseStart_2542241 baseEnd_2542241 := by
    simpa [prefixWord, tailWord_2542241, baseEnd_2542241] using wordTrace_append hprefix tailTrace_2542241
  have hstable : (prefixWord ++ tailWord_2542241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542241).length < 2 ^ (prefixWord ++ tailWord_2542241).sum := by decide
  have hdescent : baseEnd_2542241 < baseStart_2542241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542305 : List Nat := [1, 2, 3, 1, 4, 1, 4, 2, 1, 3]
def baseStart_2542305 : Nat := 118140960795 + 2542305 * 2 ^ 59
def prefixEnd_2542305 : Nat := 4983230072969 + 3 ^ 40 * 2542305 * 2
def baseEnd_2542305 : Nat := 870282956885853969130439

theorem tailTrace_2542305 : CollatzResearch.WordTrace tailWord_2542305 prefixEnd_2542305 870282956885853969130439 := by
  unfold tailWord_2542305
  simp only [CollatzResearch.WordTrace]
  refine ⟨92725481054670650971388369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61816987369780433980925579 92725481054670650971388369)
  ·
    refine ⟨69544110791002988228541277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92725481054670650971388369 69544110791002988228541277)
    ·
      refine ⟨26079041546626120585702979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69544110791002988228541277 26079041546626120585702979)
      ·
        refine ⟨39118562319939180878554469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26079041546626120585702979 39118562319939180878554469)
        ·
          refine ⟨7334730434988596414728963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39118562319939180878554469 7334730434988596414728963)
          ·
            refine ⟨11002095652482894622093445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7334730434988596414728963 11002095652482894622093445)
            ·
              refine ⟨2062892934840542741642521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11002095652482894622093445 2062892934840542741642521)
              ·
                refine ⟨1547169701130407056231891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2062892934840542741642521 1547169701130407056231891)
                ·
                  refine ⟨2320754551695610584347837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547169701130407056231891 2320754551695610584347837)
                  ·
                    refine ⟨870282956885853969130439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320754551695610584347837 870282956885853969130439)
                    ·
                      rfl

theorem cell22_2542305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_2542305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542305 prefixEnd_2542305 := by exact prefixLift 2542305
  have htrace : WordTrace (prefixWord ++ tailWord_2542305) baseStart_2542305 baseEnd_2542305 := by
    simpa [prefixWord, tailWord_2542305, baseEnd_2542305] using wordTrace_append hprefix tailTrace_2542305
  have hstable : (prefixWord ++ tailWord_2542305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542305).length < 2 ^ (prefixWord ++ tailWord_2542305).sum := by decide
  have hdescent : baseEnd_2542305 < baseStart_2542305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542361 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 2, 3]
def baseStart_2542361 : Nat := 118140960795 + 2542361 * 2 ^ 59
def prefixEnd_2542361 : Nat := 4983230072969 + 3 ^ 40 * 2542361 * 2
def baseEnd_2542361 : Nat := 870302126830288489730267

theorem tailTrace_2542361 : CollatzResearch.WordTrace tailWord_2542361 prefixEnd_2542361 870302126830288489730267 := by
  unfold tailWord_2542361
  simp only [CollatzResearch.WordTrace]
  refine ⟨92727523542467772535426937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61818349028311848356951291 92727523542467772535426937)
  ·
    refine ⟨69545642656850829401570203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92727523542467772535426937 69545642656850829401570203)
    ·
      refine ⟨104318463985276244102355305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69545642656850829401570203 104318463985276244102355305)
      ·
        refine ⟨78238847988957183076766479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104318463985276244102355305 78238847988957183076766479)
        ·
          refine ⟨117358271983435774615149719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78238847988957183076766479 117358271983435774615149719)
          ·
            refine ⟨176037407975153661922724579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117358271983435774615149719 176037407975153661922724579)
            ·
              refine ⟨264056111962730492884086869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176037407975153661922724579 264056111962730492884086869)
              ·
                refine ⟨3094407562063247963485393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 264056111962730492884086869 3094407562063247963485393)
                ·
                  refine ⟨2320805671547435972614045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3094407562063247963485393 2320805671547435972614045)
                  ·
                    refine ⟨870302126830288489730267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320805671547435972614045 870302126830288489730267)
                    ·
                      rfl

theorem cell22_2542361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 3].length) (baseStart_2542361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542361 prefixEnd_2542361 := by exact prefixLift 2542361
  have htrace : WordTrace (prefixWord ++ tailWord_2542361) baseStart_2542361 baseEnd_2542361 := by
    simpa [prefixWord, tailWord_2542361, baseEnd_2542361] using wordTrace_append hprefix tailTrace_2542361
  have hstable : (prefixWord ++ tailWord_2542361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542361).length < 2 ^ (prefixWord ++ tailWord_2542361).sum := by decide
  have hdescent : baseEnd_2542361 < baseStart_2542361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542397 : List Nat := [1, 4, 1, 4, 3, 1, 1, 3, 4]
def baseStart_2542397 : Nat := 118140960795 + 2542397 * 2 ^ 59
def prefixEnd_2542397 : Nat := 4983230072969 + 3 ^ 40 * 2542397 * 2
def baseEnd_2542397 : Nat := 290104816788665465276719

theorem tailTrace_2542397 : CollatzResearch.WordTrace tailWord_2542397 prefixEnd_2542397 290104816788665465276719 := by
  unfold tailWord_2542397
  simp only [CollatzResearch.WordTrace]
  refine ⟨92728836570337350683737445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61819224380224900455824963 92728836570337350683737445)
  ·
    refine ⟨17386656856938253253200771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92728836570337350683737445 17386656856938253253200771)
    ·
      refine ⟨26079985285407379879801157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17386656856938253253200771 26079985285407379879801157)
      ·
        refine ⟨4889997241013883727462717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26079985285407379879801157 4889997241013883727462717)
        ·
          refine ⟨1833748965380206397798519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4889997241013883727462717 1833748965380206397798519)
          ·
            refine ⟨2750623448070309596697779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833748965380206397798519 2750623448070309596697779)
            ·
              refine ⟨4125935172105464395046669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750623448070309596697779 4125935172105464395046669)
              ·
                refine ⟨1547225689539549148142501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4125935172105464395046669 1547225689539549148142501)
                ·
                  refine ⟨290104816788665465276719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547225689539549148142501 290104816788665465276719)
                  ·
                    rfl

theorem cell22_2542397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_2542397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542397 prefixEnd_2542397 := by exact prefixLift 2542397
  have htrace : WordTrace (prefixWord ++ tailWord_2542397) baseStart_2542397 baseEnd_2542397 := by
    simpa [prefixWord, tailWord_2542397, baseEnd_2542397] using wordTrace_append hprefix tailTrace_2542397
  have hstable : (prefixWord ++ tailWord_2542397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542397).length < 2 ^ (prefixWord ++ tailWord_2542397).sum := by decide
  have hdescent : baseEnd_2542397 < baseStart_2542397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542423 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 3, 3]
def baseStart_2542423 : Nat := 118140960795 + 2542423 * 2 ^ 59
def prefixEnd_2542423 : Nat := 4983230072969 + 3 ^ 40 * 2542423 * 2
def baseEnd_2542423 : Nat := 870323350697340994680077

theorem tailTrace_2542423 : CollatzResearch.WordTrace tailWord_2542423 prefixEnd_2542423 870323350697340994680077 := by
  unfold tailWord_2542423
  simp only [CollatzResearch.WordTrace]
  refine ⟨92729784868243157124183923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61819856578828771416122615 92729784868243157124183923)
  ·
    refine ⟨139094677302364735686275885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92729784868243157124183923 139094677302364735686275885)
    ·
      refine ⟨52160503988386775882353457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139094677302364735686275885 52160503988386775882353457)
      ·
        refine ⟨39120377991290081911765093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52160503988386775882353457 39120377991290081911765093)
        ·
          refine ⟨7335070873366890358455955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39120377991290081911765093 7335070873366890358455955)
          ·
            refine ⟨11002606310050335537683933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7335070873366890358455955 11002606310050335537683933)
            ·
              refine ⟨4125977366268875826631475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11002606310050335537683933 4125977366268875826631475)
              ·
                refine ⟨6188966049403313739947213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4125977366268875826631475 6188966049403313739947213)
                ·
                  refine ⟨2320862268526242652480205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6188966049403313739947213 2320862268526242652480205)
                  ·
                    refine ⟨870323350697340994680077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320862268526242652480205 870323350697340994680077)
                    ·
                      rfl

theorem cell22_2542423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_2542423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542423 prefixEnd_2542423 := by exact prefixLift 2542423
  have htrace : WordTrace (prefixWord ++ tailWord_2542423) baseStart_2542423 baseEnd_2542423 := by
    simpa [prefixWord, tailWord_2542423, baseEnd_2542423] using wordTrace_append hprefix tailTrace_2542423
  have hstable : (prefixWord ++ tailWord_2542423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542423).length < 2 ^ (prefixWord ++ tailWord_2542423).sum := by decide
  have hdescent : baseEnd_2542423 < baseStart_2542423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542464 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 10]
def baseStart_2542464 : Nat := 118140960795 + 2542464 * 2 ^ 59
def prefixEnd_2542464 : Nat := 4983230072969 + 3 ^ 40 * 2542464 * 2
def baseEnd_2542464 : Nat := 290112461945076851468317

theorem tailTrace_2542464 : CollatzResearch.WordTrace tailWord_2542464 prefixEnd_2542464 290112461945076851468317 := by
  unfold tailWord_2542464
  simp only [CollatzResearch.WordTrace]
  refine ⟨46365640130547310563213223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61820853507396414084284297 46365640130547310563213223)
  ·
    refine ⟨69548460195820965844819835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46365640130547310563213223 69548460195820965844819835)
    ·
      refine ⟨104322690293731448767229753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69548460195820965844819835 104322690293731448767229753)
      ·
        refine ⟨78242017720298586575422315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104322690293731448767229753 78242017720298586575422315)
        ·
          refine ⟨117363026580447879863133473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78242017720298586575422315 117363026580447879863133473)
          ·
            refine ⟨88022269935335909897350105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117363026580447879863133473 88022269935335909897350105)
            ·
              refine ⟨66016702451501932423012579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88022269935335909897350105 66016702451501932423012579)
              ·
                refine ⟨99025053677252898634518869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66016702451501932423012579 99025053677252898634518869)
                ·
                  refine ⟨290112461945076851468317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 99025053677252898634518869 290112461945076851468317)
                  ·
                    rfl

theorem cell22_2542464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_2542464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542464 prefixEnd_2542464 := by exact prefixLift 2542464
  have htrace : WordTrace (prefixWord ++ tailWord_2542464) baseStart_2542464 baseEnd_2542464 := by
    simpa [prefixWord, tailWord_2542464, baseEnd_2542464] using wordTrace_append hprefix tailTrace_2542464
  have hstable : (prefixWord ++ tailWord_2542464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542464).length < 2 ^ (prefixWord ++ tailWord_2542464).sum := by decide
  have hdescent : baseEnd_2542464 < baseStart_2542464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542474 : List Nat := [3, 1, 2, 4, 1, 3, 2, 2, 1, 3]
def baseStart_2542474 : Nat := 118140960795 + 2542474 * 2 ^ 59
def prefixEnd_2542474 : Nat := 4983230072969 + 3 ^ 40 * 2542474 * 2
def baseEnd_2542474 : Nat := 870340809039593861654921

theorem tailTrace_2542474 : CollatzResearch.WordTrace tailWord_2542474 prefixEnd_2542474 870340809039593861654921 := by
  unfold tailWord_2542474
  simp only [CollatzResearch.WordTrace]
  refine ⟨23182911247764598208572619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61821096660705595222860317 23182911247764598208572619)
  ·
    refine ⟨34774366871646897312858929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23182911247764598208572619 34774366871646897312858929)
    ·
      refine ⟨26080775153735172984644197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34774366871646897312858929 26080775153735172984644197)
      ·
        refine ⟨4890145341325344934620787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26080775153735172984644197 4890145341325344934620787)
        ·
          refine ⟨7335218011988017401931181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4890145341325344934620787 7335218011988017401931181)
          ·
            refine ⟨2750706754495506525724193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7335218011988017401931181 2750706754495506525724193)
            ·
              refine ⟨2063030065871629894293145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2750706754495506525724193 2063030065871629894293145)
              ·
                refine ⟨1547272549403722420719859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2063030065871629894293145 1547272549403722420719859)
                ·
                  refine ⟨2320908824105583631079789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547272549403722420719859 2320908824105583631079789)
                  ·
                    refine ⟨870340809039593861654921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320908824105583631079789 870340809039593861654921)
                    ·
                      rfl

theorem cell22_2542474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_2542474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542474 prefixEnd_2542474 := by exact prefixLift 2542474
  have htrace : WordTrace (prefixWord ++ tailWord_2542474) baseStart_2542474 baseEnd_2542474 := by
    simpa [prefixWord, tailWord_2542474, baseEnd_2542474] using wordTrace_append hprefix tailTrace_2542474
  have hstable : (prefixWord ++ tailWord_2542474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542474).length < 2 ^ (prefixWord ++ tailWord_2542474).sum := by decide
  have hdescent : baseEnd_2542474 < baseStart_2542474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542496 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_2542496 : Nat := 118140960795 + 2542496 * 2 ^ 59
def prefixEnd_2542496 : Nat := 4983230072969 + 3 ^ 40 * 2542496 * 2
def baseEnd_2542496 : Nat := 870348340089193137604853

theorem tailTrace_2542496 : CollatzResearch.WordTrace tailWord_2542496 prefixEnd_2542496 870348340089193137604853 := by
  unfold tailWord_2542496
  simp only [CollatzResearch.WordTrace]
  refine ⟨46366223698489345295795671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61821631597985793727727561 46366223698489345295795671)
  ·
    refine ⟨69549335547734017943693507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46366223698489345295795671 69549335547734017943693507)
    ·
      refine ⟨104324003321601026915540261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69549335547734017943693507 104324003321601026915540261)
      ·
        refine ⟨19560750622800192546663799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104324003321601026915540261 19560750622800192546663799)
        ·
          refine ⟨29341125934200288819995699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19560750622800192546663799 29341125934200288819995699)
          ·
            refine ⟨44011688901300433229993549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29341125934200288819995699 44011688901300433229993549)
            ·
              refine ⟨16504383337987662461247581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44011688901300433229993549 16504383337987662461247581)
              ·
                refine ⟨6189143751745373422967843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16504383337987662461247581 6189143751745373422967843)
                ·
                  refine ⟨9283715627618060134451765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6189143751745373422967843 9283715627618060134451765)
                  ·
                    refine ⟨870348340089193137604853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9283715627618060134451765 870348340089193137604853)
                    ·
                      rfl

theorem cell22_2542496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_2542496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542496 prefixEnd_2542496 := by exact prefixLift 2542496
  have htrace : WordTrace (prefixWord ++ tailWord_2542496) baseStart_2542496 baseEnd_2542496 := by
    simpa [prefixWord, tailWord_2542496, baseEnd_2542496] using wordTrace_append hprefix tailTrace_2542496
  have hstable : (prefixWord ++ tailWord_2542496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542496).length < 2 ^ (prefixWord ++ tailWord_2542496).sum := by decide
  have hdescent : baseEnd_2542496 < baseStart_2542496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542498 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_2542498 : Nat := 118140960795 + 2542498 * 2 ^ 59
def prefixEnd_2542498 : Nat := 4983230072969 + 3 ^ 40 * 2542498 * 2
def baseEnd_2542498 : Nat := 290116341576688599684949

theorem tailTrace_2542498 : CollatzResearch.WordTrace tailWord_2542498 prefixEnd_2542498 290116341576688599684949 := by
  unfold tailWord_2542498
  simp only [CollatzResearch.WordTrace]
  refine ⟨23183130085742861233291037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61821680228647629955442765 23183130085742861233291037)
  ·
    refine ⟨8693673782153572962484139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23183130085742861233291037 8693673782153572962484139)
    ·
      refine ⟨13040510673230359443726209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8693673782153572962484139 13040510673230359443726209)
      ·
        refine ⟨9780383004922769582794657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13040510673230359443726209 9780383004922769582794657)
        ·
          refine ⟨7335287253692077187095993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9780383004922769582794657 7335287253692077187095993)
          ·
            refine ⟨5501465440269057890321995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7335287253692077187095993 5501465440269057890321995)
            ·
              refine ⟨8252198160403586835482993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501465440269057890321995 8252198160403586835482993)
              ·
                refine ⟨6189148620302690126612245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8252198160403586835482993 6189148620302690126612245)
                ·
                  refine ⟨290116341576688599684949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6189148620302690126612245 290116341576688599684949)
                  ·
                    rfl

theorem cell22_2542498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_2542498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542498 prefixEnd_2542498 := by exact prefixLift 2542498
  have htrace : WordTrace (prefixWord ++ tailWord_2542498) baseStart_2542498 baseEnd_2542498 := by
    simpa [prefixWord, tailWord_2542498, baseEnd_2542498] using wordTrace_append hprefix tailTrace_2542498
  have hstable : (prefixWord ++ tailWord_2542498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542498).length < 2 ^ (prefixWord ++ tailWord_2542498).sum := by decide
  have hdescent : baseEnd_2542498 < baseStart_2542498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542511 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 2, 4]
def baseStart_2542511 : Nat := 118140960795 + 2542511 * 2 ^ 59
def prefixEnd_2542511 : Nat := 4983230072969 + 3 ^ 40 * 2542511 * 2
def baseEnd_2542511 : Nat := 870353474895738098479807

theorem tailTrace_2542511 : CollatzResearch.WordTrace tailWord_2542511 prefixEnd_2542511 870353474895738098479807 := by
  unfold tailWord_2542511
  simp only [CollatzResearch.WordTrace]
  refine ⟨92732994491924348153387387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61821996327949565435591591 92732994491924348153387387)
  ·
    refine ⟨139099491737886522230081081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92732994491924348153387387 139099491737886522230081081)
    ·
      refine ⟨104324618803414891672560811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139099491737886522230081081 104324618803414891672560811)
      ·
        refine ⟨156486928205122337508841217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104324618803414891672560811 156486928205122337508841217)
        ·
          refine ⟨117365196153841753131630913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156486928205122337508841217 117365196153841753131630913)
          ·
            refine ⟨88023897115381314848723185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117365196153841753131630913 88023897115381314848723185)
            ·
              refine ⟨66017922836535986136542389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88023897115381314848723185 66017922836535986136542389)
              ·
                refine ⟨6189180265925248700300849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66017922836535986136542389 6189180265925248700300849)
                ·
                  refine ⟨4641885199443936525225637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6189180265925248700300849 4641885199443936525225637)
                  ·
                    refine ⟨870353474895738098479807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641885199443936525225637 870353474895738098479807)
                    ·
                      rfl

theorem cell22_2542511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_2542511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542511 prefixEnd_2542511 := by exact prefixLift 2542511
  have htrace : WordTrace (prefixWord ++ tailWord_2542511) baseStart_2542511 baseEnd_2542511 := by
    simpa [prefixWord, tailWord_2542511, baseEnd_2542511] using wordTrace_append hprefix tailTrace_2542511
  have hstable : (prefixWord ++ tailWord_2542511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542511).length < 2 ^ (prefixWord ++ tailWord_2542511).sum := by decide
  have hdescent : baseEnd_2542511 < baseStart_2542511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542526 : List Nat := [4, 2, 1, 1, 1, 2, 11]
def baseStart_2542526 : Nat := 118140960795 + 2542526 * 2 ^ 59
def prefixEnd_2542526 : Nat := 4983230072969 + 3 ^ 40 * 2542526 * 2
def baseEnd_2542526 : Nat := 32235504063047520716843

theorem tailTrace_2542526 : CollatzResearch.WordTrace tailWord_2542526 prefixEnd_2542526 32235504063047520716843 := by
  unfold tailWord_2542526
  simp only [CollatzResearch.WordTrace]
  refine ⟨11591692698358750714397929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61822361057913337143455621 11591692698358750714397929)
  ·
    refine ⟨8693769523769063035798447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11591692698358750714397929 8693769523769063035798447)
    ·
      refine ⟨13040654285653594553697671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8693769523769063035798447 13040654285653594553697671)
      ·
        refine ⟨19560981428480391830546507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13040654285653594553697671 19560981428480391830546507)
        ·
          refine ⟨29341472142720587745819761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19560981428480391830546507 29341472142720587745819761)
          ·
            refine ⟨22006104107040440809364821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29341472142720587745819761 22006104107040440809364821)
            ·
              refine ⟨32235504063047520716843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22006104107040440809364821 32235504063047520716843)
              ·
                rfl

theorem cell22_2542526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 11].length) (baseStart_2542526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542526 prefixEnd_2542526 := by exact prefixLift 2542526
  have htrace : WordTrace (prefixWord ++ tailWord_2542526) baseStart_2542526 baseEnd_2542526 := by
    simpa [prefixWord, tailWord_2542526, baseEnd_2542526] using wordTrace_append hprefix tailTrace_2542526
  have hstable : (prefixWord ++ tailWord_2542526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542526).length < 2 ^ (prefixWord ++ tailWord_2542526).sum := by decide
  have hdescent : baseEnd_2542526 < baseStart_2542526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542586 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_2542586 : Nat := 118140960795 + 2542586 * 2 ^ 59
def prefixEnd_2542586 : Nat := 4983230072969 + 3 ^ 40 * 2542586 * 2
def baseEnd_2542586 : Nat := 870379148928462902854577

theorem tailTrace_2542586 : CollatzResearch.WordTrace tailWord_2542586 prefixEnd_2542586 870379148928462902854577 := by
  unfold tailWord_2542586
  simp only [CollatzResearch.WordTrace]
  refine ⟨23183932491663158990591903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61823819977768423974911741 23183932491663158990591903)
  ·
    refine ⟨34775898737494738485887855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23183932491663158990591903 34775898737494738485887855)
    ·
      refine ⟨52163848106242107728831783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34775898737494738485887855 52163848106242107728831783)
      ·
        refine ⟨78245772159363161593247675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52163848106242107728831783 78245772159363161593247675)
        ·
          refine ⟨117368658239044742389871513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78245772159363161593247675 117368658239044742389871513)
          ·
            refine ⟨88026493679283556792403635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117368658239044742389871513 88026493679283556792403635)
            ·
              refine ⟨132039740518925335188605453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88026493679283556792403635 132039740518925335188605453)
              ·
                refine ⟨49514902694597000695727045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132039740518925335188605453 49514902694597000695727045)
                ·
                  refine ⟨9284044255236937630448821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49514902694597000695727045 9284044255236937630448821)
                  ·
                    refine ⟨870379148928462902854577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9284044255236937630448821 870379148928462902854577)
                    ·
                      rfl

theorem cell22_2542586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_2542586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542586 prefixEnd_2542586 := by exact prefixLift 2542586
  have htrace : WordTrace (prefixWord ++ tailWord_2542586) baseStart_2542586 baseEnd_2542586 := by
    simpa [prefixWord, tailWord_2542586, baseEnd_2542586] using wordTrace_append hprefix tailTrace_2542586
  have hstable : (prefixWord ++ tailWord_2542586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542586).length < 2 ^ (prefixWord ++ tailWord_2542586).sum := by decide
  have hdescent : baseEnd_2542586 < baseStart_2542586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542618 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_2542618 : Nat := 118140960795 + 2542618 * 2 ^ 59
def prefixEnd_2542618 : Nat := 4983230072969 + 3 ^ 40 * 2542618 * 2
def baseEnd_2542618 : Nat := 870390103182425486054479

theorem tailTrace_2542618 : CollatzResearch.WordTrace tailWord_2542618 prefixEnd_2542618 870390103182425486054479 := by
  unfold tailWord_2542618
  simp only [CollatzResearch.WordTrace]
  refine ⟨23184224275634176356883127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61824598068357803618355005 23184224275634176356883127)
  ·
    refine ⟨34776336413451264535324691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23184224275634176356883127 34776336413451264535324691)
    ·
      refine ⟨52164504620176896802987037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34776336413451264535324691 52164504620176896802987037)
      ·
        refine ⟨19561689232566336301120139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52164504620176896802987037 19561689232566336301120139)
        ·
          refine ⟨29342533848849504451680209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19561689232566336301120139 29342533848849504451680209)
          ·
            refine ⟨22006900386637128338760157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29342533848849504451680209 22006900386637128338760157)
            ·
              refine ⟨8252587644988923127035059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22006900386637128338760157 8252587644988923127035059)
              ·
                refine ⟨12378881467483384690552589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8252587644988923127035059 12378881467483384690552589)
                ·
                  refine ⟨4642080550306269258957221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12378881467483384690552589 4642080550306269258957221)
                  ·
                    refine ⟨870390103182425486054479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4642080550306269258957221 870390103182425486054479)
                    ·
                      rfl

theorem cell22_2542618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_2542618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542618 prefixEnd_2542618 := by exact prefixLift 2542618
  have htrace : WordTrace (prefixWord ++ tailWord_2542618) baseStart_2542618 baseEnd_2542618 := by
    simpa [prefixWord, tailWord_2542618, baseEnd_2542618] using wordTrace_append hprefix tailTrace_2542618
  have hstable : (prefixWord ++ tailWord_2542618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542618).length < 2 ^ (prefixWord ++ tailWord_2542618).sum := by decide
  have hdescent : baseEnd_2542618 < baseStart_2542618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542635 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 1, 4]
def baseStart_2542635 : Nat := 118140960795 + 2542635 * 2 ^ 59
def prefixEnd_2542635 : Nat := 4983230072969 + 3 ^ 40 * 2542635 * 2
def baseEnd_2542635 : Nat := 870395922629843108379427

theorem tailTrace_2542635 : CollatzResearch.WordTrace tailWord_2542635 prefixEnd_2542635 870395922629843108379427 := by
  unfold tailWord_2542635
  simp only [CollatzResearch.WordTrace]
  refine ⟨92737517143475117330901359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61825011428983411553934239 92737517143475117330901359)
  ·
    refine ⟨139106275715212675996352039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92737517143475117330901359 139106275715212675996352039)
    ·
      refine ⟨208659413572819013994528059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139106275715212675996352039 208659413572819013994528059)
      ·
        refine ⟨312989120359228520991792089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208659413572819013994528059 312989120359228520991792089)
        ·
          refine ⟨234741840269421390743844067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312989120359228520991792089 234741840269421390743844067)
          ·
            refine ⟨352112760404132086115766101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234741840269421390743844067 352112760404132086115766101)
            ·
              refine ⟨2063160705492961442084567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 352112760404132086115766101 2063160705492961442084567)
              ·
                refine ⟨3094741058239442163126851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063160705492961442084567 3094741058239442163126851)
                ·
                  refine ⟨4642111587359163244690277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094741058239442163126851 4642111587359163244690277)
                  ·
                    refine ⟨870395922629843108379427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4642111587359163244690277 870395922629843108379427)
                    ·
                      rfl

theorem cell22_2542635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 4].length) (baseStart_2542635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542635 prefixEnd_2542635 := by exact prefixLift 2542635
  have htrace : WordTrace (prefixWord ++ tailWord_2542635) baseStart_2542635 baseEnd_2542635 := by
    simpa [prefixWord, tailWord_2542635, baseEnd_2542635] using wordTrace_append hprefix tailTrace_2542635
  have hstable : (prefixWord ++ tailWord_2542635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542635).length < 2 ^ (prefixWord ++ tailWord_2542635).sum := by decide
  have hdescent : baseEnd_2542635 < baseStart_2542635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542686 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2542686 : Nat := 118140960795 + 2542686 * 2 ^ 59
def prefixEnd_2542686 : Nat := 4983230072969 + 3 ^ 40 * 2542686 * 2
def baseEnd_2542686 : Nat := 870413380972095975354271

theorem tailTrace_2542686 : CollatzResearch.WordTrace tailWord_2542686 prefixEnd_2542686 870413380972095975354271 := by
  unfold tailWord_2542686
  simp only [CollatzResearch.WordTrace]
  refine ⟨11592422158286294130125989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61826251510860235360671941 11592422158286294130125989)
  ·
    refine ⟨2173579154678680149398623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11592422158286294130125989 2173579154678680149398623)
    ·
      refine ⟨3260368732018020224097935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173579154678680149398623 3260368732018020224097935)
      ·
        refine ⟨4890553098027030336146903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260368732018020224097935 4890553098027030336146903)
        ·
          refine ⟨7335829647040545504220355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4890553098027030336146903 7335829647040545504220355)
          ·
            refine ⟨11003744470560818256330533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7335829647040545504220355 11003744470560818256330533)
            ·
              refine ⟨2063202088230153423061975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11003744470560818256330533 2063202088230153423061975)
              ·
                refine ⟨3094803132345230134592963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063202088230153423061975 3094803132345230134592963)
                ·
                  refine ⟨4642204698517845201889445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094803132345230134592963 4642204698517845201889445)
                  ·
                    refine ⟨870413380972095975354271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4642204698517845201889445 870413380972095975354271)
                    ·
                      rfl

theorem cell22_2542686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2542686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542686 prefixEnd_2542686 := by exact prefixLift 2542686
  have htrace : WordTrace (prefixWord ++ tailWord_2542686) baseStart_2542686 baseEnd_2542686 := by
    simpa [prefixWord, tailWord_2542686, baseEnd_2542686] using wordTrace_append hprefix tailTrace_2542686
  have hstable : (prefixWord ++ tailWord_2542686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542686).length < 2 ^ (prefixWord ++ tailWord_2542686).sum := by decide
  have hdescent : baseEnd_2542686 < baseStart_2542686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542744 : List Nat := [2, 1, 2, 4, 2, 1, 3, 3, 1, 3]
def baseStart_2542744 : Nat := 118140960795 + 2542744 * 2 ^ 59
def prefixEnd_2542744 : Nat := 4983230072969 + 3 ^ 40 * 2542744 * 2
def baseEnd_2542744 : Nat := 870433235557403157404093

theorem tailTrace_2542744 : CollatzResearch.WordTrace tailWord_2542744 prefixEnd_2542744 870433235557403157404093 := by
  unfold tailWord_2542744
  simp only [CollatzResearch.WordTrace]
  refine ⟨46370746350040114473309643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61827661800053485964412857 46370746350040114473309643)
  ·
    refine ⟨69556119525060171709964465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46370746350040114473309643 69556119525060171709964465)
    ·
      refine ⟨52167089643795128782473349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69556119525060171709964465 52167089643795128782473349)
      ·
        refine ⟨9781329308211586646713753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52167089643795128782473349 9781329308211586646713753)
        ·
          refine ⟨7335996981158689985035315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9781329308211586646713753 7335996981158689985035315)
          ·
            refine ⟨11003995471738034977552973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7335996981158689985035315 11003995471738034977552973)
            ·
              refine ⟨4126498301901763116582365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11003995471738034977552973 4126498301901763116582365)
              ·
                refine ⟨1547436863213161168718387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4126498301901763116582365 1547436863213161168718387)
                ·
                  refine ⟨2321155294819741753077581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547436863213161168718387 2321155294819741753077581)
                  ·
                    refine ⟨870433235557403157404093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2321155294819741753077581 870433235557403157404093)
                    ·
                      rfl

theorem cell22_2542744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_2542744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542744 prefixEnd_2542744 := by exact prefixLift 2542744
  have htrace : WordTrace (prefixWord ++ tailWord_2542744) baseStart_2542744 baseEnd_2542744 := by
    simpa [prefixWord, tailWord_2542744, baseEnd_2542744] using wordTrace_append hprefix tailTrace_2542744
  have hstable : (prefixWord ++ tailWord_2542744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542744).length < 2 ^ (prefixWord ++ tailWord_2542744).sum := by decide
  have hdescent : baseEnd_2542744 < baseStart_2542744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
