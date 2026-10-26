import V185TrunkScan23Chunk0240

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1425349 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 1, 7, 3]
def baseStart_1425349 : Nat := 118140960795 + 1425349 * 2 ^ 59
def prefixEnd_1425349 : Nat := 4983230072969 + 3 ^ 40 * 1425349 * 2
def baseEnd_1425349 : Nat := 731889137405449049182445

theorem tailTrace_1425349 : CollatzResearch.WordTrace tailWord_1425349 prefixEnd_1425349 731889137405449049182445 := by
  unfold tailWord_1425349
  simp only [CollatzResearch.WordTrace]
  refine ⟨51986748913211478073839101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34657832608807652049226067 51986748913211478073839101)
  ·
    refine ⟨19495030842454304277689663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51986748913211478073839101 19495030842454304277689663)
    ·
      refine ⟨29242546263681456416534495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19495030842454304277689663 29242546263681456416534495)
      ·
        refine ⟨43863819395522184624801743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29242546263681456416534495 43863819395522184624801743)
        ·
          refine ⟨65795729093283276937202615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43863819395522184624801743 65795729093283276937202615)
          ·
            refine ⟨98693593639924915405803923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65795729093283276937202615 98693593639924915405803923)
            ·
              refine ⟨148040390459887373108705885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98693593639924915405803923 148040390459887373108705885)
              ·
                refine ⟨55515146422457764915764707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148040390459887373108705885 55515146422457764915764707)
                ·
                  refine ⟨83272719633686647373647061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55515146422457764915764707 83272719633686647373647061)
                  ·
                    refine ⟨1951704366414530797819853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 83272719633686647373647061 1951704366414530797819853)
                    ·
                      refine ⟨731889137405449049182445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1951704366414530797819853 731889137405449049182445)
                      ·
                        rfl

theorem cell23_1425349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_1425349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425349 prefixEnd_1425349 := by exact prefixLift 1425349
  have htrace : WordTrace (prefixWord ++ tailWord_1425349) baseStart_1425349 baseEnd_1425349 := by
    simpa [prefixWord, tailWord_1425349, baseEnd_1425349] using wordTrace_append hprefix tailTrace_1425349
  have hstable : (prefixWord ++ tailWord_1425349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425349).length < 2 ^ (prefixWord ++ tailWord_1425349).sum := by decide
  have hdescent : baseEnd_1425349 < baseStart_1425349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425416 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 6, 4]
def baseStart_1425416 : Nat := 118140960795 + 1425416 * 2 ^ 59
def prefixEnd_1425416 : Nat := 4983230072969 + 3 ^ 40 * 1425416 * 2
def baseEnd_1425416 : Nat := 243974513536433429014879

theorem tailTrace_1425416 : CollatzResearch.WordTrace tailWord_1425416 prefixEnd_1425416 243974513536433429014879 := by
  unfold tailWord_1425416
  simp only [CollatzResearch.WordTrace]
  refine ⟨25994596301984374258264051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34659461735979165677685401 25994596301984374258264051)
  ·
    refine ⟨38991894452976561387396077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25994596301984374258264051 38991894452976561387396077)
    ·
      refine ⟨14621960419866210520273529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38991894452976561387396077 14621960419866210520273529)
      ·
        refine ⟨10966470314899657890205147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14621960419866210520273529 10966470314899657890205147)
        ·
          refine ⟨16449705472349486835307721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10966470314899657890205147 16449705472349486835307721)
          ·
            refine ⟨12337279104262115126480791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16449705472349486835307721 12337279104262115126480791)
            ·
              refine ⟨18505918656393172689721187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12337279104262115126480791 18505918656393172689721187)
              ·
                refine ⟨27758877984589759034581781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18505918656393172689721187 27758877984589759034581781)
                ·
                  refine ⟨1301197405527644954746021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27758877984589759034581781 1301197405527644954746021)
                  ·
                    refine ⟨243974513536433429014879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1301197405527644954746021 243974513536433429014879)
                    ·
                      rfl

theorem cell23_1425416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_1425416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425416 prefixEnd_1425416 := by exact prefixLift 1425416
  have htrace : WordTrace (prefixWord ++ tailWord_1425416) baseStart_1425416 baseEnd_1425416 := by
    simpa [prefixWord, tailWord_1425416, baseEnd_1425416] using wordTrace_append hprefix tailTrace_1425416
  have hstable : (prefixWord ++ tailWord_1425416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425416).length < 2 ^ (prefixWord ++ tailWord_1425416).sum := by decide
  have hdescent : baseEnd_1425416 < baseStart_1425416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425436 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1425436 : Nat := 118140960795 + 1425436 * 2 ^ 59
def prefixEnd_1425436 : Nat := 4983230072969 + 3 ^ 40 * 1425436 * 2
def baseEnd_1425436 : Nat := 731933810222390208794545

theorem tailTrace_1425436 : CollatzResearch.WordTrace tailWord_1425436 prefixEnd_1425436 731933810222390208794545 := by
  unfold tailWord_1425436
  simp only [CollatzResearch.WordTrace]
  refine ⟨25994961031948145966128081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34659948042597527954837441 25994961031948145966128081)
  ·
    refine ⟨19496220773961109474596061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25994961031948145966128081 19496220773961109474596061)
    ·
      refine ⟨7311082790235416052973523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19496220773961109474596061 7311082790235416052973523)
      ·
        refine ⟨10966624185353124079460285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7311082790235416052973523 10966624185353124079460285)
        ·
          refine ⟨4112484069507421529797607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10966624185353124079460285 4112484069507421529797607)
          ·
            refine ⟨6168726104261132294696411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112484069507421529797607 6168726104261132294696411)
            ·
              refine ⟨9253089156391698442044617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168726104261132294696411 9253089156391698442044617)
              ·
                refine ⟨6939816867293773831533463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9253089156391698442044617 6939816867293773831533463)
                ·
                  refine ⟨10409725300940660747300195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6939816867293773831533463 10409725300940660747300195)
                  ·
                    refine ⟨15614587951410991120950293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10409725300940660747300195 15614587951410991120950293)
                    ·
                      refine ⟨731933810222390208794545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15614587951410991120950293 731933810222390208794545)
                      ·
                        rfl

theorem cell23_1425436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1425436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425436 prefixEnd_1425436 := by exact prefixLift 1425436
  have htrace : WordTrace (prefixWord ++ tailWord_1425436) baseStart_1425436 baseEnd_1425436 := by
    simpa [prefixWord, tailWord_1425436, baseEnd_1425436] using wordTrace_append hprefix tailTrace_1425436
  have hstable : (prefixWord ++ tailWord_1425436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425436).length < 2 ^ (prefixWord ++ tailWord_1425436).sum := by decide
  have hdescent : baseEnd_1425436 < baseStart_1425436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425450 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1425450 : Nat := 118140960795 + 1425450 * 2 ^ 59
def prefixEnd_1425450 : Nat := 4983230072969 + 3 ^ 40 * 1425450 * 2
def baseEnd_1425450 : Nat := 243980332983851051339827

theorem tailTrace_1425450 : CollatzResearch.WordTrace tailWord_1425450 prefixEnd_1425450 243980332983851051339827 := by
  unfold tailWord_1425450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12997608171461393080816451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34660288457230381548843869 12997608171461393080816451)
  ·
    refine ⟨19496412257192089621224677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12997608171461393080816451 19496412257192089621224677)
    ·
      refine ⟨3655577298223516803979627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19496412257192089621224677 3655577298223516803979627)
      ·
        refine ⟨5483365947335275205969441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655577298223516803979627 5483365947335275205969441)
        ·
          refine ⟨4112524460501456404477081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5483365947335275205969441 4112524460501456404477081)
          ·
            refine ⟨3084393345376092303357811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4112524460501456404477081 3084393345376092303357811)
            ·
              refine ⟨4626590018064138455036717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3084393345376092303357811 4626590018064138455036717)
              ·
                refine ⟨1734971256774051920638769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4626590018064138455036717 1734971256774051920638769)
                ·
                  refine ⟨1301228442580538940479077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1734971256774051920638769 1301228442580538940479077)
                  ·
                    refine ⟨243980332983851051339827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1301228442580538940479077 243980332983851051339827)
                    ·
                      rfl

theorem cell23_1425450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1425450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425450 prefixEnd_1425450 := by exact prefixLift 1425450
  have htrace : WordTrace (prefixWord ++ tailWord_1425450) baseStart_1425450 baseEnd_1425450 := by
    simpa [prefixWord, tailWord_1425450, baseEnd_1425450] using wordTrace_append hprefix tailTrace_1425450
  have hstable : (prefixWord ++ tailWord_1425450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425450).length < 2 ^ (prefixWord ++ tailWord_1425450).sum := by decide
  have hdescent : baseEnd_1425450 < baseStart_1425450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425470 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1425470 : Nat := 118140960795 + 1425470 * 2 ^ 59
def prefixEnd_1425470 : Nat := 4983230072969 + 3 ^ 40 * 1425470 * 2
def baseEnd_1425470 : Nat := 731951268564643075769389

theorem tailTrace_1425470 : CollatzResearch.WordTrace tailWord_1425470 prefixEnd_1425470 731951268564643075769389 := by
  unfold tailWord_1425470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6498895268221639467374233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34660774763848743825995909 6498895268221639467374233)
  ·
    refine ⟨4874171451166229600530675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6498895268221639467374233 4874171451166229600530675)
    ·
      refine ⟨7311257176749344400796013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4874171451166229600530675 7311257176749344400796013)
      ·
        refine ⟨2741721441281004150298505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7311257176749344400796013 2741721441281004150298505)
        ·
          refine ⟨2056291080960753112723879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2741721441281004150298505 2056291080960753112723879)
          ·
            refine ⟨3084436621441129669085819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056291080960753112723879 3084436621441129669085819)
            ·
              refine ⟨4626654932161694503628729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3084436621441129669085819 4626654932161694503628729)
              ·
                refine ⟨3469991199121270877721547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4626654932161694503628729 3469991199121270877721547)
                ·
                  refine ⟨5204986798681906316582321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3469991199121270877721547 5204986798681906316582321)
                  ·
                    refine ⟨3903740099011429737436741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5204986798681906316582321 3903740099011429737436741)
                    ·
                      refine ⟨731951268564643075769389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3903740099011429737436741 731951268564643075769389)
                      ·
                        rfl

theorem cell23_1425470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1425470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425470 prefixEnd_1425470 := by exact prefixLift 1425470
  have htrace : WordTrace (prefixWord ++ tailWord_1425470) baseStart_1425470 baseEnd_1425470 := by
    simpa [prefixWord, tailWord_1425470, baseEnd_1425470] using wordTrace_append hprefix tailTrace_1425470
  have hstable : (prefixWord ++ tailWord_1425470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425470).length < 2 ^ (prefixWord ++ tailWord_1425470).sum := by decide
  have hdescent : baseEnd_1425470 < baseStart_1425470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425473 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1425473 : Nat := 118140960795 + 1425473 * 2 ^ 59
def prefixEnd_1425473 : Nat := 4983230072969 + 3 ^ 40 * 1425473 * 2
def baseEnd_1425473 : Nat := 731952809006606564031875

theorem tailTrace_1425473 : CollatzResearch.WordTrace tailWord_1425473 prefixEnd_1425473 731952809006606564031875 := by
  unfold tailWord_1425473
  simp only [CollatzResearch.WordTrace]
  refine ⟨51991271564762247251353073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34660847709841498167568715 51991271564762247251353073)
  ·
    refine ⟨38993453673571685438514805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51991271564762247251353073 38993453673571685438514805)
    ·
      refine ⟨3655636281897345509860763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38993453673571685438514805 3655636281897345509860763)
      ·
        refine ⟨5483454422846018264791145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655636281897345509860763 5483454422846018264791145)
        ·
          refine ⟨4112590817134513698593359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5483454422846018264791145 4112590817134513698593359)
          ·
            refine ⟨6168886225701770547890039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112590817134513698593359 6168886225701770547890039)
            ·
              refine ⟨9253329338552655821835059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168886225701770547890039 9253329338552655821835059)
              ·
                refine ⟨13879994007828983732752589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9253329338552655821835059 13879994007828983732752589)
                ·
                  refine ⟨5204997752935868899782221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13879994007828983732752589 5204997752935868899782221)
                  ·
                    refine ⟨1951874157350950837418333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5204997752935868899782221 1951874157350950837418333)
                    ·
                      refine ⟨731952809006606564031875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1951874157350950837418333 731952809006606564031875)
                      ·
                        rfl

theorem cell23_1425473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1425473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425473 prefixEnd_1425473 := by exact prefixLift 1425473
  have htrace : WordTrace (prefixWord ++ tailWord_1425473) baseStart_1425473 baseEnd_1425473 := by
    simpa [prefixWord, tailWord_1425473, baseEnd_1425473] using wordTrace_append hprefix tailTrace_1425473
  have hstable : (prefixWord ++ tailWord_1425473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425473).length < 2 ^ (prefixWord ++ tailWord_1425473).sum := by decide
  have hdescent : baseEnd_1425473 < baseStart_1425473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425496 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1425496 : Nat := 118140960795 + 1425496 * 2 ^ 59
def prefixEnd_1425496 : Nat := 4983230072969 + 3 ^ 40 * 1425496 * 2
def baseEnd_1425496 : Nat := 731964619061659974044269

theorem tailTrace_1425496 : CollatzResearch.WordTrace tailWord_1425496 prefixEnd_1425496 731964619061659974044269 := by
  unfold tailWord_1425496
  simp only [CollatzResearch.WordTrace]
  refine ⟨25996055221839461089720171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34661406962452614786293561 25996055221839461089720171)
  ·
    refine ⟨38994082832759191634580257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25996055221839461089720171 38994082832759191634580257)
    ·
      refine ⟨29245562124569393725935193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38994082832759191634580257 29245562124569393725935193)
      ·
        refine ⟨21934171593427045294451395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29245562124569393725935193 21934171593427045294451395)
        ·
          refine ⟨32901257390140567941677093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21934171593427045294451395 32901257390140567941677093)
          ·
            refine ⟨6168985760651356489064455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32901257390140567941677093 6168985760651356489064455)
            ·
              refine ⟨9253478640977034733596683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168985760651356489064455 9253478640977034733596683)
              ·
                refine ⟨13880217961465552100395025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9253478640977034733596683 13880217961465552100395025)
                ·
                  refine ⟨10410163471099164075296269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13880217961465552100395025 10410163471099164075296269)
                  ·
                    refine ⟨3903811301662186528236101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10410163471099164075296269 3903811301662186528236101)
                    ·
                      refine ⟨731964619061659974044269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3903811301662186528236101 731964619061659974044269)
                      ·
                        rfl

theorem cell23_1425496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1425496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425496 prefixEnd_1425496 := by exact prefixLift 1425496
  have htrace : WordTrace (prefixWord ++ tailWord_1425496) baseStart_1425496 baseEnd_1425496 := by
    simpa [prefixWord, tailWord_1425496, baseEnd_1425496] using wordTrace_append hprefix tailTrace_1425496
  have hstable : (prefixWord ++ tailWord_1425496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425496).length < 2 ^ (prefixWord ++ tailWord_1425496).sum := by decide
  have hdescent : baseEnd_1425496 < baseStart_1425496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425500 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_1425500 : Nat := 118140960795 + 1425500 * 2 ^ 59
def prefixEnd_1425500 : Nat := 4983230072969 + 3 ^ 40 * 1425500 * 2
def baseEnd_1425500 : Nat := 731966672984277958394251

theorem tailTrace_1425500 : CollatzResearch.WordTrace tailWord_1425500 prefixEnd_1425500 731966672984277958394251 := by
  unfold tailWord_1425500
  simp only [CollatzResearch.WordTrace]
  refine ⟨25996128167832215431292977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34661504223776287241723969 25996128167832215431292977)
  ·
    refine ⟨19497096125874161573469733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25996128167832215431292977 19497096125874161573469733)
    ·
      refine ⟨3655705523601405295025575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19497096125874161573469733 3655705523601405295025575)
      ·
        refine ⟨5483558285402107942538363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655705523601405295025575 5483558285402107942538363)
        ·
          refine ⟨8225337428103161913807545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5483558285402107942538363 8225337428103161913807545)
          ·
            refine ⟨6169003071077371435355659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8225337428103161913807545 6169003071077371435355659)
            ·
              refine ⟨9253504606616057153033489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169003071077371435355659 9253504606616057153033489)
              ·
                refine ⟨6940128454962042864775117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9253504606616057153033489 6940128454962042864775117)
                ·
                  refine ⟨2602548170610766074290669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6940128454962042864775117 2602548170610766074290669)
                  ·
                    refine ⟨975955563979037277859001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2602548170610766074290669 975955563979037277859001)
                    ·
                      refine ⟨731966672984277958394251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975955563979037277859001 731966672984277958394251)
                      ·
                        rfl

theorem cell23_1425500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_1425500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425500 prefixEnd_1425500 := by exact prefixLift 1425500
  have htrace : WordTrace (prefixWord ++ tailWord_1425500) baseStart_1425500 baseEnd_1425500 := by
    simpa [prefixWord, tailWord_1425500, baseEnd_1425500] using wordTrace_append hprefix tailTrace_1425500
  have hstable : (prefixWord ++ tailWord_1425500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425500).length < 2 ^ (prefixWord ++ tailWord_1425500).sum := by decide
  have hdescent : baseEnd_1425500 < baseStart_1425500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425558 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1425558 : Nat := 118140960795 + 1425558 * 2 ^ 59
def prefixEnd_1425558 : Nat := 4983230072969 + 3 ^ 40 * 1425558 * 2
def baseEnd_1425558 : Nat := 731996454862238731468985

theorem tailTrace_1425558 : CollatzResearch.WordTrace tailWord_1425558 prefixEnd_1425558 731996454862238731468985 := by
  unfold tailWord_1425558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3249648235590894173012333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34662914512969537845464885 3249648235590894173012333)
  ·
    refine ⟨1218618088346585314879625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3249648235590894173012333 1218618088346585314879625)
    ·
      refine ⟨913963566259938986159719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1218618088346585314879625 913963566259938986159719)
      ·
        refine ⟨1370945349389908479239579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913963566259938986159719 1370945349389908479239579)
        ·
          refine ⟨2056418024084862718859369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370945349389908479239579 2056418024084862718859369)
          ·
            refine ⟨1542313518063647039144527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2056418024084862718859369 1542313518063647039144527)
            ·
              refine ⟨2313470277095470558716791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1542313518063647039144527 2313470277095470558716791)
              ·
                refine ⟨3470205415643205838075187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313470277095470558716791 3470205415643205838075187)
                ·
                  refine ⟨5205308123464808757112781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470205415643205838075187 5205308123464808757112781)
                  ·
                    refine ⟨1951990546299303283917293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5205308123464808757112781 1951990546299303283917293)
                    ·
                      refine ⟨731996454862238731468985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1951990546299303283917293 731996454862238731468985)
                      ·
                        rfl

theorem cell23_1425558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1425558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425558 prefixEnd_1425558 := by exact prefixLift 1425558
  have htrace : WordTrace (prefixWord ++ tailWord_1425558) baseStart_1425558 baseEnd_1425558 := by
    simpa [prefixWord, tailWord_1425558, baseEnd_1425558] using wordTrace_append hprefix tailTrace_1425558
  have hstable : (prefixWord ++ tailWord_1425558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425558).length < 2 ^ (prefixWord ++ tailWord_1425558).sum := by decide
  have hdescent : baseEnd_1425558 < baseStart_1425558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425564 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_1425564 : Nat := 118140960795 + 1425564 * 2 ^ 59
def prefixEnd_1425564 : Nat := 4983230072969 + 3 ^ 40 * 1425564 * 2
def baseEnd_1425564 : Nat := 731999535746165707993957

theorem tailTrace_1425564 : CollatzResearch.WordTrace tailWord_1425564 prefixEnd_1425564 731999535746165707993957 := by
  unfold tailWord_1425564
  simp only [CollatzResearch.WordTrace]
  refine ⟨25997295303716284896457873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34663060404955046528610497 25997295303716284896457873)
  ·
    refine ⟨19497971477787213672343405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25997295303716284896457873 19497971477787213672343405)
    ·
      refine ⟨7311739304170205127128777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19497971477787213672343405 7311739304170205127128777)
      ·
        refine ⟨5483804478127653845346583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7311739304170205127128777 5483804478127653845346583)
        ·
          refine ⟨8225706717191480768019875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5483804478127653845346583 8225706717191480768019875)
          ·
            refine ⟨12338560075787221152029813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8225706717191480768019875 12338560075787221152029813)
            ·
              refine ⟨1156740007105051983002795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12338560075787221152029813 1156740007105051983002795)
              ·
                refine ⟨1735110010657577974504193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156740007105051983002795 1735110010657577974504193)
                ·
                  refine ⟨1301332507993183480878145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1735110010657577974504193 1301332507993183480878145)
                  ·
                    refine ⟨975999380994887610658609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1301332507993183480878145 975999380994887610658609)
                    ·
                      refine ⟨731999535746165707993957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975999380994887610658609 731999535746165707993957)
                      ·
                        rfl

theorem cell23_1425564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_1425564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425564 prefixEnd_1425564 := by exact prefixLift 1425564
  have htrace : WordTrace (prefixWord ++ tailWord_1425564) baseStart_1425564 baseEnd_1425564 := by
    simpa [prefixWord, tailWord_1425564, baseEnd_1425564] using wordTrace_append hprefix tailTrace_1425564
  have hstable : (prefixWord ++ tailWord_1425564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425564).length < 2 ^ (prefixWord ++ tailWord_1425564).sum := by decide
  have hdescent : baseEnd_1425564 < baseStart_1425564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425623 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 3]
def baseStart_1425623 : Nat := 118140960795 + 1425623 * 2 ^ 59
def prefixEnd_1425623 : Nat := 4983230072969 + 3 ^ 40 * 1425623 * 2
def baseEnd_1425623 : Nat := 732029831104780977156185

theorem tailTrace_1425623 : CollatzResearch.WordTrace tailWord_1425623 prefixEnd_1425623 732029831104780977156185 := by
  unfold tailWord_1425623
  simp only [CollatzResearch.WordTrace]
  refine ⟨51996742514218822869313523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34664495009479215246209015 51996742514218822869313523)
  ·
    refine ⟨77995113771328234303970285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51996742514218822869313523 77995113771328234303970285)
    ·
      refine ⟨29248167664248087863988857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77995113771328234303970285 29248167664248087863988857)
      ·
        refine ⟨21936125748186065897991643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29248167664248087863988857 21936125748186065897991643)
        ·
          refine ⟨32904188622279098846987465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21936125748186065897991643 32904188622279098846987465)
          ·
            refine ⟨24678141466709324135240599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32904188622279098846987465 24678141466709324135240599)
            ·
              refine ⟨37017212200063986202860899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24678141466709324135240599 37017212200063986202860899)
              ·
                refine ⟨55525818300095979304291349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37017212200063986202860899 55525818300095979304291349)
                ·
                  refine ⟨2602772732816999029888657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55525818300095979304291349 2602772732816999029888657)
                  ·
                    refine ⟨1952079549612749272416493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2602772732816999029888657 1952079549612749272416493)
                    ·
                      refine ⟨732029831104780977156185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1952079549612749272416493 732029831104780977156185)
                      ·
                        rfl

theorem cell23_1425623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_1425623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425623 prefixEnd_1425623 := by exact prefixLift 1425623
  have htrace : WordTrace (prefixWord ++ tailWord_1425623) baseStart_1425623 baseEnd_1425623 := by
    simpa [prefixWord, tailWord_1425623, baseEnd_1425623] using wordTrace_append hprefix tailTrace_1425623
  have hstable : (prefixWord ++ tailWord_1425623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425623).length < 2 ^ (prefixWord ++ tailWord_1425623).sum := by decide
  have hdescent : baseEnd_1425623 < baseStart_1425623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425640 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_1425640 : Nat := 118140960795 + 1425640 * 2 ^ 59
def prefixEnd_1425640 : Nat := 4983230072969 + 3 ^ 40 * 1425640 * 2
def baseEnd_1425640 : Nat := 732038560275907410643607

theorem tailTrace_1425640 : CollatzResearch.WordTrace tailWord_1425640 prefixEnd_1425640 732038560275907410643607 := by
  unfold tailWord_1425640
  simp only [CollatzResearch.WordTrace]
  refine ⟨25998681277578617386341187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34664908370104823181788249 25998681277578617386341187)
  ·
    refine ⟨38998021916367926079511781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25998681277578617386341187 38998021916367926079511781)
    ·
      refine ⟨7312129109318986139908459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38998021916367926079511781 7312129109318986139908459)
      ·
        refine ⟨10968193663978479209862689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7312129109318986139908459 10968193663978479209862689)
        ·
          refine ⟨8226145247983859407397017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10968193663978479209862689 8226145247983859407397017)
          ·
            refine ⟨6169608935987894555547763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8226145247983859407397017 6169608935987894555547763)
            ·
              refine ⟨9254413403981841833321645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169608935987894555547763 9254413403981841833321645)
              ·
                refine ⟨3470405026493190687495617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9254413403981841833321645 3470405026493190687495617)
                ·
                  refine ⟨2602803769869893015621713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3470405026493190687495617 2602803769869893015621713)
                  ·
                    refine ⟨1952102827402419761716285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2602803769869893015621713 1952102827402419761716285)
                    ·
                      refine ⟨732038560275907410643607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1952102827402419761716285 732038560275907410643607)
                      ·
                        rfl

theorem cell23_1425640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_1425640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425640 prefixEnd_1425640 := by exact prefixLift 1425640
  have htrace : WordTrace (prefixWord ++ tailWord_1425640) baseStart_1425640 baseEnd_1425640 := by
    simpa [prefixWord, tailWord_1425640, baseEnd_1425640] using wordTrace_append hprefix tailTrace_1425640
  have hstable : (prefixWord ++ tailWord_1425640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425640).length < 2 ^ (prefixWord ++ tailWord_1425640).sum := by decide
  have hdescent : baseEnd_1425640 < baseStart_1425640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425660 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 6]
def baseStart_1425660 : Nat := 118140960795 + 1425660 * 2 ^ 59
def prefixEnd_1425660 : Nat := 4983230072969 + 3 ^ 40 * 1425660 * 2
def baseEnd_1425660 : Nat := 81338758876555259154835

theorem tailTrace_1425660 : CollatzResearch.WordTrace tailWord_1425660 prefixEnd_1425660 81338758876555259154835 := by
  unfold tailWord_1425660
  simp only [CollatzResearch.WordTrace]
  refine ⟨25999046007542389094205217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34665394676723185458940289 25999046007542389094205217)
  ·
    refine ⟨19499284505656791820653913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25999046007542389094205217 19499284505656791820653913)
    ·
      refine ⟨14624463379242593865490435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19499284505656791820653913 14624463379242593865490435)
      ·
        refine ⟨21936695068863890798235653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14624463379242593865490435 21936695068863890798235653)
        ·
          refine ⟨4113130325411979524669185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21936695068863890798235653 4113130325411979524669185)
          ·
            refine ⟨3084847744058984643501889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4113130325411979524669185 3084847744058984643501889)
            ·
              refine ⟨2313635808044238482626417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084847744058984643501889 2313635808044238482626417)
              ·
                refine ⟨1735226856033178861969813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2313635808044238482626417 1735226856033178861969813)
                ·
                  refine ⟨81338758876555259154835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1735226856033178861969813 81338758876555259154835)
                  ·
                    rfl

theorem cell23_1425660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_1425660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425660 prefixEnd_1425660 := by exact prefixLift 1425660
  have htrace : WordTrace (prefixWord ++ tailWord_1425660) baseStart_1425660 baseEnd_1425660 := by
    simpa [prefixWord, tailWord_1425660, baseEnd_1425660] using wordTrace_append hprefix tailTrace_1425660
  have hstable : (prefixWord ++ tailWord_1425660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425660).length < 2 ^ (prefixWord ++ tailWord_1425660).sum := by decide
  have hdescent : baseEnd_1425660 < baseStart_1425660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425673 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 3, 5]
def baseStart_1425673 : Nat := 118140960795 + 1425673 * 2 ^ 59
def prefixEnd_1425673 : Nat := 4983230072969 + 3 ^ 40 * 1425673 * 2
def baseEnd_1425673 : Nat := 244018501712501927176985

theorem tailTrace_1425673 : CollatzResearch.WordTrace tailWord_1425673 prefixEnd_1425673 244018501712501927176985 := by
  unfold tailWord_1425673
  simp only [CollatzResearch.WordTrace]
  refine ⟨51998566164037681408633673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34665710776025120939089115 51998566164037681408633673)
  ·
    refine ⟨38998924623028261056475255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51998566164037681408633673 38998924623028261056475255)
    ·
      refine ⟨58498386934542391584712883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38998924623028261056475255 58498386934542391584712883)
      ·
        refine ⟨87747580401813587377069325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58498386934542391584712883 87747580401813587377069325)
        ·
          refine ⟨32905342650680095266400997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87747580401813587377069325 32905342650680095266400997)
          ·
            refine ⟨6169751747002517862450187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32905342650680095266400997 6169751747002517862450187)
            ·
              refine ⟨9254627620503776793675281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169751747002517862450187 9254627620503776793675281)
              ·
                refine ⟨6940970715377832595256461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9254627620503776793675281 6940970715377832595256461)
                ·
                  refine ⟨2602864018266687223221173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6940970715377832595256461 2602864018266687223221173)
                  ·
                    refine ⟨244018501712501927176985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2602864018266687223221173 244018501712501927176985)
                    ·
                      rfl

theorem cell23_1425673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_1425673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425673 prefixEnd_1425673 := by exact prefixLift 1425673
  have htrace : WordTrace (prefixWord ++ tailWord_1425673) baseStart_1425673 baseEnd_1425673 := by
    simpa [prefixWord, tailWord_1425673, baseEnd_1425673] using wordTrace_append hprefix tailTrace_1425673
  have hstable : (prefixWord ++ tailWord_1425673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425673).length < 2 ^ (prefixWord ++ tailWord_1425673).sum := by decide
  have hdescent : baseEnd_1425673 < baseStart_1425673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425687 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1425687 : Nat := 118140960795 + 1425687 * 2 ^ 59
def prefixEnd_1425687 : Nat := 4983230072969 + 3 ^ 40 * 1425687 * 2
def baseEnd_1425687 : Nat := 732062693866668726755891

theorem tailTrace_1425687 : CollatzResearch.WordTrace tailWord_1425687 prefixEnd_1425687 732062693866668726755891 := by
  unfold tailWord_1425687
  simp only [CollatzResearch.WordTrace]
  refine ⟨51999076785986961799643315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34666051190657974533095543 51999076785986961799643315)
  ·
    refine ⟨77998615178980442699464973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51999076785986961799643315 77998615178980442699464973)
    ·
      refine ⟨29249480692117666012299365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77998615178980442699464973 29249480692117666012299365)
      ·
        refine ⟨5484277629772062377306131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29249480692117666012299365 5484277629772062377306131)
        ·
          refine ⟨8226416444658093565959197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5484277629772062377306131 8226416444658093565959197)
          ·
            refine ⟨3084906166746785087234699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8226416444658093565959197 3084906166746785087234699)
            ·
              refine ⟨4627359250120177630852049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3084906166746785087234699 4627359250120177630852049)
              ·
                refine ⟨3470519437590133223139037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4627359250120177630852049 3470519437590133223139037)
                ·
                  refine ⟨1301444789096299958677139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3470519437590133223139037 1301444789096299958677139)
                  ·
                    refine ⟨1952167183644449938015709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1301444789096299958677139 1952167183644449938015709)
                    ·
                      refine ⟨732062693866668726755891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1952167183644449938015709 732062693866668726755891)
                      ·
                        rfl

theorem cell23_1425687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1425687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425687 prefixEnd_1425687 := by exact prefixLift 1425687
  have htrace : WordTrace (prefixWord ++ tailWord_1425687) baseStart_1425687 baseEnd_1425687 := by
    simpa [prefixWord, tailWord_1425687, baseEnd_1425687] using wordTrace_append hprefix tailTrace_1425687
  have hstable : (prefixWord ++ tailWord_1425687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425687).length < 2 ^ (prefixWord ++ tailWord_1425687).sum := by decide
  have hdescent : baseEnd_1425687 < baseStart_1425687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425697 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 2, 3, 2]
def baseStart_1425697 : Nat := 118140960795 + 1425697 * 2 ^ 59
def prefixEnd_1425697 : Nat := 4983230072969 + 3 ^ 40 * 1425697 * 2
def baseEnd_1425697 : Nat := 732067828673213687630845

theorem tailTrace_1425697 : CollatzResearch.WordTrace tailWord_1425697 prefixEnd_1425697 732067828673213687630845 := by
  unfold tailWord_1425697
  simp only [CollatzResearch.WordTrace]
  refine ⟨51999441515950733507507345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34666294343967155671671563 51999441515950733507507345)
  ·
    refine ⟨38999581136963050130630509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51999441515950733507507345 38999581136963050130630509)
    ·
      refine ⟨14624842926361143798986441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38999581136963050130630509 14624842926361143798986441)
      ·
        refine ⟨10968632194770857849239831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14624842926361143798986441 10968632194770857849239831)
        ·
          refine ⟨16452948292156286773859747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10968632194770857849239831 16452948292156286773859747)
          ·
            refine ⟨24679422438234430160789621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16452948292156286773859747 24679422438234430160789621)
            ·
              refine ⟨2313695853584477827574027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24679422438234430160789621 2313695853584477827574027)
              ·
                refine ⟨3470543780376716741361041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313695853584477827574027 3470543780376716741361041)
                ·
                  refine ⟨2602907835282537556020781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3470543780376716741361041 2602907835282537556020781)
                  ·
                    refine ⟨976090438230951583507793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2602907835282537556020781 976090438230951583507793)
                    ·
                      refine ⟨732067828673213687630845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976090438230951583507793 732067828673213687630845)
                      ·
                        rfl

theorem cell23_1425697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_1425697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425697 prefixEnd_1425697 := by exact prefixLift 1425697
  have htrace : WordTrace (prefixWord ++ tailWord_1425697) baseStart_1425697 baseEnd_1425697 := by
    simpa [prefixWord, tailWord_1425697, baseEnd_1425697] using wordTrace_append hprefix tailTrace_1425697
  have hstable : (prefixWord ++ tailWord_1425697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425697).length < 2 ^ (prefixWord ++ tailWord_1425697).sum := by decide
  have hdescent : baseEnd_1425697 < baseStart_1425697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425777 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 2, 1, 3]
def baseStart_1425777 : Nat := 118140960795 + 1425777 * 2 ^ 59
def prefixEnd_1425777 : Nat := 4983230072969 + 3 ^ 40 * 1425777 * 2
def baseEnd_1425777 : Nat := 732108907125573374630477

theorem tailTrace_1425777 : CollatzResearch.WordTrace tailWord_1425777 prefixEnd_1425777 732108907125573374630477 := by
  unfold tailWord_1425777
  simp only [CollatzResearch.WordTrace]
  refine ⟨52002359355660907170419585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34668239570440604780279723 52002359355660907170419585)
  ·
    refine ⟨39001769516745680377814689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52002359355660907170419585 39001769516745680377814689)
    ·
      refine ⟨29251327137559260283361017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39001769516745680377814689 29251327137559260283361017)
      ·
        refine ⟨21938495353169445212520763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29251327137559260283361017 21938495353169445212520763)
        ·
          refine ⟨32907743029754167818781145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21938495353169445212520763 32907743029754167818781145)
          ·
            refine ⟨24680807272315625864085859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32907743029754167818781145 24680807272315625864085859)
            ·
              refine ⟨37021210908473438796128789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24680807272315625864085859 37021210908473438796128789)
              ·
                refine ⟨1735369261334692443568537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37021210908473438796128789 1735369261334692443568537)
                ·
                  refine ⟨1301526946001019332676403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1735369261334692443568537 1301526946001019332676403)
                  ·
                    refine ⟨1952290419001528999014605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1301526946001019332676403 1952290419001528999014605)
                    ·
                      refine ⟨732108907125573374630477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1952290419001528999014605 732108907125573374630477)
                      ·
                        rfl

theorem cell23_1425777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_1425777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425777 prefixEnd_1425777 := by exact prefixLift 1425777
  have htrace : WordTrace (prefixWord ++ tailWord_1425777) baseStart_1425777 baseEnd_1425777 := by
    simpa [prefixWord, tailWord_1425777, baseEnd_1425777] using wordTrace_append hprefix tailTrace_1425777
  have hstable : (prefixWord ++ tailWord_1425777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425777).length < 2 ^ (prefixWord ++ tailWord_1425777).sum := by decide
  have hdescent : baseEnd_1425777 < baseStart_1425777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425778 : List Nat := [3, 2, 1, 2, 1, 4, 3, 2, 1, 2, 2]
def baseStart_1425778 : Nat := 118140960795 + 1425778 * 2 ^ 59
def prefixEnd_1425778 : Nat := 4983230072969 + 3 ^ 40 * 1425778 * 2
def baseEnd_1425778 : Nat := 732109420606227870717973

theorem tailTrace_1425778 : CollatzResearch.WordTrace tailWord_1425778 prefixEnd_1425778 732109420606227870717973 := by
  unfold tailWord_1425778
  simp only [CollatzResearch.WordTrace]
  refine ⟨13000598957164321085301497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34668263885771522894137325 13000598957164321085301497)
  ·
    refine ⟨9750449217873240813976123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13000598957164321085301497 9750449217873240813976123)
    ·
      refine ⟨14625673826809861220964185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9750449217873240813976123 14625673826809861220964185)
      ·
        refine ⟨10969255370107395915723139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14625673826809861220964185 10969255370107395915723139)
        ·
          refine ⟨16453883055161093873584709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10969255370107395915723139 16453883055161093873584709)
          ·
            refine ⟨3085103072842705101297133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16453883055161093873584709 3085103072842705101297133)
            ·
              refine ⟨1156913652316014412986425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3085103072842705101297133 1156913652316014412986425)
              ·
                refine ⟨867685239237010809739819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1156913652316014412986425 867685239237010809739819)
                ·
                  refine ⟨1301527858855516214609729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867685239237010809739819 1301527858855516214609729)
                  ·
                    refine ⟨976145894141637160957297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1301527858855516214609729 976145894141637160957297)
                    ·
                      refine ⟨732109420606227870717973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976145894141637160957297 732109420606227870717973)
                      ·
                        rfl

theorem cell23_1425778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_1425778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425778 prefixEnd_1425778 := by exact prefixLift 1425778
  have htrace : WordTrace (prefixWord ++ tailWord_1425778) baseStart_1425778 baseEnd_1425778 := by
    simpa [prefixWord, tailWord_1425778, baseEnd_1425778] using wordTrace_append hprefix tailTrace_1425778
  have hstable : (prefixWord ++ tailWord_1425778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425778).length < 2 ^ (prefixWord ++ tailWord_1425778).sum := by decide
  have hdescent : baseEnd_1425778 < baseStart_1425778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425804 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 1, 3, 2]
def baseStart_1425804 : Nat := 118140960795 + 1425804 * 2 ^ 59
def prefixEnd_1425804 : Nat := 4983230072969 + 3 ^ 40 * 1425804 * 2
def baseEnd_1425804 : Nat := 732122771103244768992853

theorem tailTrace_1425804 : CollatzResearch.WordTrace tailWord_1425804 prefixEnd_1425804 732122771103244768992853 := by
  unfold tailWord_1425804
  simp only [CollatzResearch.WordTrace]
  refine ⟨26001672063281545390826233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34668896084375393854434977 26001672063281545390826233)
  ·
    refine ⟨19501254047461159043119675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26001672063281545390826233 19501254047461159043119675)
    ·
      refine ⟨29251881071191738564679513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19501254047461159043119675 29251881071191738564679513)
      ·
        refine ⟨21938910803393803923509635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29251881071191738564679513 21938910803393803923509635)
        ·
          refine ⟨32908366205090705885264453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21938910803393803923509635 32908366205090705885264453)
          ·
            refine ⟨6170318663454507353487085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32908366205090705885264453 6170318663454507353487085)
            ·
              refine ⟨2313869498795440257557657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6170318663454507353487085 2313869498795440257557657)
              ·
                refine ⟨1735402124096580193168243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2313869498795440257557657 1735402124096580193168243)
                ·
                  refine ⟨2603103186144870289752365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735402124096580193168243 2603103186144870289752365)
                  ·
                    refine ⟨976163694804326358657137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2603103186144870289752365 976163694804326358657137)
                    ·
                      refine ⟨732122771103244768992853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976163694804326358657137 732122771103244768992853)
                      ·
                        rfl

theorem cell23_1425804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_1425804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425804 prefixEnd_1425804 := by exact prefixLift 1425804
  have htrace : WordTrace (prefixWord ++ tailWord_1425804) baseStart_1425804 baseEnd_1425804 := by
    simpa [prefixWord, tailWord_1425804, baseEnd_1425804] using wordTrace_append hprefix tailTrace_1425804
  have hstable : (prefixWord ++ tailWord_1425804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425804).length < 2 ^ (prefixWord ++ tailWord_1425804).sum := by decide
  have hdescent : baseEnd_1425804 < baseStart_1425804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425817 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 1, 4, 2]
def baseStart_1425817 : Nat := 118140960795 + 1425817 * 2 ^ 59
def prefixEnd_1425817 : Nat := 4983230072969 + 3 ^ 40 * 1425817 * 2
def baseEnd_1425817 : Nat := 732129446351753218130293

theorem tailTrace_1425817 : CollatzResearch.WordTrace tailWord_1425817 prefixEnd_1425817 732129446351753218130293 := by
  unfold tailWord_1425817
  simp only [CollatzResearch.WordTrace]
  refine ⟨52003818275515994001875705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34669212183677329334583803 52003818275515994001875705)
  ·
    refine ⟨39002863706636995501406779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52003818275515994001875705 39002863706636995501406779)
    ·
      refine ⟨58504295559955493252110169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39002863706636995501406779 58504295559955493252110169)
      ·
        refine ⟨43878221669966619939082627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58504295559955493252110169 43878221669966619939082627)
        ·
          refine ⟨65817332504949929908623941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43878221669966619939082627 65817332504949929908623941)
          ·
            refine ⟨12340749844678111857866989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65817332504949929908623941 12340749844678111857866989)
            ·
              refine ⟨4627781191754291946700121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12340749844678111857866989 4627781191754291946700121)
              ·
                refine ⟨3470835893815718960025091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4627781191754291946700121 3470835893815718960025091)
                ·
                  refine ⟨5206253840723578440037637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470835893815718960025091 5206253840723578440037637)
                  ·
                    refine ⟨976172595135670957507057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5206253840723578440037637 976172595135670957507057)
                    ·
                      refine ⟨732129446351753218130293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976172595135670957507057 732129446351753218130293)
                      ·
                        rfl

theorem cell23_1425817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_1425817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425817 prefixEnd_1425817 := by exact prefixLift 1425817
  have htrace : WordTrace (prefixWord ++ tailWord_1425817) baseStart_1425817 baseEnd_1425817 := by
    simpa [prefixWord, tailWord_1425817, baseEnd_1425817] using wordTrace_append hprefix tailTrace_1425817
  have hstable : (prefixWord ++ tailWord_1425817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425817).length < 2 ^ (prefixWord ++ tailWord_1425817).sum := by decide
  have hdescent : baseEnd_1425817 < baseStart_1425817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425833 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_1425833 : Nat := 118140960795 + 1425833 * 2 ^ 59
def prefixEnd_1425833 : Nat := 4983230072969 + 3 ^ 40 * 1425833 * 2
def baseEnd_1425833 : Nat := 732137662042225155530219

theorem tailTrace_1425833 : CollatzResearch.WordTrace tailWord_1425833 prefixEnd_1425833 732137662042225155530219 := by
  unfold tailWord_1425833
  simp only [CollatzResearch.WordTrace]
  refine ⟨52004401843458028734458153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34669601228972019156305435 52004401843458028734458153)
  ·
    refine ⟨39003301382593521550843615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52004401843458028734458153 39003301382593521550843615)
    ·
      refine ⟨58504952073890282326265423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39003301382593521550843615 58504952073890282326265423)
      ·
        refine ⟨87757428110835423489398135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58504952073890282326265423 87757428110835423489398135)
        ·
          refine ⟨131636142166253135234097203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87757428110835423489398135 131636142166253135234097203)
          ·
            refine ⟨197454213249379702851145805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131636142166253135234097203 197454213249379702851145805)
            ·
              refine ⟨74045329968517388569179677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197454213249379702851145805 74045329968517388569179677)
              ·
                refine ⟨27766998738194020713442379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74045329968517388569179677 27766998738194020713442379)
                ·
                  refine ⟨41650498107291031070163569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27766998738194020713442379 41650498107291031070163569)
                  ·
                    refine ⟨31237873580468273302622677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41650498107291031070163569 31237873580468273302622677)
                    ·
                      refine ⟨732137662042225155530219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31237873580468273302622677 732137662042225155530219)
                      ·
                        rfl

theorem cell23_1425833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_1425833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425833 prefixEnd_1425833 := by exact prefixLift 1425833
  have htrace : WordTrace (prefixWord ++ tailWord_1425833) baseStart_1425833 baseEnd_1425833 := by
    simpa [prefixWord, tailWord_1425833, baseEnd_1425833] using wordTrace_append hprefix tailTrace_1425833
  have hstable : (prefixWord ++ tailWord_1425833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425833).length < 2 ^ (prefixWord ++ tailWord_1425833).sum := by decide
  have hdescent : baseEnd_1425833 < baseStart_1425833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425843 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 8]
def baseStart_1425843 : Nat := 118140960795 + 1425843 * 2 ^ 59
def prefixEnd_1425843 : Nat := 4983230072969 + 3 ^ 40 * 1425843 * 2
def baseEnd_1425843 : Nat := 732142796848770116405173

theorem tailTrace_1425843 : CollatzResearch.WordTrace tailWord_1425843 prefixEnd_1425843 732142796848770116405173 := by
  unfold tailWord_1425843
  simp only [CollatzResearch.WordTrace]
  refine ⟨52004766573421800442322183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34669844382281200294881455 52004766573421800442322183)
  ·
    refine ⟨78007149860132700663483275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52004766573421800442322183 78007149860132700663483275)
    ·
      refine ⟨117010724790199050995224913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78007149860132700663483275 117010724790199050995224913)
      ·
        refine ⟨87758043592649288246418685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117010724790199050995224913 87758043592649288246418685)
        ·
          refine ⟨32909266347243483092407007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87758043592649288246418685 32909266347243483092407007)
          ·
            refine ⟨49363899520865224638610511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32909266347243483092407007 49363899520865224638610511)
            ·
              refine ⟨74045849281297836957915767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49363899520865224638610511 74045849281297836957915767)
              ·
                refine ⟨111068773921946755436873651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74045849281297836957915767 111068773921946755436873651)
                ·
                  refine ⟨166603160882920133155310477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111068773921946755436873651 166603160882920133155310477)
                  ·
                    refine ⟨62476185331095049933241429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166603160882920133155310477 62476185331095049933241429)
                    ·
                      refine ⟨732142796848770116405173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 62476185331095049933241429 732142796848770116405173)
                      ·
                        rfl

theorem cell23_1425843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_1425843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425843 prefixEnd_1425843 := by exact prefixLift 1425843
  have htrace : WordTrace (prefixWord ++ tailWord_1425843) baseStart_1425843 baseEnd_1425843 := by
    simpa [prefixWord, tailWord_1425843, baseEnd_1425843] using wordTrace_append hprefix tailTrace_1425843
  have hstable : (prefixWord ++ tailWord_1425843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425843).length < 2 ^ (prefixWord ++ tailWord_1425843).sum := by decide
  have hdescent : baseEnd_1425843 < baseStart_1425843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425907 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 2, 4, 2]
def baseStart_1425907 : Nat := 118140960795 + 1425907 * 2 ^ 59
def prefixEnd_1425907 : Nat := 4983230072969 + 3 ^ 40 * 1425907 * 2
def baseEnd_1425907 : Nat := 732175659610657866004879

theorem tailTrace_1425907 : CollatzResearch.WordTrace tailWord_1425907 prefixEnd_1425907 732175659610657866004879 := by
  unfold tailWord_1425907
  simp only [CollatzResearch.WordTrace]
  refine ⟨52007100845189939372651975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34671400563459959581767983 52007100845189939372651975)
  ·
    refine ⟨78010651267784909058977963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52007100845189939372651975 78010651267784909058977963)
    ·
      refine ⟨117015976901677363588466945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78010651267784909058977963 117015976901677363588466945)
      ·
        refine ⟨87761982676258022691350209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117015976901677363588466945 87761982676258022691350209)
        ·
          refine ⟨65821487007193517018512657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87761982676258022691350209 65821487007193517018512657)
          ·
            refine ⟨49366115255395137763884493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65821487007193517018512657 49366115255395137763884493)
            ·
              refine ⟨18512293220773176661456685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49366115255395137763884493 18512293220773176661456685)
              ·
                refine ⟨6942109957789941248046257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18512293220773176661456685 6942109957789941248046257)
                ·
                  refine ⟨5206582468342455936034693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6942109957789941248046257 5206582468342455936034693)
                  ·
                    refine ⟨976234212814210488006505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5206582468342455936034693 976234212814210488006505)
                    ·
                      refine ⟨732175659610657866004879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976234212814210488006505 732175659610657866004879)
                      ·
                        rfl

theorem cell23_1425907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 4, 2].length) (baseStart_1425907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425907 prefixEnd_1425907 := by exact prefixLift 1425907
  have htrace : WordTrace (prefixWord ++ tailWord_1425907) baseStart_1425907 baseEnd_1425907 := by
    simpa [prefixWord, tailWord_1425907, baseEnd_1425907] using wordTrace_append hprefix tailTrace_1425907
  have hstable : (prefixWord ++ tailWord_1425907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425907).length < 2 ^ (prefixWord ++ tailWord_1425907).sum := by decide
  have hdescent : baseEnd_1425907 < baseStart_1425907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425917 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_1425917 : Nat := 118140960795 + 1425917 * 2 ^ 59
def prefixEnd_1425917 : Nat := 4983230072969 + 3 ^ 40 * 1425917 * 2
def baseEnd_1425917 : Nat := 244060264805734275626611

theorem tailTrace_1425917 : CollatzResearch.WordTrace tailWord_1425917 prefixEnd_1425917 244060264805734275626611 := by
  unfold tailWord_1425917
  simp only [CollatzResearch.WordTrace]
  refine ⟨52007465575153711080516005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34671643716769140720344003 52007465575153711080516005)
  ·
    refine ⟨9751399795341320827596751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52007465575153711080516005 9751399795341320827596751)
    ·
      refine ⟨14627099693011981241395127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9751399795341320827596751 14627099693011981241395127)
      ·
        refine ⟨21940649539517971862092691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14627099693011981241395127 21940649539517971862092691)
        ·
          refine ⟨32910974309276957793139037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21940649539517971862092691 32910974309276957793139037)
          ·
            refine ⟨12341615365978859172427139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32910974309276957793139037 12341615365978859172427139)
            ·
              refine ⟨18512423048968288758640709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12341615365978859172427139 18512423048968288758640709)
              ·
                refine ⟨3471079321681554142245133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18512423048968288758640709 3471079321681554142245133)
                ·
                  refine ⟨1301654745630582803341925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3471079321681554142245133 1301654745630582803341925)
                  ·
                    refine ⟨244060264805734275626611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1301654745630582803341925 244060264805734275626611)
                    ·
                      rfl

theorem cell23_1425917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_1425917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425917 prefixEnd_1425917 := by exact prefixLift 1425917
  have htrace : WordTrace (prefixWord ++ tailWord_1425917) baseStart_1425917 baseEnd_1425917 := by
    simpa [prefixWord, tailWord_1425917, baseEnd_1425917] using wordTrace_append hprefix tailTrace_1425917
  have hstable : (prefixWord ++ tailWord_1425917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425917).length < 2 ^ (prefixWord ++ tailWord_1425917).sum := by decide
  have hdescent : baseEnd_1425917 < baseStart_1425917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425930 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 10]
def baseStart_1425930 : Nat := 118140960795 + 1425930 * 2 ^ 59
def prefixEnd_1425930 : Nat := 4983230072969 + 3 ^ 40 * 1425930 * 2
def baseEnd_1425930 : Nat := 81354163296190141779697

theorem tailTrace_1425930 : CollatzResearch.WordTrace tailWord_1425930 prefixEnd_1425930 81354163296190141779697 := by
  unfold tailWord_1425930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13001984931026653575184811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34671959816071076200492829 13001984931026653575184811)
  ·
    refine ⟨19502977396539980362777217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13001984931026653575184811 19502977396539980362777217)
    ·
      refine ⟨14627233047404985272082913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19502977396539980362777217 14627233047404985272082913)
      ·
        refine ⟨10970424785553738954062185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14627233047404985272082913 10970424785553738954062185)
        ·
          refine ⟨8227818589165304215546639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10970424785553738954062185 8227818589165304215546639)
          ·
            refine ⟨12341727883747956323319959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8227818589165304215546639 12341727883747956323319959)
            ·
              refine ⟨18512591825621934484979939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12341727883747956323319959 18512591825621934484979939)
              ·
                refine ⟨27768887738432901727469909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18512591825621934484979939 27768887738432901727469909)
                ·
                  refine ⟨81354163296190141779697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 27768887738432901727469909 81354163296190141779697)
                  ·
                    rfl

theorem cell23_1425930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_1425930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425930 prefixEnd_1425930 := by exact prefixLift 1425930
  have htrace : WordTrace (prefixWord ++ tailWord_1425930) baseStart_1425930 baseEnd_1425930 := by
    simpa [prefixWord, tailWord_1425930, baseEnd_1425930] using wordTrace_append hprefix tailTrace_1425930
  have hstable : (prefixWord ++ tailWord_1425930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425930).length < 2 ^ (prefixWord ++ tailWord_1425930).sum := by decide
  have hdescent : baseEnd_1425930 < baseStart_1425930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425944 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1425944 : Nat := 118140960795 + 1425944 * 2 ^ 59
def prefixEnd_1425944 : Nat := 4983230072969 + 3 ^ 40 * 1425944 * 2
def baseEnd_1425944 : Nat := 732194658394874221242209

theorem tailTrace_1425944 : CollatzResearch.WordTrace tailWord_1425944 prefixEnd_1425944 732194658394874221242209 := by
  unfold tailWord_1425944
  simp only [CollatzResearch.WordTrace]
  refine ⟨26004225173027947345874443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34672300230703929794499257 26004225173027947345874443)
  ·
    refine ⟨39006337759541921018811665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26004225173027947345874443 39006337759541921018811665)
    ·
      refine ⟨29254753319656440764108749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39006337759541921018811665 29254753319656440764108749)
      ·
        refine ⟨10970532494871165286540781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29254753319656440764108749 10970532494871165286540781)
        ·
          refine ⟨4113949685576686982452793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10970532494871165286540781 4113949685576686982452793)
          ·
            refine ⟨3085462264182515236839595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4113949685576686982452793 3085462264182515236839595)
            ·
              refine ⟨4628193396273772855259393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085462264182515236839595 4628193396273772855259393)
              ·
                refine ⟨3471145047205329641444545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4628193396273772855259393 3471145047205329641444545)
                ·
                  refine ⟨2603358785403997231083409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3471145047205329641444545 2603358785403997231083409)
                  ·
                    refine ⟨1952519089052997923312557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2603358785403997231083409 1952519089052997923312557)
                    ·
                      refine ⟨732194658394874221242209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1952519089052997923312557 732194658394874221242209)
                      ·
                        rfl

theorem cell23_1425944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1425944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425944 prefixEnd_1425944 := by exact prefixLift 1425944
  have htrace : WordTrace (prefixWord ++ tailWord_1425944) baseStart_1425944 baseEnd_1425944 := by
    simpa [prefixWord, tailWord_1425944, baseEnd_1425944] using wordTrace_append hprefix tailTrace_1425944
  have hstable : (prefixWord ++ tailWord_1425944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425944).length < 2 ^ (prefixWord ++ tailWord_1425944).sum := by decide
  have hdescent : baseEnd_1425944 < baseStart_1425944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425977 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 3, 5]
def baseStart_1425977 : Nat := 118140960795 + 1425977 * 2 ^ 59
def prefixEnd_1425977 : Nat := 4983230072969 + 3 ^ 40 * 1425977 * 2
def baseEnd_1425977 : Nat := 244070534418824197376519

theorem tailTrace_1425977 : CollatzResearch.WordTrace tailWord_1425977 prefixEnd_1425977 244070534418824197376519 := by
  unfold tailWord_1425977
  simp only [CollatzResearch.WordTrace]
  refine ⟨52009653954936341327700185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34673102636624227551800123 52009653954936341327700185)
  ·
    refine ⟨39007240466202255995775139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52009653954936341327700185 39007240466202255995775139)
    ·
      refine ⟨58510860699303383993662709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39007240466202255995775139 58510860699303383993662709)
      ·
        refine ⟨5485393190559692249405879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58510860699303383993662709 5485393190559692249405879)
        ·
          refine ⟨8228089785839538374108819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485393190559692249405879 8228089785839538374108819)
          ·
            refine ⟨12342134678759307561163229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8228089785839538374108819 12342134678759307561163229)
            ·
              refine ⟨4628300504534740335436211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12342134678759307561163229 4628300504534740335436211)
              ·
                refine ⟨6942450756802110503154317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628300504534740335436211 6942450756802110503154317)
                ·
                  refine ⟨2603419033800791438682869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6942450756802110503154317 2603419033800791438682869)
                  ·
                    refine ⟨244070534418824197376519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2603419033800791438682869 244070534418824197376519)
                    ·
                      rfl

theorem cell23_1425977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_1425977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425977 prefixEnd_1425977 := by exact prefixLift 1425977
  have htrace : WordTrace (prefixWord ++ tailWord_1425977) baseStart_1425977 baseEnd_1425977 := by
    simpa [prefixWord, tailWord_1425977, baseEnd_1425977] using wordTrace_append hprefix tailTrace_1425977
  have hstable : (prefixWord ++ tailWord_1425977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425977).length < 2 ^ (prefixWord ++ tailWord_1425977).sum := by decide
  have hdescent : baseEnd_1425977 < baseStart_1425977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425984 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 2, 3, 2]
def baseStart_1425984 : Nat := 118140960795 + 1425984 * 2 ^ 59
def prefixEnd_1425984 : Nat := 4983230072969 + 3 ^ 40 * 1425984 * 2
def baseEnd_1425984 : Nat := 732215197621054064742025

theorem tailTrace_1425984 : CollatzResearch.WordTrace tailWord_1425984 prefixEnd_1425984 732215197621054064742025 := by
  unfold tailWord_1425984
  simp only [CollatzResearch.WordTrace]
  refine ⟨26004954632955490761602503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34673272843940654348803337 26004954632955490761602503)
  ·
    refine ⟨39007431949433236142403755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26004954632955490761602503 39007431949433236142403755)
    ·
      refine ⟨58511147924149854213605633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39007431949433236142403755 58511147924149854213605633)
      ·
        refine ⟨43883360943112390660204225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58511147924149854213605633 43883360943112390660204225)
        ·
          refine ⟨32912520707334292995153169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43883360943112390660204225 32912520707334292995153169)
          ·
            refine ⟨24684390530500719746364877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32912520707334292995153169 24684390530500719746364877)
            ·
              refine ⟨9256646448937769904886829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24684390530500719746364877 9256646448937769904886829)
              ·
                refine ⟨3471242418351663714332561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9256646448937769904886829 3471242418351663714332561)
                ·
                  refine ⟨2603431813763747785749421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3471242418351663714332561 2603431813763747785749421)
                  ·
                    refine ⟨976286930161405419656033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2603431813763747785749421 976286930161405419656033)
                    ·
                      refine ⟨732215197621054064742025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976286930161405419656033 732215197621054064742025)
                      ·
                        rfl

theorem cell23_1425984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_1425984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425984 prefixEnd_1425984 := by exact prefixLift 1425984
  have htrace : WordTrace (prefixWord ++ tailWord_1425984) baseStart_1425984 baseEnd_1425984 := by
    simpa [prefixWord, tailWord_1425984, baseEnd_1425984] using wordTrace_append hprefix tailTrace_1425984
  have hstable : (prefixWord ++ tailWord_1425984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425984).length < 2 ^ (prefixWord ++ tailWord_1425984).sum := by decide
  have hdescent : baseEnd_1425984 < baseStart_1425984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426008 : List Nat := [2, 1, 2, 2, 1, 2, 6, 2, 1, 1, 3]
def baseStart_1426008 : Nat := 118140960795 + 1426008 * 2 ^ 59
def prefixEnd_1426008 : Nat := 4983230072969 + 3 ^ 40 * 1426008 * 2
def baseEnd_1426008 : Nat := 732227521156761970841915

theorem tailTrace_1426008 : CollatzResearch.WordTrace tailWord_1426008 prefixEnd_1426008 732227521156761970841915 := by
  unfold tailWord_1426008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26005392308912016811039339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34673856411882689081385785 26005392308912016811039339)
  ·
    refine ⟨39008088463368025216559009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26005392308912016811039339 39008088463368025216559009)
    ·
      refine ⟨29256066347526018912419257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39008088463368025216559009 29256066347526018912419257)
      ·
        refine ⟨21942049760644514184314443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29256066347526018912419257 21942049760644514184314443)
        ·
          refine ⟨32913074640966771276471665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21942049760644514184314443 32913074640966771276471665)
          ·
            refine ⟨24684805980725078457353749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32913074640966771276471665 24684805980725078457353749)
            ·
              refine ⟨1157100280346488052688457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24684805980725078457353749 1157100280346488052688457)
              ·
                refine ⟨867825210259866039516343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1157100280346488052688457 867825210259866039516343)
                ·
                  refine ⟨1301737815389799059274515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867825210259866039516343 1301737815389799059274515)
                  ·
                    refine ⟨1952606723084698588911773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1301737815389799059274515 1952606723084698588911773)
                    ·
                      refine ⟨732227521156761970841915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1952606723084698588911773 732227521156761970841915)
                      ·
                        rfl

theorem cell23_1426008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_1426008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426008 prefixEnd_1426008 := by exact prefixLift 1426008
  have htrace : WordTrace (prefixWord ++ tailWord_1426008) baseStart_1426008 baseEnd_1426008 := by
    simpa [prefixWord, tailWord_1426008, baseEnd_1426008] using wordTrace_append hprefix tailTrace_1426008
  have hstable : (prefixWord ++ tailWord_1426008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426008).length < 2 ^ (prefixWord ++ tailWord_1426008).sum := by decide
  have hdescent : baseEnd_1426008 < baseStart_1426008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426047 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 3]
def baseStart_1426047 : Nat := 118140960795 + 1426047 * 2 ^ 59
def prefixEnd_1426047 : Nat := 4983230072969 + 3 ^ 40 * 1426047 * 2
def baseEnd_1426047 : Nat := 732247546902287318254235

theorem tailTrace_1426047 : CollatzResearch.WordTrace tailWord_1426047 prefixEnd_1426047 732247546902287318254235 := by
  unfold tailWord_1426047
  simp only [CollatzResearch.WordTrace]
  refine ⟨52012207064682743282748395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34674804709788495521832263 52012207064682743282748395)
  ·
    refine ⟨78018310597024114924122593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52012207064682743282748395 78018310597024114924122593)
    ·
      refine ⟨58513732947768086193091945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78018310597024114924122593 58513732947768086193091945)
      ·
        refine ⟨43885299710826064644818959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58513732947768086193091945 43885299710826064644818959)
        ·
          refine ⟨65827949566239096967228439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43885299710826064644818959 65827949566239096967228439)
          ·
            refine ⟨98741924349358645450842659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65827949566239096967228439 98741924349358645450842659)
            ·
              refine ⟨148112886524037968176263989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98741924349358645450842659 148112886524037968176263989)
              ·
                refine ⟨13885583111628559516524749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148112886524037968176263989 13885583111628559516524749)
                ·
                  refine ⟨5207093666860709818696781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13885583111628559516524749 5207093666860709818696781)
                  ·
                    refine ⟨1952660125072766182011293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5207093666860709818696781 1952660125072766182011293)
                    ·
                      refine ⟨732247546902287318254235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1952660125072766182011293 732247546902287318254235)
                      ·
                        rfl

theorem cell23_1426047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_1426047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426047 prefixEnd_1426047 := by exact prefixLift 1426047
  have htrace : WordTrace (prefixWord ++ tailWord_1426047) baseStart_1426047 baseEnd_1426047 := by
    simpa [prefixWord, tailWord_1426047, baseEnd_1426047] using wordTrace_append hprefix tailTrace_1426047
  have hstable : (prefixWord ++ tailWord_1426047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426047).length < 2 ^ (prefixWord ++ tailWord_1426047).sum := by decide
  have hdescent : baseEnd_1426047 < baseStart_1426047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426048 : List Nat := [2, 1, 1, 2, 1, 5, 1, 5, 1, 2, 2]
def baseStart_1426048 : Nat := 118140960795 + 1426048 * 2 ^ 59
def prefixEnd_1426048 : Nat := 4983230072969 + 3 ^ 40 * 1426048 * 2
def baseEnd_1426048 : Nat := 732248060382941814341731

theorem tailTrace_1426048 : CollatzResearch.WordTrace tailWord_1426048 prefixEnd_1426048 732248060382941814341731 := by
  unfold tailWord_1426048
  simp only [CollatzResearch.WordTrace]
  refine ⟨26006121768839560226767399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34674829025119413635689865 26006121768839560226767399)
  ·
    refine ⟨39009182653259340340151099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26006121768839560226767399 39009182653259340340151099)
    ·
      refine ⟨58513773979889010510226649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39009182653259340340151099 58513773979889010510226649)
      ·
        refine ⟨43885330484916757882669987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58513773979889010510226649 43885330484916757882669987)
        ·
          refine ⟨65827995727375136824004981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43885330484916757882669987 65827995727375136824004981)
          ·
            refine ⟨6171374599441419077250467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65827995727375136824004981 6171374599441419077250467)
            ·
              refine ⟨9257061899162128615875701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6171374599441419077250467 9257061899162128615875701)
              ·
                refine ⟨867849553046449557738347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9257061899162128615875701 867849553046449557738347)
                ·
                  refine ⟨1301774329569674336607521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867849553046449557738347 1301774329569674336607521)
                  ·
                    refine ⟨976330747177255752455641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1301774329569674336607521 976330747177255752455641)
                    ·
                      refine ⟨732248060382941814341731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976330747177255752455641 732248060382941814341731)
                      ·
                        rfl

theorem cell23_1426048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 1, 2, 2].length) (baseStart_1426048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426048 prefixEnd_1426048 := by exact prefixLift 1426048
  have htrace : WordTrace (prefixWord ++ tailWord_1426048) baseStart_1426048 baseEnd_1426048 := by
    simpa [prefixWord, tailWord_1426048, baseEnd_1426048] using wordTrace_append hprefix tailTrace_1426048
  have hstable : (prefixWord ++ tailWord_1426048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426048).length < 2 ^ (prefixWord ++ tailWord_1426048).sum := by decide
  have hdescent : baseEnd_1426048 < baseStart_1426048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426051 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 1, 2, 3]
def baseStart_1426051 : Nat := 118140960795 + 1426051 * 2 ^ 59
def prefixEnd_1426051 : Nat := 4983230072969 + 3 ^ 40 * 1426051 * 2
def baseEnd_1426051 : Nat := 732249600824905302604217

theorem tailTrace_1426051 : CollatzResearch.WordTrace tailWord_1426051 prefixEnd_1426051 732249600824905302604217 := by
  unfold tailWord_1426051
  simp only [CollatzResearch.WordTrace]
  refine ⟨52012352956668251965894007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34674901971112167977262671 52012352956668251965894007)
  ·
    refine ⟨78018529435002377948841011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52012352956668251965894007 78018529435002377948841011)
    ·
      refine ⟨117027794152503566923261517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78018529435002377948841011 117027794152503566923261517)
      ·
        refine ⟨43885422807188837596223069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117027794152503566923261517 43885422807188837596223069)
        ·
          refine ⟨16457033552695814098583651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43885422807188837596223069 16457033552695814098583651)
          ·
            refine ⟨24685550329043721147875477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16457033552695814098583651 24685550329043721147875477)
            ·
              refine ⟨1157135171673924428806663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24685550329043721147875477 1157135171673924428806663)
              ·
                refine ⟨1735702757510886643209995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157135171673924428806663 1735702757510886643209995)
                ·
                  refine ⟨2603554136266329964814993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735702757510886643209995 2603554136266329964814993)
                  ·
                    refine ⟨1952665602199747473611245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2603554136266329964814993 1952665602199747473611245)
                    ·
                      refine ⟨732249600824905302604217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1952665602199747473611245 732249600824905302604217)
                      ·
                        rfl

theorem cell23_1426051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_1426051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426051 prefixEnd_1426051 := by exact prefixLift 1426051
  have htrace : WordTrace (prefixWord ++ tailWord_1426051) baseStart_1426051 baseEnd_1426051 := by
    simpa [prefixWord, tailWord_1426051, baseEnd_1426051] using wordTrace_append hprefix tailTrace_1426051
  have hstable : (prefixWord ++ tailWord_1426051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426051).length < 2 ^ (prefixWord ++ tailWord_1426051).sum := by decide
  have hdescent : baseEnd_1426051 < baseStart_1426051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426058 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_1426058 : Nat := 118140960795 + 1426058 * 2 ^ 59
def prefixEnd_1426058 : Nat := 4983230072969 + 3 ^ 40 * 1426058 * 2
def baseEnd_1426058 : Nat := 244084398396495591738895

theorem tailTrace_1426058 : CollatzResearch.WordTrace tailWord_1426058 prefixEnd_1426058 244084398396495591738895 := by
  unfold tailWord_1426058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003152066910723040349707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34675072178428594774265885 13003152066910723040349707)
  ·
    refine ⟨19504728100366084560524561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13003152066910723040349707 19504728100366084560524561)
    ·
      refine ⟨14628546075274563420393421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19504728100366084560524561 14628546075274563420393421)
      ·
        refine ⟨5485704778227961282647533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14628546075274563420393421 5485704778227961282647533)
        ·
          refine ⟨2057139291835485480992825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5485704778227961282647533 2057139291835485480992825)
          ·
            refine ⟨1542854468876614110744619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2057139291835485480992825 1542854468876614110744619)
            ·
              refine ⟨2314281703314921166116929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1542854468876614110744619 2314281703314921166116929)
              ·
                refine ⟨1735711277486190874587697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2314281703314921166116929 1735711277486190874587697)
                ·
                  refine ⟨1301783458114643155940773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1735711277486190874587697 1301783458114643155940773)
                  ·
                    refine ⟨244084398396495591738895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1301783458114643155940773 244084398396495591738895)
                    ·
                      rfl

theorem cell23_1426058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_1426058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426058 prefixEnd_1426058 := by exact prefixLift 1426058
  have htrace : WordTrace (prefixWord ++ tailWord_1426058) baseStart_1426058 baseEnd_1426058 := by
    simpa [prefixWord, tailWord_1426058, baseEnd_1426058] using wordTrace_append hprefix tailTrace_1426058
  have hstable : (prefixWord ++ tailWord_1426058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426058).length < 2 ^ (prefixWord ++ tailWord_1426058).sum := by decide
  have hdescent : baseEnd_1426058 < baseStart_1426058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426107 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 3]
def baseStart_1426107 : Nat := 118140960795 + 1426107 * 2 ^ 59
def prefixEnd_1426107 : Nat := 4983230072969 + 3 ^ 40 * 1426107 * 2
def baseEnd_1426107 : Nat := 732278355741557083503959

theorem tailTrace_1426107 : CollatzResearch.WordTrace tailWord_1426107 prefixEnd_1426107 732278355741557083503959 := by
  unfold tailWord_1426107
  simp only [CollatzResearch.WordTrace]
  refine ⟨52014395444465373529932575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34676263629643582353288383 52014395444465373529932575)
  ·
    refine ⟨78021593166698060294898863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52014395444465373529932575 78021593166698060294898863)
    ·
      refine ⟨117032389750047090442348295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78021593166698060294898863 117032389750047090442348295)
      ·
        refine ⟨175548584625070635663522443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117032389750047090442348295 175548584625070635663522443)
        ·
          refine ⟨263322876937605953495283665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175548584625070635663522443 263322876937605953495283665)
          ·
            refine ⟨197492157703204465121462749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263322876937605953495283665 197492157703204465121462749)
            ·
              refine ⟨74059559138701674420548531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197492157703204465121462749 74059559138701674420548531)
              ·
                refine ⟨111089338708052511630822797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74059559138701674420548531 111089338708052511630822797)
                ·
                  refine ⟨41658502015519691861558549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111089338708052511630822797 41658502015519691861558549)
                  ·
                    refine ⟨1952742281977485556010557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41658502015519691861558549 1952742281977485556010557)
                    ·
                      refine ⟨732278355741557083503959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1952742281977485556010557 732278355741557083503959)
                      ·
                        rfl

theorem cell23_1426107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 3].length) (baseStart_1426107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426107 prefixEnd_1426107 := by exact prefixLift 1426107
  have htrace : WordTrace (prefixWord ++ tailWord_1426107) baseStart_1426107 baseEnd_1426107 := by
    simpa [prefixWord, tailWord_1426107, baseEnd_1426107] using wordTrace_append hprefix tailTrace_1426107
  have hstable : (prefixWord ++ tailWord_1426107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426107).length < 2 ^ (prefixWord ++ tailWord_1426107).sum := by decide
  have hdescent : baseEnd_1426107 < baseStart_1426107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426132 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1426132 : Nat := 118140960795 + 1426132 * 2 ^ 59
def prefixEnd_1426132 : Nat := 4983230072969 + 3 ^ 40 * 1426132 * 2
def baseEnd_1426132 : Nat := 732291192757919485691345

theorem tailTrace_1426132 : CollatzResearch.WordTrace tailWord_1426132 prefixEnd_1426132 732291192757919485691345 := by
  unfold tailWord_1426132
  simp only [CollatzResearch.WordTrace]
  refine ⟨26007653634687401399796325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34676871512916535199728433 26007653634687401399796325)
  ·
    refine ⟨4876435056503887762461811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26007653634687401399796325 4876435056503887762461811)
    ·
      refine ⟨7314652584755831643692717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4876435056503887762461811 7314652584755831643692717)
      ·
        refine ⟨2742994719283436866384769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7314652584755831643692717 2742994719283436866384769)
        ·
          refine ⟨2057246039462577649788577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2742994719283436866384769 2057246039462577649788577)
          ·
            refine ⟨1542934529596933237341433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2057246039462577649788577 1542934529596933237341433)
            ·
              refine ⟨1157200897197699928006075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1542934529596933237341433 1157200897197699928006075)
              ·
                refine ⟨1735801345796549892009113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157200897197699928006075 1735801345796549892009113)
                ·
                  refine ⟨1301851009347412419006835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1735801345796549892009113 1301851009347412419006835)
                  ·
                    refine ⟨1952776514021118628510253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1301851009347412419006835 1952776514021118628510253)
                    ·
                      refine ⟨732291192757919485691345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1952776514021118628510253 732291192757919485691345)
                      ·
                        rfl

theorem cell23_1426132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1426132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426132 prefixEnd_1426132 := by exact prefixLift 1426132
  have htrace : WordTrace (prefixWord ++ tailWord_1426132) baseStart_1426132 baseEnd_1426132 := by
    simpa [prefixWord, tailWord_1426132, baseEnd_1426132] using wordTrace_append hprefix tailTrace_1426132
  have hstable : (prefixWord ++ tailWord_1426132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426132).length < 2 ^ (prefixWord ++ tailWord_1426132).sum := by decide
  have hdescent : baseEnd_1426132 < baseStart_1426132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426138 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2]
def baseStart_1426138 : Nat := 118140960795 + 1426138 * 2 ^ 59
def prefixEnd_1426138 : Nat := 4983230072969 + 3 ^ 40 * 1426138 * 2
def baseEnd_1426138 : Nat := 732294273641846462216317

theorem tailTrace_1426138 : CollatzResearch.WordTrace tailWord_1426138 prefixEnd_1426138 732294273641846462216317 := by
  unfold tailWord_1426138
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003881526838266456077767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34677017404902043882874045 13003881526838266456077767)
  ·
    refine ⟨19505822290257399684116651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13003881526838266456077767 19505822290257399684116651)
    ·
      refine ⟨29258733435386099526174977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19505822290257399684116651 29258733435386099526174977)
      ·
        refine ⟨21944050076539574644631233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29258733435386099526174977 21944050076539574644631233)
        ·
          refine ⟨16458037557404680983473425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21944050076539574644631233 16458037557404680983473425)
          ·
            refine ⟨12343528168053510737605069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16458037557404680983473425 12343528168053510737605069)
            ·
              refine ⟨4628823063020066526601901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12343528168053510737605069 4628823063020066526601901)
              ·
                refine ⟨1735808648632524947475713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4628823063020066526601901 1735808648632524947475713)
                ·
                  refine ⟨1301856486474393710606785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1735808648632524947475713 1301856486474393710606785)
                  ·
                    refine ⟨976392364855795282955089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1301856486474393710606785 976392364855795282955089)
                    ·
                      refine ⟨732294273641846462216317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976392364855795282955089 732294273641846462216317)
                      ·
                        rfl

theorem cell23_1426138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_1426138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426138 prefixEnd_1426138 := by exact prefixLift 1426138
  have htrace : WordTrace (prefixWord ++ tailWord_1426138) baseStart_1426138 baseEnd_1426138 := by
    simpa [prefixWord, tailWord_1426138, baseEnd_1426138] using wordTrace_append hprefix tailTrace_1426138
  have hstable : (prefixWord ++ tailWord_1426138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426138).length < 2 ^ (prefixWord ++ tailWord_1426138).sum := by decide
  have hdescent : baseEnd_1426138 < baseStart_1426138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426154 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_1426154 : Nat := 118140960795 + 1426154 * 2 ^ 59
def prefixEnd_1426154 : Nat := 4983230072969 + 3 ^ 40 * 1426154 * 2
def baseEnd_1426154 : Nat := 732302489332318399616243

theorem tailTrace_1426154 : CollatzResearch.WordTrace tailWord_1426154 prefixEnd_1426154 732302489332318399616243 := by
  unfold tailWord_1426154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004027418823775139223379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34677406450196733704595677 13004027418823775139223379)
  ·
    refine ⟨19506041128235662708835069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13004027418823775139223379 19506041128235662708835069)
    ·
      refine ⟨7314765423088373515813151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19506041128235662708835069 7314765423088373515813151)
      ·
        refine ⟨10972148134632560273719727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7314765423088373515813151 10972148134632560273719727)
        ·
          refine ⟨16458222201948840410579591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10972148134632560273719727 16458222201948840410579591)
          ·
            refine ⟨24687333302923260615869387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16458222201948840410579591 24687333302923260615869387)
            ·
              refine ⟨37030999954384890923804081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24687333302923260615869387 37030999954384890923804081)
              ·
                refine ⟨27773249965788668192853061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37030999954384890923804081 27773249965788668192853061)
                ·
                  refine ⟨5207484368585375286159949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27773249965788668192853061 5207484368585375286159949)
                  ·
                    refine ⟨1952806638219515732309981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5207484368585375286159949 1952806638219515732309981)
                    ·
                      refine ⟨732302489332318399616243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1952806638219515732309981 732302489332318399616243)
                      ·
                        rfl

theorem cell23_1426154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_1426154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426154 prefixEnd_1426154 := by exact prefixLift 1426154
  have htrace : WordTrace (prefixWord ++ tailWord_1426154) baseStart_1426154 baseEnd_1426154 := by
    simpa [prefixWord, tailWord_1426154, baseEnd_1426154] using wordTrace_append hprefix tailTrace_1426154
  have hstable : (prefixWord ++ tailWord_1426154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426154).length < 2 ^ (prefixWord ++ tailWord_1426154).sum := by decide
  have hdescent : baseEnd_1426154 < baseStart_1426154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426178 : List Nat := [3, 4, 1, 1, 1, 3, 1, 4, 5]
def baseStart_1426178 : Nat := 118140960795 + 1426178 * 2 ^ 59
def prefixEnd_1426178 : Nat := 4983230072969 + 3 ^ 40 * 1426178 * 2
def baseEnd_1426178 : Nat := 81368312540891811746237

theorem tailTrace_1426178 : CollatzResearch.WordTrace tailWord_1426178 prefixEnd_1426178 81368312540891811746237 := by
  unfold tailWord_1426178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004246256802038163941797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34677990018138768437178125 13004246256802038163941797)
  ·
    refine ⟨2438296173150382155739087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13004246256802038163941797 2438296173150382155739087)
    ·
      refine ⟨3657444259725573233608631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2438296173150382155739087 3657444259725573233608631)
      ·
        refine ⟨5486166389588359850412947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657444259725573233608631 5486166389588359850412947)
        ·
          refine ⟨8229249584382539775619421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5486166389588359850412947 8229249584382539775619421)
          ·
            refine ⟨3085968594143452415857283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8229249584382539775619421 3085968594143452415857283)
            ·
              refine ⟨4628952891215178623785925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085968594143452415857283 4628952891215178623785925)
              ·
                refine ⟨867928667102845991959861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4628952891215178623785925 867928667102845991959861)
                ·
                  refine ⟨81368312540891811746237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 867928667102845991959861 81368312540891811746237)
                  ·
                    rfl

theorem cell23_1426178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_1426178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426178 prefixEnd_1426178 := by exact prefixLift 1426178
  have htrace : WordTrace (prefixWord ++ tailWord_1426178) baseStart_1426178 baseEnd_1426178 := by
    simpa [prefixWord, tailWord_1426178, baseEnd_1426178] using wordTrace_append hprefix tailTrace_1426178
  have hstable : (prefixWord ++ tailWord_1426178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426178).length < 2 ^ (prefixWord ++ tailWord_1426178).sum := by decide
  have hdescent : baseEnd_1426178 < baseStart_1426178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426184 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_1426184 : Nat := 118140960795 + 1426184 * 2 ^ 59
def prefixEnd_1426184 : Nat := 4983230072969 + 3 ^ 40 * 1426184 * 2
def baseEnd_1426184 : Nat := 732317893751953282241105

theorem tailTrace_1426184 : CollatzResearch.WordTrace tailWord_1426184 prefixEnd_1426184 732317893751953282241105 := by
  unfold tailWord_1426184
  simp only [CollatzResearch.WordTrace]
  refine ⟨26008601932593207840242803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34678135910124277120323737 26008601932593207840242803)
  ·
    refine ⟨39012902898889811760364205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26008601932593207840242803 39012902898889811760364205)
    ·
      refine ⟨14629838587083679410136577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39012902898889811760364205 14629838587083679410136577)
      ·
        refine ⟨10972378940312759557602433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14629838587083679410136577 10972378940312759557602433)
        ·
          refine ⟨8229284205234569668201825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10972378940312759557602433 8229284205234569668201825)
          ·
            refine ⟨6171963153925927251151369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8229284205234569668201825 6171963153925927251151369)
            ·
              refine ⟨4628972365444445438363527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6171963153925927251151369 4628972365444445438363527)
              ·
                refine ⟨6943458548166668157545291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628972365444445438363527 6943458548166668157545291)
                ·
                  refine ⟨10415187822250002236317937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6943458548166668157545291 10415187822250002236317937)
                  ·
                    refine ⟨7811390866687501677238453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10415187822250002236317937 7811390866687501677238453)
                    ·
                      refine ⟨732317893751953282241105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7811390866687501677238453 732317893751953282241105)
                      ·
                        rfl

theorem cell23_1426184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_1426184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426184 prefixEnd_1426184 := by exact prefixLift 1426184
  have htrace : WordTrace (prefixWord ++ tailWord_1426184) baseStart_1426184 baseEnd_1426184 := by
    simpa [prefixWord, tailWord_1426184, baseEnd_1426184] using wordTrace_append hprefix tailTrace_1426184
  have hstable : (prefixWord ++ tailWord_1426184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426184).length < 2 ^ (prefixWord ++ tailWord_1426184).sum := by decide
  have hdescent : baseEnd_1426184 < baseStart_1426184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426187 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 2, 8]
def baseStart_1426187 : Nat := 118140960795 + 1426187 * 2 ^ 59
def prefixEnd_1426187 : Nat := 4983230072969 + 3 ^ 40 * 1426187 * 2
def baseEnd_1426187 : Nat := 244106478064638923501197

theorem tailTrace_1426187 : CollatzResearch.WordTrace tailWord_1426187 prefixEnd_1426187 244106478064638923501197 := by
  unfold tailWord_1426187
  simp only [CollatzResearch.WordTrace]
  refine ⟨52017313284175547192844815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34678208856117031461896543 52017313284175547192844815)
  ·
    refine ⟨78025969926263320789267223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52017313284175547192844815 78025969926263320789267223)
    ·
      refine ⟨117038954889394981183900835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78025969926263320789267223 117038954889394981183900835)
      ·
        refine ⟨175558432334092471775851253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117038954889394981183900835 175558432334092471775851253)
        ·
          refine ⟨16458603031321169228986055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175558432334092471775851253 16458603031321169228986055)
          ·
            refine ⟨24687904546981753843479083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16458603031321169228986055 24687904546981753843479083)
            ·
              refine ⟨37031856820472630765218625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24687904546981753843479083 37031856820472630765218625)
              ·
                refine ⟨27773892615354473073913969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37031856820472630765218625 27773892615354473073913969)
                ·
                  refine ⟨20830419461515854805435477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27773892615354473073913969 20830419461515854805435477)
                  ·
                    refine ⟨244106478064638923501197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20830419461515854805435477 244106478064638923501197)
                    ·
                      rfl

theorem cell23_1426187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 8].length) (baseStart_1426187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426187 prefixEnd_1426187 := by exact prefixLift 1426187
  have htrace : WordTrace (prefixWord ++ tailWord_1426187) baseStart_1426187 baseEnd_1426187 := by
    simpa [prefixWord, tailWord_1426187, baseEnd_1426187] using wordTrace_append hprefix tailTrace_1426187
  have hstable : (prefixWord ++ tailWord_1426187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426187).length < 2 ^ (prefixWord ++ tailWord_1426187).sum := by decide
  have hdescent : baseEnd_1426187 < baseStart_1426187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426217 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 10]
def baseStart_1426217 : Nat := 118140960795 + 1426217 * 2 ^ 59
def prefixEnd_1426217 : Nat := 4983230072969 + 3 ^ 40 * 1426217 * 2
def baseEnd_1426217 : Nat := 81370537623727961458717

theorem tailTrace_1426217 : CollatzResearch.WordTrace tailWord_1426217 prefixEnd_1426217 81370537623727961458717 := by
  unfold tailWord_1426217
  simp only [CollatzResearch.WordTrace]
  refine ⟨52018407474066862316436905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34678938316044574877624603 52018407474066862316436905)
  ·
    refine ⟨39013805605550146737327679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52018407474066862316436905 39013805605550146737327679)
    ·
      refine ⟨58520708408325220105991519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39013805605550146737327679 58520708408325220105991519)
      ·
        refine ⟨87781062612487830158987279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58520708408325220105991519 87781062612487830158987279)
        ·
          refine ⟨131671593918731745238480919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87781062612487830158987279 131671593918731745238480919)
          ·
            refine ⟨197507390878097617857721379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131671593918731745238480919 197507390878097617857721379)
            ·
              refine ⟨296261086317146426786582069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197507390878097617857721379 296261086317146426786582069)
              ·
                refine ⟨27774476842232477511242069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 296261086317146426786582069 27774476842232477511242069)
                ·
                  refine ⟨81370537623727961458717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 27774476842232477511242069 81370537623727961458717)
                  ·
                    rfl

theorem cell23_1426217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 10].length) (baseStart_1426217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426217 prefixEnd_1426217 := by exact prefixLift 1426217
  have htrace : WordTrace (prefixWord ++ tailWord_1426217) baseStart_1426217 baseEnd_1426217 := by
    simpa [prefixWord, tailWord_1426217, baseEnd_1426217] using wordTrace_append hprefix tailTrace_1426217
  have hstable : (prefixWord ++ tailWord_1426217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426217).length < 2 ^ (prefixWord ++ tailWord_1426217).sum := by decide
  have hdescent : baseEnd_1426217 < baseStart_1426217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426264 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 3, 5]
def baseStart_1426264 : Nat := 118140960795 + 1426264 * 2 ^ 59
def prefixEnd_1426264 : Nat := 4983230072969 + 3 ^ 40 * 1426264 * 2
def baseEnd_1426264 : Nat := 244119657401437656413579

theorem tailTrace_1426264 : CollatzResearch.WordTrace tailWord_1426264 prefixEnd_1426264 244119657401437656413579 := by
  unfold tailWord_1426264
  simp only [CollatzResearch.WordTrace]
  refine ⟨26010060852448294671698923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34680081136597726228931897 26010060852448294671698923)
  ·
    refine ⟨39015091278672442007548385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26010060852448294671698923 39015091278672442007548385)
    ·
      refine ⟨29261318459004331505661289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39015091278672442007548385 29261318459004331505661289)
      ·
        refine ⟨21945988844253248629245967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29261318459004331505661289 21945988844253248629245967)
        ·
          refine ⟨32918983266379872943868951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21945988844253248629245967 32918983266379872943868951)
          ·
            refine ⟨49378474899569809415803427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32918983266379872943868951 49378474899569809415803427)
            ·
              refine ⟨74067712349354714123705141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49378474899569809415803427 74067712349354714123705141)
              ·
                refine ⟨6943848032752004449097357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74067712349354714123705141 6943848032752004449097357)
                ·
                  refine ⟨2603943012282001668411509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6943848032752004449097357 2603943012282001668411509)
                  ·
                    refine ⟨244119657401437656413579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2603943012282001668411509 244119657401437656413579)
                    ·
                      rfl

theorem cell23_1426264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_1426264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426264 prefixEnd_1426264 := by exact prefixLift 1426264
  have htrace : WordTrace (prefixWord ++ tailWord_1426264) baseStart_1426264 baseEnd_1426264 := by
    simpa [prefixWord, tailWord_1426264, baseEnd_1426264] using wordTrace_append hprefix tailTrace_1426264
  have hstable : (prefixWord ++ tailWord_1426264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426264).length < 2 ^ (prefixWord ++ tailWord_1426264).sum := by decide
  have hdescent : baseEnd_1426264 < baseStart_1426264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426271 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 1, 5, 2]
def baseStart_1426271 : Nat := 118140960795 + 1426271 * 2 ^ 59
def prefixEnd_1426271 : Nat := 4983230072969 + 3 ^ 40 * 1426271 * 2
def baseEnd_1426271 : Nat := 732362566568894441853205

theorem tailTrace_1426271 : CollatzResearch.WordTrace tailWord_1426271 prefixEnd_1426271 732362566568894441853205 := by
  unfold tailWord_1426271
  simp only [CollatzResearch.WordTrace]
  refine ⟨52020377015871229538902667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34680251343914153025935111 52020377015871229538902667)
  ·
    refine ⟨78030565523806844308354001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52020377015871229538902667 78030565523806844308354001)
    ·
      refine ⟨58522924142855133231265501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78030565523806844308354001 58522924142855133231265501)
      ·
        refine ⟨21946096553570674961724563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58522924142855133231265501 21946096553570674961724563)
        ·
          refine ⟨32919144830356012442586845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21946096553570674961724563 32919144830356012442586845)
          ·
            refine ⟨12344679311383504665970067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32919144830356012442586845 12344679311383504665970067)
            ·
              refine ⟨18517018967075256998955101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12344679311383504665970067 18517018967075256998955101)
              ·
                refine ⟨6943882112653221374608163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18517018967075256998955101 6943882112653221374608163)
                ·
                  refine ⟨10415823168979832061912245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6943882112653221374608163 10415823168979832061912245)
                  ·
                    refine ⟨976483422091859255804273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10415823168979832061912245 976483422091859255804273)
                    ·
                      refine ⟨732362566568894441853205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976483422091859255804273 732362566568894441853205)
                      ·
                        rfl

theorem cell23_1426271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_1426271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426271 prefixEnd_1426271 := by exact prefixLift 1426271
  have htrace : WordTrace (prefixWord ++ tailWord_1426271) baseStart_1426271 baseEnd_1426271 := by
    simpa [prefixWord, tailWord_1426271, baseEnd_1426271] using wordTrace_append hprefix tailTrace_1426271
  have hstable : (prefixWord ++ tailWord_1426271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426271).length < 2 ^ (prefixWord ++ tailWord_1426271).sum := by decide
  have hdescent : baseEnd_1426271 < baseStart_1426271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426302 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_1426302 : Nat := 118140960795 + 1426302 * 2 ^ 59
def prefixEnd_1426302 : Nat := 4983230072969 + 3 ^ 40 * 1426302 * 2
def baseEnd_1426302 : Nat := 81375387163242646729507

theorem tailTrace_1426302 : CollatzResearch.WordTrace tailWord_1426302 prefixEnd_1426302 81375387163242646729507 := by
  unfold tailWord_1426302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6502688459844865229160145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34681005119172614555520773 6502688459844865229160145)
  ·
    refine ⟨4877016344883648921870109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6502688459844865229160145 4877016344883648921870109)
    ·
      refine ⟨1828881129331368345701291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4877016344883648921870109 1828881129331368345701291)
      ·
        refine ⟨2743321693997052518551937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828881129331368345701291 2743321693997052518551937)
        ·
          refine ⟨2057491270497789388913953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2743321693997052518551937 2057491270497789388913953)
          ·
            refine ⟨1543118452873342041685465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2057491270497789388913953 1543118452873342041685465)
            ·
              refine ⟨1157338839655006531264099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543118452873342041685465 1157338839655006531264099)
              ·
                refine ⟨1736008259482509796896149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157338839655006531264099 1736008259482509796896149)
                ·
                  refine ⟨81375387163242646729507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1736008259482509796896149 81375387163242646729507)
                  ·
                    rfl

theorem cell23_1426302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_1426302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426302 prefixEnd_1426302 := by exact prefixLift 1426302
  have htrace : WordTrace (prefixWord ++ tailWord_1426302) baseStart_1426302 baseEnd_1426302 := by
    simpa [prefixWord, tailWord_1426302, baseEnd_1426302] using wordTrace_append hprefix tailTrace_1426302
  have hstable : (prefixWord ++ tailWord_1426302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426302).length < 2 ^ (prefixWord ++ tailWord_1426302).sum := by decide
  have hdescent : baseEnd_1426302 < baseStart_1426302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426304 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_1426304 : Nat := 118140960795 + 1426304 * 2 ^ 59
def prefixEnd_1426304 : Nat := 4983230072969 + 3 ^ 40 * 1426304 * 2
def baseEnd_1426304 : Nat := 732379511430492812740553

theorem tailTrace_1426304 : CollatzResearch.WordTrace tailWord_1426304 prefixEnd_1426304 732379511430492812740553 := by
  unfold tailWord_1426304
  simp only [CollatzResearch.WordTrace]
  refine ⟨26010790312375838087426983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34681053749834450783235977 26010790312375838087426983)
  ·
    refine ⟨39016185468563757131140475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26010790312375838087426983 39016185468563757131140475)
    ·
      refine ⟨58524278202845635696710713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39016185468563757131140475 58524278202845635696710713)
      ·
        refine ⟨43893208652134226772533035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58524278202845635696710713 43893208652134226772533035)
        ·
          refine ⟨65839812978201340158799553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43893208652134226772533035 65839812978201340158799553)
          ·
            refine ⟨49379859733651005119099665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65839812978201340158799553 49379859733651005119099665)
            ·
              refine ⟨37034894800238253839324749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49379859733651005119099665 37034894800238253839324749)
              ·
                refine ⟨13888085550089345189746781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37034894800238253839324749 13888085550089345189746781)
                ·
                  refine ⟨5208032081283504446155043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13888085550089345189746781 5208032081283504446155043)
                  ·
                    refine ⟨7812048121925256669232565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208032081283504446155043 7812048121925256669232565)
                    ·
                      refine ⟨732379511430492812740553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7812048121925256669232565 732379511430492812740553)
                      ·
                        rfl

theorem cell23_1426304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_1426304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426304 prefixEnd_1426304 := by exact prefixLift 1426304
  have htrace : WordTrace (prefixWord ++ tailWord_1426304) baseStart_1426304 baseEnd_1426304 := by
    simpa [prefixWord, tailWord_1426304, baseEnd_1426304] using wordTrace_append hprefix tailTrace_1426304
  have hstable : (prefixWord ++ tailWord_1426304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426304).length < 2 ^ (prefixWord ++ tailWord_1426304).sum := by decide
  have hdescent : baseEnd_1426304 < baseStart_1426304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426322 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_1426322 : Nat := 118140960795 + 1426322 * 2 ^ 59
def prefixEnd_1426322 : Nat := 4983230072969 + 3 ^ 40 * 1426322 * 2
def baseEnd_1426322 : Nat := 732388754082273742315471

theorem tailTrace_1426322 : CollatzResearch.WordTrace tailWord_1426322 prefixEnd_1426322 732388754082273742315471 := by
  unfold tailWord_1426322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13005559284671616312252305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34681491425790976832672813 13005559284671616312252305)
  ·
    refine ⟨9754169463503712234189229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13005559284671616312252305 9754169463503712234189229)
    ·
      refine ⟨3657813548813892087820961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9754169463503712234189229 3657813548813892087820961)
      ·
        refine ⟨2743360161610419065865721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3657813548813892087820961 2743360161610419065865721)
        ·
          refine ⟨2057520121207814299399291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2743360161610419065865721 2057520121207814299399291)
          ·
            refine ⟨3086280181811721449098937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057520121207814299399291 3086280181811721449098937)
            ·
              refine ⟨2314710136358791086824203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3086280181811721449098937 2314710136358791086824203)
              ·
                refine ⟨3472065204538186630236305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314710136358791086824203 3472065204538186630236305)
                ·
                  refine ⟨2604048903403639972677229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472065204538186630236305 2604048903403639972677229)
                  ·
                    refine ⟨976518338776364989753961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604048903403639972677229 976518338776364989753961)
                    ·
                      refine ⟨732388754082273742315471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976518338776364989753961 732388754082273742315471)
                      ·
                        rfl

theorem cell23_1426322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_1426322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426322 prefixEnd_1426322 := by exact prefixLift 1426322
  have htrace : WordTrace (prefixWord ++ tailWord_1426322) baseStart_1426322 baseEnd_1426322 := by
    simpa [prefixWord, tailWord_1426322, baseEnd_1426322] using wordTrace_append hprefix tailTrace_1426322
  have hstable : (prefixWord ++ tailWord_1426322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426322).length < 2 ^ (prefixWord ++ tailWord_1426322).sum := by decide
  have hdescent : baseEnd_1426322 < baseStart_1426322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426335 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 1, 1, 4]
def baseStart_1426335 : Nat := 118140960795 + 1426335 * 2 ^ 59
def prefixEnd_1426335 : Nat := 4983230072969 + 3 ^ 40 * 1426335 * 2
def baseEnd_1426335 : Nat := 732395429330782191452911

theorem tailTrace_1426335 : CollatzResearch.WordTrace tailWord_1426335 prefixEnd_1426335 732395429330782191452911 := by
  unfold tailWord_1426335
  simp only [CollatzResearch.WordTrace]
  refine ⟨52022711287639368469232459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34681807525092912312821639 52022711287639368469232459)
  ·
    refine ⟨78034066931459052703848689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52022711287639368469232459 78034066931459052703848689)
    ·
      refine ⟨58525550198594289527886517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78034066931459052703848689 58525550198594289527886517)
      ·
        refine ⟨5486770331118214643239361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58525550198594289527886517 5486770331118214643239361)
        ·
          refine ⟨4115077748338660982429521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5486770331118214643239361 4115077748338660982429521)
          ·
            refine ⟨3086308311253995736822141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4115077748338660982429521 3086308311253995736822141)
            ·
              refine ⟨1157365616720248401308303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3086308311253995736822141 1157365616720248401308303)
              ·
                refine ⟨1736048425080372601962455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157365616720248401308303 1736048425080372601962455)
                ·
                  refine ⟨2604072637620558902943683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736048425080372601962455 2604072637620558902943683)
                  ·
                    refine ⟨3906108956430838354415525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2604072637620558902943683 3906108956430838354415525)
                    ·
                      refine ⟨732395429330782191452911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3906108956430838354415525 732395429330782191452911)
                      ·
                        rfl

theorem cell23_1426335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_1426335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426335 prefixEnd_1426335 := by exact prefixLift 1426335
  have htrace : WordTrace (prefixWord ++ tailWord_1426335) baseStart_1426335 baseEnd_1426335 := by
    simpa [prefixWord, tailWord_1426335, baseEnd_1426335] using wordTrace_append hprefix tailTrace_1426335
  have hstable : (prefixWord ++ tailWord_1426335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426335).length < 2 ^ (prefixWord ++ tailWord_1426335).sum := by decide
  have hdescent : baseEnd_1426335 < baseStart_1426335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426338 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1426338 : Nat := 118140960795 + 1426338 * 2 ^ 59
def prefixEnd_1426338 : Nat := 4983230072969 + 3 ^ 40 * 1426338 * 2
def baseEnd_1426338 : Nat := 732396969772745679715397

theorem tailTrace_1426338 : CollatzResearch.WordTrace tailWord_1426338 prefixEnd_1426338 732396969772745679715397 := by
  unfold tailWord_1426338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13005705176657124995397917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34681880471085666654394445 13005705176657124995397917)
  ·
    refine ⟨4877139441246421873274219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13005705176657124995397917 4877139441246421873274219)
    ·
      refine ⟨7315709161869632809911329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4877139441246421873274219 7315709161869632809911329)
      ·
        refine ⟨5486781871402224607433497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7315709161869632809911329 5486781871402224607433497)
        ·
          refine ⟨4115086403551668455575123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5486781871402224607433497 4115086403551668455575123)
          ·
            refine ⟨6172629605327502683362685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115086403551668455575123 6172629605327502683362685)
            ·
              refine ⟨2314736101997813506261007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6172629605327502683362685 2314736101997813506261007)
              ·
                refine ⟨3472104152996720259391511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314736101997813506261007 3472104152996720259391511)
                ·
                  refine ⟨5208156229495080389087267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472104152996720259391511 5208156229495080389087267)
                  ·
                    refine ⟨7812234344242620583630901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208156229495080389087267 7812234344242620583630901)
                    ·
                      refine ⟨732396969772745679715397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7812234344242620583630901 732396969772745679715397)
                      ·
                        rfl

theorem cell23_1426338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1426338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426338 prefixEnd_1426338 := by exact prefixLift 1426338
  have htrace : WordTrace (prefixWord ++ tailWord_1426338) baseStart_1426338 baseEnd_1426338 := by
    simpa [prefixWord, tailWord_1426338, baseEnd_1426338] using wordTrace_append hprefix tailTrace_1426338
  have hstable : (prefixWord ++ tailWord_1426338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426338).length < 2 ^ (prefixWord ++ tailWord_1426338).sum := by decide
  have hdescent : baseEnd_1426338 < baseStart_1426338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426368 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 3]
def baseStart_1426368 : Nat := 118140960795 + 1426368 * 2 ^ 59
def prefixEnd_1426368 : Nat := 4983230072969 + 3 ^ 40 * 1426368 * 2
def baseEnd_1426368 : Nat := 732412374192380562340259

theorem tailTrace_1426368 : CollatzResearch.WordTrace tailWord_1426368 prefixEnd_1426368 732412374192380562340259 := by
  unfold tailWord_1426368
  simp only [CollatzResearch.WordTrace]
  refine ⟨26011957448259907552591879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34682609931013210070122505 26011957448259907552591879)
  ·
    refine ⟨39017936172389861328887819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26011957448259907552591879 39017936172389861328887819)
    ·
      refine ⟨58526904258584791993331729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39017936172389861328887819 58526904258584791993331729)
      ·
        refine ⟨43895178193938593994998797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58526904258584791993331729 43895178193938593994998797)
        ·
          refine ⟨16460691822726972748124549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43895178193938593994998797 16460691822726972748124549)
          ·
            refine ⟨3086379716761307390273353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16460691822726972748124549 3086379716761307390273353)
            ·
              refine ⟨2314784787570980542705015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3086379716761307390273353 2314784787570980542705015)
              ·
                refine ⟨3472177181356470814057523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314784787570980542705015 3472177181356470814057523)
                ·
                  refine ⟨5208265772034706221086285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472177181356470814057523 5208265772034706221086285)
                  ·
                    refine ⟨1953099664513014832907357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5208265772034706221086285 1953099664513014832907357)
                    ·
                      refine ⟨732412374192380562340259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1953099664513014832907357 732412374192380562340259)
                      ·
                        rfl

theorem cell23_1426368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_1426368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426368 prefixEnd_1426368 := by exact prefixLift 1426368
  have htrace : WordTrace (prefixWord ++ tailWord_1426368) baseStart_1426368 baseEnd_1426368 := by
    simpa [prefixWord, tailWord_1426368, baseEnd_1426368] using wordTrace_append hprefix tailTrace_1426368
  have hstable : (prefixWord ++ tailWord_1426368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426368).length < 2 ^ (prefixWord ++ tailWord_1426368).sum := by decide
  have hdescent : baseEnd_1426368 < baseStart_1426368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426384 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 3, 8]
def baseStart_1426384 : Nat := 118140960795 + 1426384 * 2 ^ 59
def prefixEnd_1426384 : Nat := 4983230072969 + 3 ^ 40 * 1426384 * 2
def baseEnd_1426384 : Nat := 244140196627617499913395

theorem tailTrace_1426384 : CollatzResearch.WordTrace tailWord_1426384 prefixEnd_1426384 244140196627617499913395 := by
  unfold tailWord_1426384
  simp only [CollatzResearch.WordTrace]
  refine ⟨26012249232230924918883103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34682998976307899891844137 26012249232230924918883103)
  ·
    refine ⟨39018373848346387378324655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26012249232230924918883103 39018373848346387378324655)
    ·
      refine ⟨58527560772519581067486983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39018373848346387378324655 58527560772519581067486983)
      ·
        refine ⟨87791341158779371601230475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58527560772519581067486983 87791341158779371601230475)
        ·
          refine ⟨131687011738169057401845713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87791341158779371601230475 131687011738169057401845713)
          ·
            refine ⟨98765258803626793051384285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131687011738169057401845713 98765258803626793051384285)
            ·
              refine ⟨37036972051360047394269107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98765258803626793051384285 37036972051360047394269107)
              ·
                refine ⟨55555458077040071091403661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37036972051360047394269107 55555458077040071091403661)
                ·
                  refine ⟨20833296778890026659276373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55555458077040071091403661 20833296778890026659276373)
                  ·
                    refine ⟨244140196627617499913395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20833296778890026659276373 244140196627617499913395)
                    ·
                      rfl

theorem cell23_1426384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_1426384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426384 prefixEnd_1426384 := by exact prefixLift 1426384
  have htrace : WordTrace (prefixWord ++ tailWord_1426384) baseStart_1426384 baseEnd_1426384 := by
    simpa [prefixWord, tailWord_1426384, baseEnd_1426384] using wordTrace_append hprefix tailTrace_1426384
  have hstable : (prefixWord ++ tailWord_1426384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426384).length < 2 ^ (prefixWord ++ tailWord_1426384).sum := by decide
  have hdescent : baseEnd_1426384 < baseStart_1426384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426389 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 1, 2, 3]
def baseStart_1426389 : Nat := 118140960795 + 1426389 * 2 ^ 59
def prefixEnd_1426389 : Nat := 4983230072969 + 3 ^ 40 * 1426389 * 2
def baseEnd_1426389 : Nat := 732423157286124980177663

theorem tailTrace_1426389 : CollatzResearch.WordTrace tailWord_1426389 prefixEnd_1426389 732423157286124980177663 := by
  unfold tailWord_1426389
  simp only [CollatzResearch.WordTrace]
  refine ⟨52024680829443735691698221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34683120552962490461132147 52024680829443735691698221)
  ·
    refine ⟨19509255311041400884386833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52024680829443735691698221 19509255311041400884386833)
    ·
      refine ⟨14631941483281050663290125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19509255311041400884386833 14631941483281050663290125)
      ·
        refine ⟨5486978056230393998733797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14631941483281050663290125 5486978056230393998733797)
        ·
          refine ⟨1028808385543198874762587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5486978056230393998733797 1028808385543198874762587)
          ·
            refine ⟨1543212578314798312143881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028808385543198874762587 1543212578314798312143881)
            ·
              refine ⟨1157409433736098734107911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543212578314798312143881 1157409433736098734107911)
              ·
                refine ⟨1736114150604148101161867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157409433736098734107911 1736114150604148101161867)
                ·
                  refine ⟨2604171225906222151742801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736114150604148101161867 2604171225906222151742801)
                  ·
                    refine ⟨1953128419429666613807101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2604171225906222151742801 1953128419429666613807101)
                    ·
                      refine ⟨732423157286124980177663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1953128419429666613807101 732423157286124980177663)
                      ·
                        rfl

theorem cell23_1426389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_1426389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426389 prefixEnd_1426389 := by exact prefixLift 1426389
  have htrace : WordTrace (prefixWord ++ tailWord_1426389) baseStart_1426389 baseEnd_1426389 := by
    simpa [prefixWord, tailWord_1426389, baseEnd_1426389] using wordTrace_append hprefix tailTrace_1426389
  have hstable : (prefixWord ++ tailWord_1426389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426389).length < 2 ^ (prefixWord ++ tailWord_1426389).sum := by decide
  have hdescent : baseEnd_1426389 < baseStart_1426389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426402 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1426402 : Nat := 118140960795 + 1426402 * 2 ^ 59
def prefixEnd_1426402 : Nat := 4983230072969 + 3 ^ 40 * 1426402 * 2
def baseEnd_1426402 : Nat := 732429832534633429315103

theorem tailTrace_1426402 : CollatzResearch.WordTrace tailWord_1426402 prefixEnd_1426402 732429832534633429315103 := by
  unfold tailWord_1426402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13006288744599159727980365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34683436652264425941280973 13006288744599159727980365)
  ·
    refine ⟨4877358279224684897992637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13006288744599159727980365 4877358279224684897992637)
    ·
      refine ⟨1829009354709256836747239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4877358279224684897992637 1829009354709256836747239)
      ·
        refine ⟨2743514032063885255120859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829009354709256836747239 2743514032063885255120859)
        ·
          refine ⟨4115271048095827882681289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743514032063885255120859 4115271048095827882681289)
          ·
            refine ⟨3086453286071870912010967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4115271048095827882681289 3086453286071870912010967)
            ·
              refine ⟨4629679929107806368016451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3086453286071870912010967 4629679929107806368016451)
              ·
                refine ⟨6944519893661709552024677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4629679929107806368016451 6944519893661709552024677)
                ·
                  refine ⟨1302097480061570541004627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6944519893661709552024677 1302097480061570541004627)
                  ·
                    refine ⟨1953146220092355811506941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1302097480061570541004627 1953146220092355811506941)
                    ·
                      refine ⟨732429832534633429315103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1953146220092355811506941 732429832534633429315103)
                      ·
                        rfl

theorem cell23_1426402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1426402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426402 prefixEnd_1426402 := by exact prefixLift 1426402
  have htrace : WordTrace (prefixWord ++ tailWord_1426402) baseStart_1426402 baseEnd_1426402 := by
    simpa [prefixWord, tailWord_1426402, baseEnd_1426402] using wordTrace_append hprefix tailTrace_1426402
  have hstable : (prefixWord ++ tailWord_1426402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426402).length < 2 ^ (prefixWord ++ tailWord_1426402).sum := by decide
  have hdescent : baseEnd_1426402 < baseStart_1426402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426408 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_1426408 : Nat := 118140960795 + 1426408 * 2 ^ 59
def prefixEnd_1426408 : Nat := 4983230072969 + 3 ^ 40 * 1426408 * 2
def baseEnd_1426408 : Nat := 732432913418560405840075

theorem tailTrace_1426408 : CollatzResearch.WordTrace tailWord_1426408 prefixEnd_1426408 732432913418560405840075 := by
  unfold tailWord_1426408
  simp only [CollatzResearch.WordTrace]
  refine ⟨26012686908187450968319939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34683582544249934624426585 26012686908187450968319939)
  ·
    refine ⟨39019030362281176452479909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26012686908187450968319939 39019030362281176452479909)
    ·
      refine ⟨7316068192927720584839983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39019030362281176452479909 7316068192927720584839983)
      ·
        refine ⟨10974102289391580877259975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7316068192927720584839983 10974102289391580877259975)
        ·
          refine ⟨16461153434087371315889963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10974102289391580877259975 16461153434087371315889963)
          ·
            refine ⟨24691730151131056973834945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16461153434087371315889963 24691730151131056973834945)
            ·
              refine ⟨18518797613348292730376209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24691730151131056973834945 18518797613348292730376209)
              ·
                refine ⟨13889098210011219547782157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18518797613348292730376209 13889098210011219547782157)
                ·
                  refine ⟨5208411828754207330418309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13889098210011219547782157 5208411828754207330418309)
                  ·
                    refine ⟨976577217891413874453433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5208411828754207330418309 976577217891413874453433)
                    ·
                      refine ⟨732432913418560405840075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976577217891413874453433 732432913418560405840075)
                      ·
                        rfl

theorem cell23_1426408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_1426408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426408 prefixEnd_1426408 := by exact prefixLift 1426408
  have htrace : WordTrace (prefixWord ++ tailWord_1426408) baseStart_1426408 baseEnd_1426408 := by
    simpa [prefixWord, tailWord_1426408, baseEnd_1426408] using wordTrace_append hprefix tailTrace_1426408
  have hstable : (prefixWord ++ tailWord_1426408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426408).length < 2 ^ (prefixWord ++ tailWord_1426408).sum := by decide
  have hdescent : baseEnd_1426408 < baseStart_1426408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426441 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 1, 5, 3]
def baseStart_1426441 : Nat := 118140960795 + 1426441 * 2 ^ 59
def prefixEnd_1426441 : Nat := 4983230072969 + 3 ^ 40 * 1426441 * 2
def baseEnd_1426441 : Nat := 732449858280158776727423

theorem tailTrace_1426441 : CollatzResearch.WordTrace tailWord_1426441 prefixEnd_1426441 732449858280158776727423 := by
  unfold tailWord_1426441
  simp only [CollatzResearch.WordTrace]
  refine ⟨52026577425255348572591177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34684384950170232381727451 52026577425255348572591177)
  ·
    refine ⟨39019933068941511429443383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52026577425255348572591177 39019933068941511429443383)
    ·
      refine ⟨58529899603412267144165075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39019933068941511429443383 58529899603412267144165075)
      ·
        refine ⟨87794849405118400716247613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58529899603412267144165075 87794849405118400716247613)
        ·
          refine ⟨32923068526919400268592855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87794849405118400716247613 32923068526919400268592855)
          ·
            refine ⟨49384602790379100402889283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32923068526919400268592855 49384602790379100402889283)
            ·
              refine ⟨74076904185568650604333925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49384602790379100402889283 74076904185568650604333925)
              ·
                refine ⟨13889419534794121988312611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74076904185568650604333925 13889419534794121988312611)
                ·
                  refine ⟨20834129302191182982468917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13889419534794121988312611 20834129302191182982468917)
                  ·
                    refine ⟨1953199622080423404606461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20834129302191182982468917 1953199622080423404606461)
                    ·
                      refine ⟨732449858280158776727423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1953199622080423404606461 732449858280158776727423)
                      ·
                        rfl

theorem cell23_1426441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5, 3].length) (baseStart_1426441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426441 prefixEnd_1426441 := by exact prefixLift 1426441
  have htrace : WordTrace (prefixWord ++ tailWord_1426441) baseStart_1426441 baseEnd_1426441 := by
    simpa [prefixWord, tailWord_1426441, baseEnd_1426441] using wordTrace_append hprefix tailTrace_1426441
  have hstable : (prefixWord ++ tailWord_1426441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426441).length < 2 ^ (prefixWord ++ tailWord_1426441).sum := by decide
  have hdescent : baseEnd_1426441 < baseStart_1426441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426478 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1426478 : Nat := 118140960795 + 1426478 * 2 ^ 59
def prefixEnd_1426478 : Nat := 4983230072969 + 3 ^ 40 * 1426478 * 2
def baseEnd_1426478 : Nat := 244156285688125043988251

theorem tailTrace_1426478 : CollatzResearch.WordTrace tailWord_1426478 prefixEnd_1426478 244156285688125043988251 := by
  unfold tailWord_1426478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6503490865765162986461011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34685284617414202594458725 6503490865765162986461011)
  ·
    refine ⟨9755236298647744479691517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6503490865765162986461011 9755236298647744479691517)
    ·
      refine ⟨3658213611992904179884319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9755236298647744479691517 3658213611992904179884319)
      ·
        refine ⟨5487320417989356269826479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3658213611992904179884319 5487320417989356269826479)
        ·
          refine ⟨8230980626984034404739719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5487320417989356269826479 8230980626984034404739719)
          ·
            refine ⟨12346470940476051607109579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8230980626984034404739719 12346470940476051607109579)
            ·
              refine ⟨18519706410714077410664369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12346470940476051607109579 18519706410714077410664369)
              ·
                refine ⟨13889779808035558057998277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18519706410714077410664369 13889779808035558057998277)
                ·
                  refine ⟨2604333714006667135874677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13889779808035558057998277 2604333714006667135874677)
                  ·
                    refine ⟨244156285688125043988251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2604333714006667135874677 244156285688125043988251)
                    ·
                      rfl

theorem cell23_1426478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1426478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426478 prefixEnd_1426478 := by exact prefixLift 1426478
  have htrace : WordTrace (prefixWord ++ tailWord_1426478) baseStart_1426478 baseEnd_1426478 := by
    simpa [prefixWord, tailWord_1426478, baseEnd_1426478] using wordTrace_append hprefix tailTrace_1426478
  have hstable : (prefixWord ++ tailWord_1426478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426478).length < 2 ^ (prefixWord ++ tailWord_1426478).sum := by decide
  have hdescent : baseEnd_1426478 < baseStart_1426478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426549 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1426549 : Nat := 118140960795 + 1426549 * 2 ^ 59
def prefixEnd_1426549 : Nat := 4983230072969 + 3 ^ 40 * 1426549 * 2
def baseEnd_1426549 : Nat := 732505314190844354176927

theorem tailTrace_1426549 : CollatzResearch.WordTrace tailWord_1426549 prefixEnd_1426549 732505314190844354176927 := by
  unfold tailWord_1426549
  simp only [CollatzResearch.WordTrace]
  refine ⟨52030516508864083017522701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34687011005909388678348467 52030516508864083017522701)
  ·
    refine ⟨19511443690824031131571013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52030516508864083017522701 19511443690824031131571013)
    ·
      refine ⟨3658395692029505837169565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19511443690824031131571013 3658395692029505837169565)
      ·
        refine ⟨1371898384511064688938587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3658395692029505837169565 1371898384511064688938587)
        ·
          refine ⟨2057847576766597033407881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371898384511064688938587 2057847576766597033407881)
          ·
            refine ⟨1543385682574947775055911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2057847576766597033407881 1543385682574947775055911)
            ·
              refine ⟨2315078523862421662583867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543385682574947775055911 2315078523862421662583867)
              ·
                refine ⟨3472617785793632493875801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2315078523862421662583867 3472617785793632493875801)
                ·
                  refine ⟨2604463339345224370406851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472617785793632493875801 2604463339345224370406851)
                  ·
                    refine ⟨3906695009017836555610277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2604463339345224370406851 3906695009017836555610277)
                    ·
                      refine ⟨732505314190844354176927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3906695009017836555610277 732505314190844354176927)
                      ·
                        rfl

theorem cell23_1426549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1426549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426549 prefixEnd_1426549 := by exact prefixLift 1426549
  have htrace : WordTrace (prefixWord ++ tailWord_1426549) baseStart_1426549 baseEnd_1426549 := by
    simpa [prefixWord, tailWord_1426549, baseEnd_1426549] using wordTrace_append hprefix tailTrace_1426549
  have hstable : (prefixWord ++ tailWord_1426549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426549).length < 2 ^ (prefixWord ++ tailWord_1426549).sum := by decide
  have hdescent : baseEnd_1426549 < baseStart_1426549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426602 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1426602 : Nat := 118140960795 + 1426602 * 2 ^ 59
def prefixEnd_1426602 : Nat := 4983230072969 + 3 ^ 40 * 1426602 * 2
def baseEnd_1426602 : Nat := 244177509555177548938061

theorem tailTrace_1426602 : CollatzResearch.WordTrace tailWord_1426602 prefixEnd_1426602 244177509555177548938061 := by
  unfold tailWord_1426602
  simp only [CollatzResearch.WordTrace]
  refine ⟨13008112394418018267300515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34688299718448048712801373 13008112394418018267300515)
  ·
    refine ⟨19512168591627027400950773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13008112394418018267300515 19512168591627027400950773)
    ·
      refine ⟨1829265805465033818839135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19512168591627027400950773 1829265805465033818839135)
      ·
        refine ⟨2743898708197550728258703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829265805465033818839135 2743898708197550728258703)
        ·
          refine ⟨4115848062296326092388055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743898708197550728258703 4115848062296326092388055)
          ·
            refine ⟨6173772093444489138582083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115848062296326092388055 6173772093444489138582083)
            ·
              refine ⟨9260658140166733707873125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6173772093444489138582083 9260658140166733707873125)
              ·
                refine ⟨1736373401281262570226211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9260658140166733707873125 1736373401281262570226211)
                ·
                  refine ⟨2604560101921893855339317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736373401281262570226211 2604560101921893855339317)
                  ·
                    refine ⟨244177509555177548938061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2604560101921893855339317 244177509555177548938061)
                    ·
                      rfl

theorem cell23_1426602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1426602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426602 prefixEnd_1426602 := by exact prefixLift 1426602
  have htrace : WordTrace (prefixWord ++ tailWord_1426602) baseStart_1426602 baseEnd_1426602 := by
    simpa [prefixWord, tailWord_1426602, baseEnd_1426602] using wordTrace_append hprefix tailTrace_1426602
  have hstable : (prefixWord ++ tailWord_1426602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426602).length < 2 ^ (prefixWord ++ tailWord_1426602).sum := by decide
  have hdescent : baseEnd_1426602 < baseStart_1426602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426618 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_1426618 : Nat := 118140960795 + 1426618 * 2 ^ 59
def prefixEnd_1426618 : Nat := 4983230072969 + 3 ^ 40 * 1426618 * 2
def baseEnd_1426618 : Nat := 732540744356004584214109

theorem tailTrace_1426618 : CollatzResearch.WordTrace tailWord_1426618 prefixEnd_1426618 732540744356004584214109 := by
  unfold tailWord_1426618
  simp only [CollatzResearch.WordTrace]
  refine ⟨13008258286403526950446127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34688688763742738534523005 13008258286403526950446127)
  ·
    refine ⟨19512387429605290425669191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13008258286403526950446127 19512387429605290425669191)
    ·
      refine ⟨29268581144407935638503787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19512387429605290425669191 29268581144407935638503787)
      ·
        refine ⟨43902871716611903457755681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29268581144407935638503787 43902871716611903457755681)
        ·
          refine ⟨32927153787458927593316761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43902871716611903457755681 32927153787458927593316761)
          ·
            refine ⟨24695365340594195694987571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32927153787458927593316761 24695365340594195694987571)
            ·
              refine ⟨37043048010891293542481357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24695365340594195694987571 37043048010891293542481357)
              ·
                refine ⟨13891143004084235078430509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37043048010891293542481357 13891143004084235078430509)
                ·
                  refine ⟨5209178626531588154411441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13891143004084235078430509 5209178626531588154411441)
                  ·
                    refine ⟨3906883969898691115808581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5209178626531588154411441 3906883969898691115808581)
                    ·
                      refine ⟨732540744356004584214109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3906883969898691115808581 732540744356004584214109)
                      ·
                        rfl

theorem cell23_1426618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_1426618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426618 prefixEnd_1426618 := by exact prefixLift 1426618
  have htrace : WordTrace (prefixWord ++ tailWord_1426618) baseStart_1426618 baseEnd_1426618 := by
    simpa [prefixWord, tailWord_1426618, baseEnd_1426618] using wordTrace_append hprefix tailTrace_1426618
  have hstable : (prefixWord ++ tailWord_1426618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426618).length < 2 ^ (prefixWord ++ tailWord_1426618).sum := by decide
  have hdescent : baseEnd_1426618 < baseStart_1426618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426622 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_1426622 : Nat := 118140960795 + 1426622 * 2 ^ 59
def prefixEnd_1426622 : Nat := 4983230072969 + 3 ^ 40 * 1426622 * 2
def baseEnd_1426622 : Nat := 732542798278622568564091

theorem tailTrace_1426622 : CollatzResearch.WordTrace tailWord_1426622 prefixEnd_1426622 732542798278622568564091 := by
  unfold tailWord_1426622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504147379699952060616265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34688786025066410989953413 6504147379699952060616265)
  ·
    refine ⟨4878110534774964045462199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6504147379699952060616265 4878110534774964045462199)
    ·
      refine ⟨7317165802162446068193299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4878110534774964045462199 7317165802162446068193299)
      ·
        refine ⟨10975748703243669102289949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7317165802162446068193299 10975748703243669102289949)
        ·
          refine ⟨4115905763716375913358731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10975748703243669102289949 4115905763716375913358731)
          ·
            refine ⟨6173858645574563870038097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115905763716375913358731 6173858645574563870038097)
            ·
              refine ⟨4630393984180922902528573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6173858645574563870038097 4630393984180922902528573)
              ·
                refine ⟨1736397744067846088448215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4630393984180922902528573 1736397744067846088448215)
                ·
                  refine ⟨2604596616101769132672323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736397744067846088448215 2604596616101769132672323)
                  ·
                    refine ⟨3906894924152653699008485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2604596616101769132672323 3906894924152653699008485)
                    ·
                      refine ⟨732542798278622568564091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3906894924152653699008485 732542798278622568564091)
                      ·
                        rfl

theorem cell23_1426622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_1426622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426622 prefixEnd_1426622 := by exact prefixLift 1426622
  have htrace : WordTrace (prefixWord ++ tailWord_1426622) baseStart_1426622 baseEnd_1426622 := by
    simpa [prefixWord, tailWord_1426622, baseEnd_1426622] using wordTrace_append hprefix tailTrace_1426622
  have hstable : (prefixWord ++ tailWord_1426622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426622).length < 2 ^ (prefixWord ++ tailWord_1426622).sum := by decide
  have hdescent : baseEnd_1426622 < baseStart_1426622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426645 : List Nat := [1, 3, 2, 4, 1, 2, 2, 8]
def baseStart_1426645 : Nat := 118140960795 + 1426645 * 2 ^ 59
def prefixEnd_1426645 : Nat := 4983230072969 + 3 ^ 40 * 1426645 * 2
def baseEnd_1426645 : Nat := 27131652160506517725055

theorem tailTrace_1426645 : CollatzResearch.WordTrace tailWord_1426645 prefixEnd_1426645 27131652160506517725055 := by
  unfold tailWord_1426645
  simp only [CollatzResearch.WordTrace]
  refine ⟨52034017916516291413017389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34689345277677527608678259 52034017916516291413017389)
  ·
    refine ⟨19512756718693609279881521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52034017916516291413017389 19512756718693609279881521)
    ·
      refine ⟨14634567539020206959911141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19512756718693609279881521 14634567539020206959911141)
      ·
        refine ⟨2743981413566288804983339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14634567539020206959911141 2743981413566288804983339)
        ·
          refine ⟨4115972120349433207475009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743981413566288804983339 4115972120349433207475009)
          ·
            refine ⟨3086979090262074905606257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4115972120349433207475009 3086979090262074905606257)
            ·
              refine ⟨2315234317696556179204693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3086979090262074905606257 2315234317696556179204693)
              ·
                refine ⟨27131652160506517725055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2315234317696556179204693 27131652160506517725055)
                ·
                  rfl

theorem cell23_1426645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 8].length) (baseStart_1426645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426645 prefixEnd_1426645 := by exact prefixLift 1426645
  have htrace : WordTrace (prefixWord ++ tailWord_1426645) baseStart_1426645 baseEnd_1426645 := by
    simpa [prefixWord, tailWord_1426645, baseEnd_1426645] using wordTrace_append hprefix tailTrace_1426645
  have hstable : (prefixWord ++ tailWord_1426645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426645).length < 2 ^ (prefixWord ++ tailWord_1426645).sum := by decide
  have hdescent : baseEnd_1426645 < baseStart_1426645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426688 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 2, 6]
def baseStart_1426688 : Nat := 118140960795 + 1426688 * 2 ^ 59
def prefixEnd_1426688 : Nat := 4983230072969 + 3 ^ 40 * 1426688 * 2
def baseEnd_1426688 : Nat := 244192229333939770112929

theorem tailTrace_1426688 : CollatzResearch.WordTrace tailWord_1426688 prefixEnd_1426688 244192229333939770112929 := by
  unfold tailWord_1426688
  simp only [CollatzResearch.WordTrace]
  refine ⟨26017793127680254878416359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34690390836907006504555145 26017793127680254878416359)
  ·
    refine ⟨39026689691520382317624539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26017793127680254878416359 39026689691520382317624539)
    ·
      refine ⟨58540034537280573476436809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39026689691520382317624539 58540034537280573476436809)
      ·
        refine ⟨43905025902960430107327607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58540034537280573476436809 43905025902960430107327607)
        ·
          refine ⟨65857538854440645160991411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43905025902960430107327607 65857538854440645160991411)
          ·
            refine ⟨98786308281660967741487117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65857538854440645160991411 98786308281660967741487117)
            ·
              refine ⟨37044865605622862903057669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98786308281660967741487117 37044865605622862903057669)
              ·
                refine ⟨6945912301054286794323313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37044865605622862903057669 6945912301054286794323313)
                ·
                  refine ⟨5209434225790715095742485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6945912301054286794323313 5209434225790715095742485)
                  ·
                    refine ⟨244192229333939770112929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5209434225790715095742485 244192229333939770112929)
                    ·
                      rfl

theorem cell23_1426688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_1426688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426688 prefixEnd_1426688 := by exact prefixLift 1426688
  have htrace : WordTrace (prefixWord ++ tailWord_1426688) baseStart_1426688 baseEnd_1426688 := by
    simpa [prefixWord, tailWord_1426688, baseEnd_1426688] using wordTrace_append hprefix tailTrace_1426688
  have hstable : (prefixWord ++ tailWord_1426688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426688).length < 2 ^ (prefixWord ++ tailWord_1426688).sum := by decide
  have hdescent : baseEnd_1426688 < baseStart_1426688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426689 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_1426689 : Nat := 118140960795 + 1426689 * 2 ^ 59
def prefixEnd_1426689 : Nat := 4983230072969 + 3 ^ 40 * 1426689 * 2
def baseEnd_1426689 : Nat := 732577201482473806426283

theorem tailTrace_1426689 : CollatzResearch.WordTrace tailWord_1426689 prefixEnd_1426689 732577201482473806426283 := by
  unfold tailWord_1426689
  simp only [CollatzResearch.WordTrace]
  refine ⟨52035622728356886927619121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34690415152237924618412747 52035622728356886927619121)
  ·
    refine ⟨39026717046267665195714341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52035622728356886927619121 39026717046267665195714341)
    ·
      refine ⟨7317509446175187224196439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39026717046267665195714341 7317509446175187224196439)
      ·
        refine ⟨10976264169262780836294659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7317509446175187224196439 10976264169262780836294659)
        ·
          refine ⟨16464396253894171254441989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10976264169262780836294659 16464396253894171254441989)
          ·
            refine ⟨3087074297605157110207873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16464396253894171254441989 3087074297605157110207873)
            ·
              refine ⟨2315305723203867832655905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3087074297605157110207873 2315305723203867832655905)
              ·
                refine ⟨1736479292402900874491929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2315305723203867832655905 1736479292402900874491929)
                ·
                  refine ⟨1302359469302175655868947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1736479292402900874491929 1302359469302175655868947)
                  ·
                    refine ⟨1953539203953263483803421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1302359469302175655868947 1953539203953263483803421)
                    ·
                      refine ⟨732577201482473806426283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1953539203953263483803421 732577201482473806426283)
                      ·
                        rfl

theorem cell23_1426689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_1426689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426689 prefixEnd_1426689 := by exact prefixLift 1426689
  have htrace : WordTrace (prefixWord ++ tailWord_1426689) baseStart_1426689 baseEnd_1426689 := by
    simpa [prefixWord, tailWord_1426689, baseEnd_1426689] using wordTrace_append hprefix tailTrace_1426689
  have hstable : (prefixWord ++ tailWord_1426689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426689).length < 2 ^ (prefixWord ++ tailWord_1426689).sum := by decide
  have hdescent : baseEnd_1426689 < baseStart_1426689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426706 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1426706 : Nat := 118140960795 + 1426706 * 2 ^ 59
def prefixEnd_1426706 : Nat := 4983230072969 + 3 ^ 40 * 1426706 * 2
def baseEnd_1426706 : Nat := 732585930653600239913705

theorem tailTrace_1426706 : CollatzResearch.WordTrace tailWord_1426706 prefixEnd_1426706 732585930653600239913705 := by
  unfold tailWord_1426706
  simp only [CollatzResearch.WordTrace]
  refine ⟨13009060692323824707746993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34690828512863532553991981 13009060692323824707746993)
  ·
    refine ⟨9756795519242868530810245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13009060692323824707746993 9756795519242868530810245)
    ·
      refine ⟨1829399159858037849526921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9756795519242868530810245 1829399159858037849526921)
      ·
        refine ⟨1372049369893528387145191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1829399159858037849526921 1372049369893528387145191)
        ·
          refine ⟨2058074054840292580717787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372049369893528387145191 2058074054840292580717787)
          ·
            refine ⟨3087111082260438871076681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058074054840292580717787 3087111082260438871076681)
            ·
              refine ⟨2315333311695329153307511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3087111082260438871076681 2315333311695329153307511)
              ·
                refine ⟨3472999967542993729961267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2315333311695329153307511 3472999967542993729961267)
                ·
                  refine ⟨5209499951314490594941901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472999967542993729961267 5209499951314490594941901)
                  ·
                    refine ⟨1953562481742933973103213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5209499951314490594941901 1953562481742933973103213)
                    ·
                      refine ⟨732585930653600239913705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1953562481742933973103213 732585930653600239913705)
                      ·
                        rfl

theorem cell23_1426706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1426706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426706 prefixEnd_1426706 := by exact prefixLift 1426706
  have htrace : WordTrace (prefixWord ++ tailWord_1426706) baseStart_1426706 baseEnd_1426706 := by
    simpa [prefixWord, tailWord_1426706, baseEnd_1426706] using wordTrace_append hprefix tailTrace_1426706
  have hstable : (prefixWord ++ tailWord_1426706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426706).length < 2 ^ (prefixWord ++ tailWord_1426706).sum := by decide
  have hdescent : baseEnd_1426706 < baseStart_1426706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426712 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 1, 4, 2]
def baseStart_1426712 : Nat := 118140960795 + 1426712 * 2 ^ 59
def prefixEnd_1426712 : Nat := 4983230072969 + 3 ^ 40 * 1426712 * 2
def baseEnd_1426712 : Nat := 732589011537527216438677

theorem tailTrace_1426712 : CollatzResearch.WordTrace tailWord_1426712 prefixEnd_1426712 732589011537527216438677 := by
  unfold tailWord_1426712
  simp only [CollatzResearch.WordTrace]
  refine ⟨26018230803636780927853195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34690974404849041237137593 26018230803636780927853195)
  ·
    refine ⟨39027346205455171391779793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26018230803636780927853195 39027346205455171391779793)
    ·
      refine ⟨29270509654091378543834845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39027346205455171391779793 29270509654091378543834845)
      ·
        refine ⟨10976441120284266953938067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29270509654091378543834845 10976441120284266953938067)
        ·
          refine ⟨16464661680426400430907101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10976441120284266953938067 16464661680426400430907101)
          ·
            refine ⟨6174248130159900161590163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16464661680426400430907101 6174248130159900161590163)
            ·
              refine ⟨9261372195239850242385245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6174248130159900161590163 9261372195239850242385245)
              ·
                refine ⟨3473014573214943840894467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9261372195239850242385245 3473014573214943840894467)
                ·
                  refine ⟨5209521859822415761341701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3473014573214943840894467 5209521859822415761341701)
                  ·
                    refine ⟨976785348716702955251569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5209521859822415761341701 976785348716702955251569)
                    ·
                      refine ⟨732589011537527216438677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976785348716702955251569 732589011537527216438677)
                      ·
                        rfl

theorem cell23_1426712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_1426712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426712 prefixEnd_1426712 := by exact prefixLift 1426712
  have htrace : WordTrace (prefixWord ++ tailWord_1426712) baseStart_1426712 baseEnd_1426712 := by
    simpa [prefixWord, tailWord_1426712, baseEnd_1426712] using wordTrace_append hprefix tailTrace_1426712
  have hstable : (prefixWord ++ tailWord_1426712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426712).length < 2 ^ (prefixWord ++ tailWord_1426712).sum := by decide
  have hdescent : baseEnd_1426712 < baseStart_1426712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426733 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_1426733 : Nat := 118140960795 + 1426733 * 2 ^ 59
def prefixEnd_1426733 : Nat := 4983230072969 + 3 ^ 40 * 1426733 * 2
def baseEnd_1426733 : Nat := 732599794631271634276081

theorem tailTrace_1426733 : CollatzResearch.WordTrace tailWord_1426733 prefixEnd_1426733 732599794631271634276081 := by
  unfold tailWord_1426733
  simp only [CollatzResearch.WordTrace]
  refine ⟨52037227540197482442220853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34691485026798321628147235 52037227540197482442220853)
  ·
    refine ⟨4878490081893513978958205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52037227540197482442220853 4878490081893513978958205)
    ·
      refine ⟨1829433780710067742109327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4878490081893513978958205 1829433780710067742109327)
      ·
        refine ⟨2744150671065101613163991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829433780710067742109327 2744150671065101613163991)
        ·
          refine ⟨4116226006597652419745987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2744150671065101613163991 4116226006597652419745987)
          ·
            refine ⟨6174339009896478629618981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4116226006597652419745987 6174339009896478629618981)
            ·
              refine ⟨1157688564355589743053559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6174339009896478629618981 1157688564355589743053559)
              ·
                refine ⟨1736532846533384614580339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157688564355589743053559 1736532846533384614580339)
                ·
                  refine ⟨2604799269800076921870509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736532846533384614580339 2604799269800076921870509)
                  ·
                    refine ⟨976799726175028845701441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604799269800076921870509 976799726175028845701441)
                    ·
                      refine ⟨732599794631271634276081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976799726175028845701441 732599794631271634276081)
                      ·
                        rfl

theorem cell23_1426733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_1426733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426733 prefixEnd_1426733 := by exact prefixLift 1426733
  have htrace : WordTrace (prefixWord ++ tailWord_1426733) baseStart_1426733 baseEnd_1426733 := by
    simpa [prefixWord, tailWord_1426733, baseEnd_1426733] using wordTrace_append hprefix tailTrace_1426733
  have hstable : (prefixWord ++ tailWord_1426733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426733).length < 2 ^ (prefixWord ++ tailWord_1426733).sum := by decide
  have hdescent : baseEnd_1426733 < baseStart_1426733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426785 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_1426785 : Nat := 118140960795 + 1426785 * 2 ^ 59
def prefixEnd_1426785 : Nat := 4983230072969 + 3 ^ 40 * 1426785 * 2
def baseEnd_1426785 : Nat := 732626495625305430825841

theorem tailTrace_1426785 : CollatzResearch.WordTrace tailWord_1426785 prefixEnd_1426785 732626495625305430825841 := by
  unfold tailWord_1426785
  simp only [CollatzResearch.WordTrace]
  refine ⟨52039124136009095323113809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34692749424006063548742539 52039124136009095323113809)
  ·
    refine ⟨39029343102006821492335357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52039124136009095323113809 39029343102006821492335357)
    ·
      refine ⟨14636003663252558059625759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39029343102006821492335357 14636003663252558059625759)
      ·
        refine ⟨21954005494878837089438639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14636003663252558059625759 21954005494878837089438639)
        ·
          refine ⟨32931008242318255634157959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21954005494878837089438639 32931008242318255634157959)
          ·
            refine ⟨49396512363477383451236939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32931008242318255634157959 49396512363477383451236939)
            ·
              refine ⟨74094768545216075176855409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49396512363477383451236939 74094768545216075176855409)
              ·
                refine ⟨55571076408912056382641557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74094768545216075176855409 55571076408912056382641557)
                ·
                  refine ⟨2604894206667752642936323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55571076408912056382641557 2604894206667752642936323)
                  ·
                    refine ⟨3907341310001628964404485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2604894206667752642936323 3907341310001628964404485)
                    ·
                      refine ⟨732626495625305430825841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3907341310001628964404485 732626495625305430825841)
                      ·
                        rfl

theorem cell23_1426785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_1426785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426785 prefixEnd_1426785 := by exact prefixLift 1426785
  have htrace : WordTrace (prefixWord ++ tailWord_1426785) baseStart_1426785 baseEnd_1426785 := by
    simpa [prefixWord, tailWord_1426785, baseEnd_1426785] using wordTrace_append hprefix tailTrace_1426785
  have hstable : (prefixWord ++ tailWord_1426785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426785).length < 2 ^ (prefixWord ++ tailWord_1426785).sum := by decide
  have hdescent : baseEnd_1426785 < baseStart_1426785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426802 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1426802 : Nat := 118140960795 + 1426802 * 2 ^ 59
def prefixEnd_1426802 : Nat := 4983230072969 + 3 ^ 40 * 1426802 * 2
def baseEnd_1426802 : Nat := 732635224796431864313263

theorem tailTrace_1426802 : CollatzResearch.WordTrace tailWord_1426802 prefixEnd_1426802 732635224796431864313263 := by
  unfold tailWord_1426802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13009936044236876806620665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34693162784631671484321773 13009936044236876806620665)
  ·
    refine ⟨9757452033177657604965499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13009936044236876806620665 9757452033177657604965499)
    ·
      refine ⟨14636178049766486407448249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9757452033177657604965499 14636178049766486407448249)
      ·
        refine ⟨10977133537324864805586187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14636178049766486407448249 10977133537324864805586187)
        ·
          refine ⟨16465700305987297208379281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10977133537324864805586187 16465700305987297208379281)
          ·
            refine ⟨12349275229490472906284461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16465700305987297208379281 12349275229490472906284461)
            ·
              refine ⟨4630978211058927339856673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12349275229490472906284461 4630978211058927339856673)
              ·
                refine ⟨3473233658294195504892505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4630978211058927339856673 3473233658294195504892505)
                ·
                  refine ⟨2604925243720646628669379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3473233658294195504892505 2604925243720646628669379)
                  ·
                    refine ⟨3907387865580969943004069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2604925243720646628669379 3907387865580969943004069)
                    ·
                      refine ⟨732635224796431864313263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3907387865580969943004069 732635224796431864313263)
                      ·
                        rfl

theorem cell23_1426802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1426802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426802 prefixEnd_1426802 := by exact prefixLift 1426802
  have htrace : WordTrace (prefixWord ++ tailWord_1426802) baseStart_1426802 baseEnd_1426802 := by
    simpa [prefixWord, tailWord_1426802, baseEnd_1426802] using wordTrace_append hprefix tailTrace_1426802
  have hstable : (prefixWord ++ tailWord_1426802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426802).length < 2 ^ (prefixWord ++ tailWord_1426802).sum := by decide
  have hdescent : baseEnd_1426802 < baseStart_1426802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426814 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1426814 : Nat := 118140960795 + 1426814 * 2 ^ 59
def prefixEnd_1426814 : Nat := 4983230072969 + 3 ^ 40 * 1426814 * 2
def baseEnd_1426814 : Nat := 732641386564285817363209

theorem tailTrace_1426814 : CollatzResearch.WordTrace tailWord_1426814 prefixEnd_1426814 732641386564285817363209 := by
  unfold tailWord_1426814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6505022731613004159489937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34693454568602688850612997 6505022731613004159489937)
  ·
    refine ⟨4878767048709753119617453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6505022731613004159489937 4878767048709753119617453)
    ·
      refine ⟨1829537643266157419856545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4878767048709753119617453 1829537643266157419856545)
      ·
        refine ⟨1372153232449618064892409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1829537643266157419856545 1372153232449618064892409)
        ·
          refine ⟨1029114924337213548669307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1372153232449618064892409 1029114924337213548669307)
          ·
            refine ⟨1543672386505820323003961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029114924337213548669307 1543672386505820323003961)
            ·
              refine ⟨1157754289879365242252971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543672386505820323003961 1157754289879365242252971)
              ·
                refine ⟨1736631434819047863379457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157754289879365242252971 1736631434819047863379457)
                ·
                  refine ⟨1302473576114285897534593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1736631434819047863379457 1302473576114285897534593)
                  ·
                    refine ⟨976855182085714423150945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1302473576114285897534593 976855182085714423150945)
                    ·
                      refine ⟨732641386564285817363209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976855182085714423150945 732641386564285817363209)
                      ·
                        rfl

theorem cell23_1426814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1426814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426814 prefixEnd_1426814 := by exact prefixLift 1426814
  have htrace : WordTrace (prefixWord ++ tailWord_1426814) baseStart_1426814 baseEnd_1426814 := by
    simpa [prefixWord, tailWord_1426814, baseEnd_1426814] using wordTrace_append hprefix tailTrace_1426814
  have hstable : (prefixWord ++ tailWord_1426814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426814).length < 2 ^ (prefixWord ++ tailWord_1426814).sum := by decide
  have hdescent : baseEnd_1426814 < baseStart_1426814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426906 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 1, 5]
def baseStart_1426906 : Nat := 118140960795 + 1426906 * 2 ^ 59
def prefixEnd_1426906 : Nat := 4983230072969 + 3 ^ 40 * 1426906 * 2
def baseEnd_1426906 : Nat := 244229542261499819137595

theorem tailTrace_1426906 : CollatzResearch.WordTrace tailWord_1426906 prefixEnd_1426906 244229542261499819137595 := by
  unfold tailWord_1426906
  simp only [CollatzResearch.WordTrace]
  refine ⟨13010884342142683247067143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34695691579047155325512381 13010884342142683247067143)
  ·
    refine ⟨19516326513214024870600715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13010884342142683247067143 19516326513214024870600715)
    ·
      refine ⟨29274489769821037305901073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19516326513214024870600715 29274489769821037305901073)
      ·
        refine ⟨21955867327365777979425805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29274489769821037305901073 21955867327365777979425805)
        ·
          refine ⟨8233450247762166742284677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21955867327365777979425805 8233450247762166742284677)
          ·
            refine ⟨1543771921455406264178377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8233450247762166742284677 1543771921455406264178377)
            ·
              refine ⟨1157828941091554698133783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543771921455406264178377 1157828941091554698133783)
              ·
                refine ⟨1736743411637332047200675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157828941091554698133783 1736743411637332047200675)
                ·
                  refine ⟨2605115117455998070801013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736743411637332047200675 2605115117455998070801013)
                  ·
                    refine ⟨244229542261499819137595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2605115117455998070801013 244229542261499819137595)
                    ·
                      rfl

theorem cell23_1426906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_1426906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426906 prefixEnd_1426906 := by exact prefixLift 1426906
  have htrace : WordTrace (prefixWord ++ tailWord_1426906) baseStart_1426906 baseEnd_1426906 := by
    simpa [prefixWord, tailWord_1426906, baseEnd_1426906] using wordTrace_append hprefix tailTrace_1426906
  have hstable : (prefixWord ++ tailWord_1426906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426906).length < 2 ^ (prefixWord ++ tailWord_1426906).sum := by decide
  have hdescent : baseEnd_1426906 < baseStart_1426906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426912 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 3]
def baseStart_1426912 : Nat := 118140960795 + 1426912 * 2 ^ 59
def prefixEnd_1426912 : Nat := 4983230072969 + 3 ^ 40 * 1426912 * 2
def baseEnd_1426912 : Nat := 732691707668426433937757

theorem tailTrace_1426912 : CollatzResearch.WordTrace tailWord_1426912 prefixEnd_1426912 732691707668426433937757 := by
  unfold tailWord_1426912
  simp only [CollatzResearch.WordTrace]
  refine ⟨26021878103274498006493495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34695837471032664008657993 26021878103274498006493495)
  ·
    refine ⟨39032817154911747009740243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26021878103274498006493495 39032817154911747009740243)
    ·
      refine ⟨58549225732367620514610365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39032817154911747009740243 58549225732367620514610365)
      ·
        refine ⟨21955959649637857692978887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58549225732367620514610365 21955959649637857692978887)
        ·
          refine ⟨32933939474456786539468331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21955959649637857692978887 32933939474456786539468331)
          ·
            refine ⟨49400909211685179809202497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32933939474456786539468331 49400909211685179809202497)
            ·
              refine ⟨37050681908763884856901873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49400909211685179809202497 37050681908763884856901873)
              ·
                refine ⟨27788011431572913642676405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37050681908763884856901873 27788011431572913642676405)
                ·
                  refine ⟨2605126071709960654000913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27788011431572913642676405 2605126071709960654000913)
                  ·
                    refine ⟨1953844553782470490500685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2605126071709960654000913 1953844553782470490500685)
                    ·
                      refine ⟨732691707668426433937757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1953844553782470490500685 732691707668426433937757)
                      ·
                        rfl

theorem cell23_1426912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_1426912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426912 prefixEnd_1426912 := by exact prefixLift 1426912
  have htrace : WordTrace (prefixWord ++ tailWord_1426912) baseStart_1426912 baseEnd_1426912 := by
    simpa [prefixWord, tailWord_1426912, baseEnd_1426912] using wordTrace_append hprefix tailTrace_1426912
  have hstable : (prefixWord ++ tailWord_1426912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426912).length < 2 ^ (prefixWord ++ tailWord_1426912).sum := by decide
  have hdescent : baseEnd_1426912 < baseStart_1426912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426919 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 4, 4]
def baseStart_1426919 : Nat := 118140960795 + 1426919 * 2 ^ 59
def prefixEnd_1426919 : Nat := 4983230072969 + 3 ^ 40 * 1426919 * 2
def baseEnd_1426919 : Nat := 244231767344335968850075

theorem tailTrace_1426919 : CollatzResearch.WordTrace tailWord_1426919 prefixEnd_1426919 244231767344335968850075 := by
  unfold tailWord_1426919
  simp only [CollatzResearch.WordTrace]
  refine ⟨52044011517523636208491811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34696007678349090805661207 52044011517523636208491811)
  ·
    refine ⟨78066017276285454312737717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52044011517523636208491811 78066017276285454312737717)
    ·
      refine ⟨7318689119651761341819161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78066017276285454312737717 7318689119651761341819161)
      ·
        refine ⟨5489016839738821006364371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7318689119651761341819161 5489016839738821006364371)
        ·
          refine ⟨8233525259608231509546557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5489016839738821006364371 8233525259608231509546557)
          ·
            refine ⟨3087571972353086816079959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8233525259608231509546557 3087571972353086816079959)
            ·
              refine ⟨4631357958529630224119939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3087571972353086816079959 4631357958529630224119939)
              ·
                refine ⟨6947036937794445336179909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631357958529630224119939 6947036937794445336179909)
                ·
                  refine ⟨1302569425836458500533733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6947036937794445336179909 1302569425836458500533733)
                  ·
                    refine ⟨244231767344335968850075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1302569425836458500533733 244231767344335968850075)
                    ·
                      rfl

theorem cell23_1426919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_1426919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426919 prefixEnd_1426919 := by exact prefixLift 1426919
  have htrace : WordTrace (prefixWord ++ tailWord_1426919) baseStart_1426919 baseEnd_1426919 := by
    simpa [prefixWord, tailWord_1426919, baseEnd_1426919] using wordTrace_append hprefix tailTrace_1426919
  have hstable : (prefixWord ++ tailWord_1426919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426919).length < 2 ^ (prefixWord ++ tailWord_1426919).sum := by decide
  have hdescent : baseEnd_1426919 < baseStart_1426919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426935 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_1426935 : Nat := 118140960795 + 1426935 * 2 ^ 59
def prefixEnd_1426935 : Nat := 4983230072969 + 3 ^ 40 * 1426935 * 2
def baseEnd_1426935 : Nat := 732703517723479843950151

theorem tailTrace_1426935 : CollatzResearch.WordTrace tailWord_1426935 prefixEnd_1426935 732703517723479843950151 := by
  unfold tailWord_1426935
  simp only [CollatzResearch.WordTrace]
  refine ⟨52044595085465670941074259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34696396723643780627382839 52044595085465670941074259)
  ·
    refine ⟨78066892628198506411611389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52044595085465670941074259 78066892628198506411611389)
    ·
      refine ⟨29275084735574439904354271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78066892628198506411611389 29275084735574439904354271)
      ·
        refine ⟨43912627103361659856531407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29275084735574439904354271 43912627103361659856531407)
        ·
          refine ⟨65868940655042489784797111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43912627103361659856531407 65868940655042489784797111)
          ·
            refine ⟨98803410982563734677195667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65868940655042489784797111 98803410982563734677195667)
            ·
              refine ⟨148205116473845602015793501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98803410982563734677195667 148205116473845602015793501)
              ·
                refine ⟨55576918677692100755922563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148205116473845602015793501 55576918677692100755922563)
                ·
                  refine ⟨83365378016538151133883845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55576918677692100755922563 83365378016538151133883845)
                  ·
                    refine ⟨15631008378100903337603221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83365378016538151133883845 15631008378100903337603221)
                    ·
                      refine ⟨732703517723479843950151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15631008378100903337603221 732703517723479843950151)
                      ·
                        rfl

theorem cell23_1426935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_1426935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426935 prefixEnd_1426935 := by exact prefixLift 1426935
  have htrace : WordTrace (prefixWord ++ tailWord_1426935) baseStart_1426935 baseEnd_1426935 := by
    simpa [prefixWord, tailWord_1426935, baseEnd_1426935] using wordTrace_append hprefix tailTrace_1426935
  have hstable : (prefixWord ++ tailWord_1426935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426935).length < 2 ^ (prefixWord ++ tailWord_1426935).sum := by decide
  have hdescent : baseEnd_1426935 < baseStart_1426935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426936 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 2, 4]
def baseStart_1426936 : Nat := 118140960795 + 1426936 * 2 ^ 59
def prefixEnd_1426936 : Nat := 4983230072969 + 3 ^ 40 * 1426936 * 2
def baseEnd_1426936 : Nat := 244234677068044780012549

theorem tailTrace_1426936 : CollatzResearch.WordTrace tailWord_1426936 prefixEnd_1426936 244234677068044780012549 := by
  unfold tailWord_1426936
  simp only [CollatzResearch.WordTrace]
  refine ⟨26022315779231024055930331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34696421038974698741240441 26022315779231024055930331)
  ·
    refine ⟨39033473668846536083895497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26022315779231024055930331 39033473668846536083895497)
    ·
      refine ⟨29275105251634902062921623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39033473668846536083895497 29275105251634902062921623)
      ·
        refine ⟨43912657877452353094382435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29275105251634902062921623 43912657877452353094382435)
        ·
          refine ⟨65868986816178529641573653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43912657877452353094382435 65868986816178529641573653)
          ·
            refine ⟨3087608757008368576948765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65868986816178529641573653 3087608757008368576948765)
            ·
              refine ⟨1157853283878138216355787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3087608757008368576948765 1157853283878138216355787)
              ·
                refine ⟨1736779925817207324533681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157853283878138216355787 1736779925817207324533681)
                ·
                  refine ⟨1302584944362905493400261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1736779925817207324533681 1302584944362905493400261)
                  ·
                    refine ⟨244234677068044780012549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1302584944362905493400261 244234677068044780012549)
                    ·
                      rfl

theorem cell23_1426936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_1426936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426936 prefixEnd_1426936 := by exact prefixLift 1426936
  have htrace : WordTrace (prefixWord ++ tailWord_1426936) baseStart_1426936 baseEnd_1426936 := by
    simpa [prefixWord, tailWord_1426936, baseEnd_1426936] using wordTrace_append hprefix tailTrace_1426936
  have hstable : (prefixWord ++ tailWord_1426936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426936).length < 2 ^ (prefixWord ++ tailWord_1426936).sum := by decide
  have hdescent : baseEnd_1426936 < baseStart_1426936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426972 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1426972 : Nat := 118140960795 + 1426972 * 2 ^ 59
def prefixEnd_1426972 : Nat := 4983230072969 + 3 ^ 40 * 1426972 * 2
def baseEnd_1426972 : Nat := 732722516507696199187481

theorem tailTrace_1426972 : CollatzResearch.WordTrace tailWord_1426972 prefixEnd_1426972 732722516507696199187481 := by
  unfold tailWord_1426972
  simp only [CollatzResearch.WordTrace]
  refine ⟨26022972293165813130085585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34697296390887750840114113 26022972293165813130085585)
  ·
    refine ⟨19517229219874359847564189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26022972293165813130085585 19517229219874359847564189)
    ·
      refine ⟨7318960957452884942836571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19517229219874359847564189 7318960957452884942836571)
      ·
        refine ⟨10978441436179327414254857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7318960957452884942836571 10978441436179327414254857)
        ·
          refine ⟨8233831077134495560691143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10978441436179327414254857 8233831077134495560691143)
          ·
            refine ⟨12350746615701743341036715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233831077134495560691143 12350746615701743341036715)
            ·
              refine ⟨18526119923552615011555073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12350746615701743341036715 18526119923552615011555073)
              ·
                refine ⟨13894589942664461258666305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18526119923552615011555073 13894589942664461258666305)
                ·
                  refine ⟨10420942456998345943999729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13894589942664461258666305 10420942456998345943999729)
                  ·
                    refine ⟨7815706842748759457999797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10420942456998345943999729 7815706842748759457999797)
                    ·
                      refine ⟨732722516507696199187481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7815706842748759457999797 732722516507696199187481)
                      ·
                        rfl

theorem cell23_1426972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1426972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426972 prefixEnd_1426972 := by exact prefixLift 1426972
  have htrace : WordTrace (prefixWord ++ tailWord_1426972) baseStart_1426972 baseEnd_1426972 := by
    simpa [prefixWord, tailWord_1426972, baseEnd_1426972] using wordTrace_append hprefix tailTrace_1426972
  have hstable : (prefixWord ++ tailWord_1426972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426972).length < 2 ^ (prefixWord ++ tailWord_1426972).sum := by decide
  have hdescent : baseEnd_1426972 < baseStart_1426972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426976 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1426976 : Nat := 118140960795 + 1426976 * 2 ^ 59
def prefixEnd_1426976 : Nat := 4983230072969 + 3 ^ 40 * 1426976 * 2
def baseEnd_1426976 : Nat := 732724570430314183537463

theorem tailTrace_1426976 : CollatzResearch.WordTrace tailWord_1426976 prefixEnd_1426976 732724570430314183537463 := by
  unfold tailWord_1426976
  simp only [CollatzResearch.WordTrace]
  refine ⟨26023045239158567471658391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34697393652211423295544521 26023045239158567471658391)
  ·
    refine ⟨39034567858737851207487587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26023045239158567471658391 39034567858737851207487587)
    ·
      refine ⟨58551851788106776811231381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39034567858737851207487587 58551851788106776811231381)
      ·
        refine ⟨2744618052567505163026471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58551851788106776811231381 2744618052567505163026471)
        ·
          refine ⟨4116927078851257744539707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2744618052567505163026471 4116927078851257744539707)
          ·
            refine ⟨6175390618276886616809561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4116927078851257744539707 6175390618276886616809561)
            ·
              refine ⟨4631542963707664962607171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6175390618276886616809561 4631542963707664962607171)
              ·
                refine ⟨6947314445561497443910757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631542963707664962607171 6947314445561497443910757)
                ·
                  refine ⟨1302621458542780770733267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6947314445561497443910757 1302621458542780770733267)
                  ·
                    refine ⟨1953932187814171156099901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1302621458542780770733267 1953932187814171156099901)
                    ·
                      refine ⟨732724570430314183537463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1953932187814171156099901 732724570430314183537463)
                      ·
                        rfl

theorem cell23_1426976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1426976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426976 prefixEnd_1426976 := by exact prefixLift 1426976
  have htrace : WordTrace (prefixWord ++ tailWord_1426976) baseStart_1426976 baseEnd_1426976 := by
    simpa [prefixWord, tailWord_1426976, baseEnd_1426976] using wordTrace_append hprefix tailTrace_1426976
  have hstable : (prefixWord ++ tailWord_1426976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426976).length < 2 ^ (prefixWord ++ tailWord_1426976).sum := by decide
  have hdescent : baseEnd_1426976 < baseStart_1426976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426986 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_1426986 : Nat := 118140960795 + 1426986 * 2 ^ 59
def prefixEnd_1426986 : Nat := 4983230072969 + 3 ^ 40 * 1426986 * 2
def baseEnd_1426986 : Nat := 732729705236859144412417

theorem tailTrace_1426986 : CollatzResearch.WordTrace tailWord_1426986 prefixEnd_1426986 732729705236859144412417 := by
  unfold tailWord_1426986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011613802070226662795203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34697636805520604434120541 13011613802070226662795203)
  ·
    refine ⟨19517420703105339994192805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13011613802070226662795203 19517420703105339994192805)
    ·
      refine ⟨3659516381832251248911151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19517420703105339994192805 3659516381832251248911151)
      ·
        refine ⟨5489274572748376873366727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659516381832251248911151 5489274572748376873366727)
        ·
          refine ⟨8233911859122565310050091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5489274572748376873366727 8233911859122565310050091)
          ·
            refine ⟨12350867788683847965075137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233911859122565310050091 12350867788683847965075137)
            ·
              refine ⟨9263150841512885973806353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12350867788683847965075137 9263150841512885973806353)
              ·
                refine ⟨6947363131134664480354765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9263150841512885973806353 6947363131134664480354765)
                ·
                  refine ⟨2605261174175499180133037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6947363131134664480354765 2605261174175499180133037)
                  ·
                    refine ⟨976972940315812192549889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2605261174175499180133037 976972940315812192549889)
                    ·
                      refine ⟨732729705236859144412417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 976972940315812192549889 732729705236859144412417)
                      ·
                        rfl

theorem cell23_1426986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_1426986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1426986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1426986 prefixEnd_1426986 := by exact prefixLift 1426986
  have htrace : WordTrace (prefixWord ++ tailWord_1426986) baseStart_1426986 baseEnd_1426986 := by
    simpa [prefixWord, tailWord_1426986, baseEnd_1426986] using wordTrace_append hprefix tailTrace_1426986
  have hstable : (prefixWord ++ tailWord_1426986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426986).length < 2 ^ (prefixWord ++ tailWord_1426986).sum := by decide
  have hdescent : baseEnd_1426986 < baseStart_1426986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427002 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_1427002 : Nat := 118140960795 + 1427002 * 2 ^ 59
def prefixEnd_1427002 : Nat := 4983230072969 + 3 ^ 40 * 1427002 * 2
def baseEnd_1427002 : Nat := 732737920927331081812343

theorem tailTrace_1427002 : CollatzResearch.WordTrace tailWord_1427002 prefixEnd_1427002 732737920927331081812343 := by
  unfold tailWord_1427002
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011759694055735345940815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34698025850815294255842173 13011759694055735345940815)
  ·
    refine ⟨19517639541083603018911223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13011759694055735345940815 19517639541083603018911223)
    ·
      refine ⟨29276459311625404528366835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19517639541083603018911223 29276459311625404528366835)
      ·
        refine ⟨43914688967438106792550253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29276459311625404528366835 43914688967438106792550253)
        ·
          refine ⟨16468008362789290047206345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43914688967438106792550253 16468008362789290047206345)
          ·
            refine ⟨12351006272091967535404759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16468008362789290047206345 12351006272091967535404759)
            ·
              refine ⟨18526509408137951303107139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12351006272091967535404759 18526509408137951303107139)
              ·
                refine ⟨27789764112206926954660709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18526509408137951303107139 27789764112206926954660709)
                ·
                  refine ⟨5210580771038798803998883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27789764112206926954660709 5210580771038798803998883)
                  ·
                    refine ⟨7815871156558198205998325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5210580771038798803998883 7815871156558198205998325)
                    ·
                      refine ⟨732737920927331081812343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7815871156558198205998325 732737920927331081812343)
                      ·
                        rfl

theorem cell23_1427002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_1427002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427002 prefixEnd_1427002 := by exact prefixLift 1427002
  have htrace : WordTrace (prefixWord ++ tailWord_1427002) baseStart_1427002 baseEnd_1427002 := by
    simpa [prefixWord, tailWord_1427002, baseEnd_1427002] using wordTrace_append hprefix tailTrace_1427002
  have hstable : (prefixWord ++ tailWord_1427002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427002).length < 2 ^ (prefixWord ++ tailWord_1427002).sum := by decide
  have hdescent : baseEnd_1427002 < baseStart_1427002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427052 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_1427052 : Nat := 118140960795 + 1427052 * 2 ^ 59
def prefixEnd_1427052 : Nat := 4983230072969 + 3 ^ 40 * 1427052 * 2
def baseEnd_1427052 : Nat := 244254531653351962062371

theorem tailTrace_1427052 : CollatzResearch.WordTrace tailWord_1427052 prefixEnd_1427052 244254531653351962062371 := by
  unfold tailWord_1427052
  simp only [CollatzResearch.WordTrace]
  refine ⟨26024431213020899961541705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34699241617361199948722273 26024431213020899961541705)
  ·
    refine ⟨19518323409765674971156279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26024431213020899961541705 19518323409765674971156279)
    ·
      refine ⟨29277485114648512456734419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19518323409765674971156279 29277485114648512456734419)
      ·
        refine ⟨43916227671972768685101629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29277485114648512456734419 43916227671972768685101629)
        ·
          refine ⟨16468585376989788256913111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43916227671972768685101629 16468585376989788256913111)
          ·
            refine ⟨24702878065484682385369667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16468585376989788256913111 24702878065484682385369667)
            ·
              refine ⟨37054317098227023578054501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24702878065484682385369667 37054317098227023578054501)
              ·
                refine ⟨6947684455917566920885219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37054317098227023578054501 6947684455917566920885219)
                ·
                  refine ⟨10421526683876350381327829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947684455917566920885219 10421526683876350381327829)
                  ·
                    refine ⟨244254531653351962062371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10421526683876350381327829 244254531653351962062371)
                    ·
                      rfl

theorem cell23_1427052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_1427052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427052 prefixEnd_1427052 := by exact prefixLift 1427052
  have htrace : WordTrace (prefixWord ++ tailWord_1427052) baseStart_1427052 baseEnd_1427052 := by
    simpa [prefixWord, tailWord_1427052, baseEnd_1427052] using wordTrace_append hprefix tailTrace_1427052
  have hstable : (prefixWord ++ tailWord_1427052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427052).length < 2 ^ (prefixWord ++ tailWord_1427052).sum := by decide
  have hdescent : baseEnd_1427052 < baseStart_1427052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427069 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_1427069 : Nat := 118140960795 + 1427069 * 2 ^ 59
def prefixEnd_1427069 : Nat := 4983230072969 + 3 ^ 40 * 1427069 * 2
def baseEnd_1427069 : Nat := 244257441377060773224845

theorem tailTrace_1427069 : CollatzResearch.WordTrace tailWord_1427069 prefixEnd_1427069 244257441377060773224845 := by
  unfold tailWord_1427069
  simp only [CollatzResearch.WordTrace]
  refine ⟨52049482466980211826452261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34699654977986807884301507 52049482466980211826452261)
  ·
    refine ⟨9759277962558789717459799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52049482466980211826452261 9759277962558789717459799)
    ·
      refine ⟨14638916943838184576189699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9759277962558789717459799 14638916943838184576189699)
      ·
        refine ⟨21958375415757276864284549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14638916943838184576189699 21958375415757276864284549)
        ·
          refine ⟨4117195390454489412053353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21958375415757276864284549 4117195390454489412053353)
          ·
            refine ⟨3087896542840867059040015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4117195390454489412053353 3087896542840867059040015)
            ·
              refine ⟨4631844814261300588560023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3087896542840867059040015 4631844814261300588560023)
              ·
                refine ⟨6947767221391950882840035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631844814261300588560023 6947767221391950882840035)
                ·
                  refine ⟨10421650832087926324260053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947767221391950882840035 10421650832087926324260053)
                  ·
                    refine ⟨244257441377060773224845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10421650832087926324260053 244257441377060773224845)
                    ·
                      rfl

theorem cell23_1427069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_1427069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427069 prefixEnd_1427069 := by exact prefixLift 1427069
  have htrace : WordTrace (prefixWord ++ tailWord_1427069) baseStart_1427069 baseEnd_1427069 := by
    simpa [prefixWord, tailWord_1427069, baseEnd_1427069] using wordTrace_append hprefix tailTrace_1427069
  have hstable : (prefixWord ++ tailWord_1427069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427069).length < 2 ^ (prefixWord ++ tailWord_1427069).sum := by decide
  have hdescent : baseEnd_1427069 < baseStart_1427069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427109 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 1, 4, 3]
def baseStart_1427109 : Nat := 118140960795 + 1427109 * 2 ^ 59
def prefixEnd_1427109 : Nat := 4983230072969 + 3 ^ 40 * 1427109 * 2
def baseEnd_1427109 : Nat := 732792863357362163174351

theorem tailTrace_1427109 : CollatzResearch.WordTrace tailWord_1427109 prefixEnd_1427109 732792863357362163174351 := by
  unfold tailWord_1427109
  simp only [CollatzResearch.WordTrace]
  refine ⟨52050941386835298657908381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34700627591223532438605587 52050941386835298657908381)
  ·
    refine ⟨19519103020063236996715643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52050941386835298657908381 19519103020063236996715643)
    ·
      refine ⟨29278654530094855495073465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19519103020063236996715643 29278654530094855495073465)
      ·
        refine ⟨21958990897571141621305099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29278654530094855495073465 21958990897571141621305099)
        ·
          refine ⟨32938486346356712431957649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21958990897571141621305099 32938486346356712431957649)
          ·
            refine ⟨24703864759767534323968237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32938486346356712431957649 24703864759767534323968237)
            ·
              refine ⟨9263949284912825371488089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24703864759767534323968237 9263949284912825371488089)
              ·
                refine ⟨6947961963684619028616067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9263949284912825371488089 6947961963684619028616067)
                ·
                  refine ⟨10421942945526928542924101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947961963684619028616067 10421942945526928542924101)
                  ·
                    refine ⟨1954114302286299101798269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10421942945526928542924101 1954114302286299101798269)
                    ·
                      refine ⟨732792863357362163174351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1954114302286299101798269 732792863357362163174351)
                      ·
                        rfl

theorem cell23_1427109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_1427109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427109 prefixEnd_1427109 := by exact prefixLift 1427109
  have htrace : WordTrace (prefixWord ++ tailWord_1427109) baseStart_1427109 baseEnd_1427109 := by
    simpa [prefixWord, tailWord_1427109, baseEnd_1427109] using wordTrace_append hprefix tailTrace_1427109
  have hstable : (prefixWord ++ tailWord_1427109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427109).length < 2 ^ (prefixWord ++ tailWord_1427109).sum := by decide
  have hdescent : baseEnd_1427109 < baseStart_1427109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427150 : List Nat := [4, 1, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_1427150 : Nat := 118140960795 + 1427150 * 2 ^ 59
def prefixEnd_1427150 : Nat := 4983230072969 + 3 ^ 40 * 1427150 * 2
def baseEnd_1427150 : Nat := 244271305354732167587221

theorem tailTrace_1427150 : CollatzResearch.WordTrace tailWord_1427150 prefixEnd_1427150 244271305354732167587221 := by
  unfold tailWord_1427150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6506554597460845332518863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34701624519791175106767269 6506554597460845332518863)
  ·
    refine ⟨9759831896191267998778295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6506554597460845332518863 9759831896191267998778295)
    ·
      refine ⟨14639747844286901998167443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9759831896191267998778295 14639747844286901998167443)
      ·
        refine ⟨21959621766430352997251165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14639747844286901998167443 21959621766430352997251165)
        ·
          refine ⟨8234858162411382373969187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21959621766430352997251165 8234858162411382373969187)
          ·
            refine ⟨12352287243617073560953781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8234858162411382373969187 12352287243617073560953781)
            ·
              refine ⟨1158026929089100646339417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12352287243617073560953781 1158026929089100646339417)
              ·
                refine ⟨868520196816825484754563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1158026929089100646339417 868520196816825484754563)
                ·
                  refine ⟨1302780295225238227131845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868520196816825484754563 1302780295225238227131845)
                  ·
                    refine ⟨244271305354732167587221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1302780295225238227131845 244271305354732167587221)
                    ·
                      rfl

theorem cell23_1427150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_1427150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427150 prefixEnd_1427150 := by exact prefixLift 1427150
  have htrace : WordTrace (prefixWord ++ tailWord_1427150) baseStart_1427150 baseEnd_1427150 := by
    simpa [prefixWord, tailWord_1427150, baseEnd_1427150] using wordTrace_append hprefix tailTrace_1427150
  have hstable : (prefixWord ++ tailWord_1427150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427150).length < 2 ^ (prefixWord ++ tailWord_1427150).sum := by decide
  have hdescent : baseEnd_1427150 < baseStart_1427150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427159 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 3, 5]
def baseStart_1427159 : Nat := 118140960795 + 1427159 * 2 ^ 59
def prefixEnd_1427159 : Nat := 4983230072969 + 3 ^ 40 * 1427159 * 2
def baseEnd_1427159 : Nat := 244272845796695655849707

theorem tailTrace_1427159 : CollatzResearch.WordTrace tailWord_1427159 prefixEnd_1427159 244272845796695655849707 := by
  unfold tailWord_1427159
  simp only [CollatzResearch.WordTrace]
  refine ⟨52052765036654157197228531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34701843357769438131485687 52052765036654157197228531)
  ·
    refine ⟨78079147554981235795842797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52052765036654157197228531 78079147554981235795842797)
    ·
      refine ⟨29279680333117963423441049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78079147554981235795842797 29279680333117963423441049)
      ·
        refine ⟨21959760249838472567580787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29279680333117963423441049 21959760249838472567580787)
        ·
          refine ⟨32939640374757708851371181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21959760249838472567580787 32939640374757708851371181)
          ·
            refine ⟨12352365140534140819264193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32939640374757708851371181 12352365140534140819264193)
            ·
              refine ⟨9264273855400605614448145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12352365140534140819264193 9264273855400605614448145)
              ·
                refine ⟨6948205391550454210836109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9264273855400605614448145 6948205391550454210836109)
                ·
                  refine ⟨2605577021831420329063541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6948205391550454210836109 2605577021831420329063541)
                  ·
                    refine ⟨244272845796695655849707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2605577021831420329063541 244272845796695655849707)
                    ·
                      rfl

theorem cell23_1427159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_1427159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427159 prefixEnd_1427159 := by exact prefixLift 1427159
  have htrace : WordTrace (prefixWord ++ tailWord_1427159) baseStart_1427159 baseEnd_1427159 := by
    simpa [prefixWord, tailWord_1427159, baseEnd_1427159] using wordTrace_append hprefix tailTrace_1427159
  have hstable : (prefixWord ++ tailWord_1427159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427159).length < 2 ^ (prefixWord ++ tailWord_1427159).sum := by decide
  have hdescent : baseEnd_1427159 < baseStart_1427159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427176 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1427176 : Nat := 118140960795 + 1427176 * 2 ^ 59
def prefixEnd_1427176 : Nat := 4983230072969 + 3 ^ 40 * 1427176 * 2
def baseEnd_1427176 : Nat := 244275755520404467012181

theorem tailTrace_1427176 : CollatzResearch.WordTrace tailWord_1427176 prefixEnd_1427176 244275755520404467012181 := by
  unfold tailWord_1427176
  simp only [CollatzResearch.WordTrace]
  refine ⟨26026692538796284550298691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34702256718395046067064921 26026692538796284550298691)
  ·
    refine ⟨39040038808194426825448037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26026692538796284550298691 39040038808194426825448037)
    ·
      refine ⟨7320007276536455029771507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39040038808194426825448037 7320007276536455029771507)
      ·
        refine ⟨10980010914804682544657261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7320007276536455029771507 10980010914804682544657261)
        ·
          refine ⟨4117504093051755954246473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10980010914804682544657261 4117504093051755954246473)
          ·
            refine ⟨3088128069788816965684855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4117504093051755954246473 3088128069788816965684855)
            ·
              refine ⟨4632192104683225448527283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088128069788816965684855 4632192104683225448527283)
              ·
                refine ⟨6948288157024838172790925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632192104683225448527283 6948288157024838172790925)
                ·
                  refine ⟨2605608058884314314796597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6948288157024838172790925 2605608058884314314796597)
                  ·
                    refine ⟨244275755520404467012181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2605608058884314314796597 244275755520404467012181)
                    ·
                      rfl

theorem cell23_1427176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1427176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427176 prefixEnd_1427176 := by exact prefixLift 1427176
  have htrace : WordTrace (prefixWord ++ tailWord_1427176) baseStart_1427176 baseEnd_1427176 := by
    simpa [prefixWord, tailWord_1427176, baseEnd_1427176] using wordTrace_append hprefix tailTrace_1427176
  have hstable : (prefixWord ++ tailWord_1427176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427176).length < 2 ^ (prefixWord ++ tailWord_1427176).sum := by decide
  have hdescent : baseEnd_1427176 < baseStart_1427176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427183 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 2, 3, 2]
def baseStart_1427183 : Nat := 118140960795 + 1427183 * 2 ^ 59
def prefixEnd_1427183 : Nat := 4983230072969 + 3 ^ 40 * 1427183 * 2
def baseEnd_1427183 : Nat := 732830860925794873649011

theorem tailTrace_1427183 : CollatzResearch.WordTrace tailWord_1427183 prefixEnd_1427183 732830860925794873649011 := by
  unfold tailWord_1427183
  simp only [CollatzResearch.WordTrace]
  refine ⟨52053640388567209296102203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34702426925711472864068135 52053640388567209296102203)
  ·
    refine ⟨78080460582850813944153305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52053640388567209296102203 78080460582850813944153305)
    ·
      refine ⟨58560345437138110458114979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78080460582850813944153305 58560345437138110458114979)
      ·
        refine ⟨87840518155707165687172469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58560345437138110458114979 87840518155707165687172469)
        ·
          refine ⟨8235048577097546783172419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87840518155707165687172469 8235048577097546783172419)
          ·
            refine ⟨12352572865646320174758629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8235048577097546783172419 12352572865646320174758629)
            ·
              refine ⟨2316107412308685032767243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12352572865646320174758629 2316107412308685032767243)
              ·
                refine ⟨3474161118463027549150865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316107412308685032767243 3474161118463027549150865)
                ·
                  refine ⟨2605620838847270661863149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3474161118463027549150865 2605620838847270661863149)
                  ·
                    refine ⟨977107814567726498198681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2605620838847270661863149 977107814567726498198681)
                    ·
                      refine ⟨732830860925794873649011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977107814567726498198681 732830860925794873649011)
                      ·
                        rfl

theorem cell23_1427183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 3, 2].length) (baseStart_1427183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427183 prefixEnd_1427183 := by exact prefixLift 1427183
  have htrace : WordTrace (prefixWord ++ tailWord_1427183) baseStart_1427183 baseEnd_1427183 := by
    simpa [prefixWord, tailWord_1427183, baseEnd_1427183] using wordTrace_append hprefix tailTrace_1427183
  have hstable : (prefixWord ++ tailWord_1427183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427183).length < 2 ^ (prefixWord ++ tailWord_1427183).sum := by decide
  have hdescent : baseEnd_1427183 < baseStart_1427183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427207 : List Nat := [1, 1, 4, 4, 2, 1, 1, 4, 1, 1, 3]
def baseStart_1427207 : Nat := 118140960795 + 1427207 * 2 ^ 59
def prefixEnd_1427207 : Nat := 4983230072969 + 3 ^ 40 * 1427207 * 2
def baseEnd_1427207 : Nat := 732843184461502779748901

theorem tailTrace_1427207 : CollatzResearch.WordTrace tailWord_1427207 prefixEnd_1427207 732843184461502779748901 := by
  unfold tailWord_1427207
  simp only [CollatzResearch.WordTrace]
  refine ⟨52054515740480261394975875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34703010493653507596650583 52054515740480261394975875)
  ·
    refine ⟨78081773610720392092463813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52054515740480261394975875 78081773610720392092463813)
    ·
      refine ⟨14640332552010073517336965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78081773610720392092463813 14640332552010073517336965)
      ·
        refine ⟨2745062353501888784500681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14640332552010073517336965 2745062353501888784500681)
        ·
          refine ⟨2058796765126416588375511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2745062353501888784500681 2058796765126416588375511)
          ·
            refine ⟨3088195147689624882563267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058796765126416588375511 3088195147689624882563267)
            ·
              refine ⟨4632292721534437323844901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088195147689624882563267 4632292721534437323844901)
              ·
                refine ⟨868554885287706998220919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4632292721534437323844901 868554885287706998220919)
                ·
                  refine ⟨1302832327931560497331379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868554885287706998220919 1302832327931560497331379)
                  ·
                    refine ⟨1954248491897340745997069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1302832327931560497331379 1954248491897340745997069)
                    ·
                      refine ⟨732843184461502779748901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1954248491897340745997069 732843184461502779748901)
                      ·
                        rfl

theorem cell23_1427207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_1427207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427207 prefixEnd_1427207 := by exact prefixLift 1427207
  have htrace : WordTrace (prefixWord ++ tailWord_1427207) baseStart_1427207 baseEnd_1427207 := by
    simpa [prefixWord, tailWord_1427207, baseEnd_1427207] using wordTrace_append hprefix tailTrace_1427207
  have hstable : (prefixWord ++ tailWord_1427207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427207).length < 2 ^ (prefixWord ++ tailWord_1427207).sum := by decide
  have hdescent : baseEnd_1427207 < baseStart_1427207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427209 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_1427209 : Nat := 118140960795 + 1427209 * 2 ^ 59
def prefixEnd_1427209 : Nat := 4983230072969 + 3 ^ 40 * 1427209 * 2
def baseEnd_1427209 : Nat := 732844211422811771923891

theorem tailTrace_1427209 : CollatzResearch.WordTrace tailWord_1427209 prefixEnd_1427209 732844211422811771923891 := by
  unfold tailWord_1427209
  simp only [CollatzResearch.WordTrace]
  refine ⟨52054588686473015736548681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34703059124315343824365787 52054588686473015736548681)
  ·
    refine ⟨39040941514854761802411511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52054588686473015736548681 39040941514854761802411511)
    ·
      refine ⟨58561412272282142703617267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39040941514854761802411511 58561412272282142703617267)
      ·
        refine ⟨87842118408423214055425901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58561412272282142703617267 87842118408423214055425901)
        ·
          refine ⟨32940794403158705270784713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87842118408423214055425901 32940794403158705270784713)
          ·
            refine ⟨24705595802369028953088535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32940794403158705270784713 24705595802369028953088535)
            ·
              refine ⟨37058393703553543429632803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24705595802369028953088535 37058393703553543429632803)
              ·
                refine ⟨55587590555330315144449205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37058393703553543429632803 55587590555330315144449205)
                ·
                  refine ⟨5211336614562217044792113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55587590555330315144449205 5211336614562217044792113)
                  ·
                    refine ⟨3908502460921662783594085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5211336614562217044792113 3908502460921662783594085)
                    ·
                      refine ⟨732844211422811771923891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3908502460921662783594085 732844211422811771923891)
                      ·
                        rfl

theorem cell23_1427209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_1427209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427209 prefixEnd_1427209 := by exact prefixLift 1427209
  have htrace : WordTrace (prefixWord ++ tailWord_1427209) baseStart_1427209 baseEnd_1427209 := by
    simpa [prefixWord, tailWord_1427209, baseEnd_1427209] using wordTrace_append hprefix tailTrace_1427209
  have hstable : (prefixWord ++ tailWord_1427209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427209).length < 2 ^ (prefixWord ++ tailWord_1427209).sum := by decide
  have hdescent : baseEnd_1427209 < baseStart_1427209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427223 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 2, 4]
def baseStart_1427223 : Nat := 118140960795 + 1427223 * 2 ^ 59
def prefixEnd_1427223 : Nat := 4983230072969 + 3 ^ 40 * 1427223 * 2
def baseEnd_1427223 : Nat := 244283800050658239049609

theorem tailTrace_1427223 : CollatzResearch.WordTrace tailWord_1427223 prefixEnd_1427223 244283800050658239049609 := by
  unfold tailWord_1427223
  simp only [CollatzResearch.WordTrace]
  refine ⟨52055099308422296127558323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34703399538948197418372215 52055099308422296127558323)
  ·
    refine ⟨78082648962633444191337485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52055099308422296127558323 78082648962633444191337485)
    ·
      refine ⟨29280993360987541571751557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78082648962633444191337485 29280993360987541571751557)
      ·
        refine ⟨5490186255185164044703417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29280993360987541571751557 5490186255185164044703417)
        ·
          refine ⟨4117639691388873033527563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5490186255185164044703417 4117639691388873033527563)
          ·
            refine ⟨6176459537083309550291345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117639691388873033527563 6176459537083309550291345)
            ·
              refine ⟨4632344652812482162718509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6176459537083309550291345 4632344652812482162718509)
              ·
                refine ⟨1737129244804680811019441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4632344652812482162718509 1737129244804680811019441)
                ·
                  refine ⟨1302846933603510608264581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1737129244804680811019441 1302846933603510608264581)
                  ·
                    refine ⟨244283800050658239049609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1302846933603510608264581 244283800050658239049609)
                    ·
                      rfl

theorem cell23_1427223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_1427223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427223 prefixEnd_1427223 := by exact prefixLift 1427223
  have htrace : WordTrace (prefixWord ++ tailWord_1427223) baseStart_1427223 baseEnd_1427223 := by
    simpa [prefixWord, tailWord_1427223, baseEnd_1427223] using wordTrace_append hprefix tailTrace_1427223
  have hstable : (prefixWord ++ tailWord_1427223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427223).length < 2 ^ (prefixWord ++ tailWord_1427223).sum := by decide
  have hdescent : baseEnd_1427223 < baseStart_1427223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427226 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_1427226 : Nat := 118140960795 + 1427226 * 2 ^ 59
def prefixEnd_1427226 : Nat := 4983230072969 + 3 ^ 40 * 1427226 * 2
def baseEnd_1427226 : Nat := 732852940593938205411313

theorem tailTrace_1427226 : CollatzResearch.WordTrace tailWord_1427226 prefixEnd_1427226 732852940593938205411313 := by
  unfold tailWord_1427226
  simp only [CollatzResearch.WordTrace]
  refine ⟨13013802181852856909979383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34703472484940951759945021 13013802181852856909979383)
  ·
    refine ⟨19520703272779285364969075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13013802181852856909979383 19520703272779285364969075)
    ·
      refine ⟨29281054909168928047453613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19520703272779285364969075 29281054909168928047453613)
      ·
        refine ⟨10980395590938348017795105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29281054909168928047453613 10980395590938348017795105)
        ·
          refine ⟨8235296693203761013346329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10980395590938348017795105 8235296693203761013346329)
          ·
            refine ⟨6176472519902820760009747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8235296693203761013346329 6176472519902820760009747)
            ·
              refine ⟨9264708779854231140014621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176472519902820760009747 9264708779854231140014621)
              ·
                refine ⟨3474265792445336677505483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9264708779854231140014621 3474265792445336677505483)
                ·
                  refine ⟨5211398688668005016258225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474265792445336677505483 5211398688668005016258225)
                  ·
                    refine ⟨3908549016501003762193669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5211398688668005016258225 3908549016501003762193669)
                    ·
                      refine ⟨732852940593938205411313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3908549016501003762193669 732852940593938205411313)
                      ·
                        rfl

theorem cell23_1427226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_1427226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427226 prefixEnd_1427226 := by exact prefixLift 1427226
  have htrace : WordTrace (prefixWord ++ tailWord_1427226) baseStart_1427226 baseEnd_1427226 := by
    simpa [prefixWord, tailWord_1427226, baseEnd_1427226] using wordTrace_append hprefix tailTrace_1427226
  have hstable : (prefixWord ++ tailWord_1427226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427226).length < 2 ^ (prefixWord ++ tailWord_1427226).sum := by decide
  have hdescent : baseEnd_1427226 < baseStart_1427226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427250 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3]
def baseStart_1427250 : Nat := 118140960795 + 1427250 * 2 ^ 59
def prefixEnd_1427250 : Nat := 4983230072969 + 3 ^ 40 * 1427250 * 2
def baseEnd_1427250 : Nat := 732865264129646111511203

theorem tailTrace_1427250 : CollatzResearch.WordTrace tailWord_1427250 prefixEnd_1427250 732865264129646111511203 := by
  unfold tailWord_1427250
  simp only [CollatzResearch.WordTrace]
  refine ⟨13014021019831119934697801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34704056052882986492527469 13014021019831119934697801)
  ·
    refine ⟨9760515764873339951023351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13014021019831119934697801 9760515764873339951023351)
    ·
      refine ⟨14640773647310009926535027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9760515764873339951023351 14640773647310009926535027)
      ·
        refine ⟨21961160470965014889802541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14640773647310009926535027 21961160470965014889802541)
        ·
          refine ⟨8235435176611880583675953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21961160470965014889802541 8235435176611880583675953)
          ·
            refine ⟨6176576382458910437756965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8235435176611880583675953 6176576382458910437756965)
            ·
              refine ⟨1158108071711045707079431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6176576382458910437756965 1158108071711045707079431)
              ·
                refine ⟨1737162107566568560619147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158108071711045707079431 1737162107566568560619147)
                ·
                  refine ⟨2605743161349852840928721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737162107566568560619147 2605743161349852840928721)
                  ·
                    refine ⟨1954307371012389630696541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2605743161349852840928721 1954307371012389630696541)
                    ·
                      refine ⟨732865264129646111511203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1954307371012389630696541 732865264129646111511203)
                      ·
                        rfl

theorem cell23_1427250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_1427250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427250 prefixEnd_1427250 := by exact prefixLift 1427250
  have htrace : WordTrace (prefixWord ++ tailWord_1427250) baseStart_1427250 baseEnd_1427250 := by
    simpa [prefixWord, tailWord_1427250, baseEnd_1427250] using wordTrace_append hprefix tailTrace_1427250
  have hstable : (prefixWord ++ tailWord_1427250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427250).length < 2 ^ (prefixWord ++ tailWord_1427250).sum := by decide
  have hdescent : baseEnd_1427250 < baseStart_1427250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427257 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 2, 4]
def baseStart_1427257 : Nat := 118140960795 + 1427257 * 2 ^ 59
def prefixEnd_1427257 : Nat := 4983230072969 + 3 ^ 40 * 1427257 * 2
def baseEnd_1427257 : Nat := 244289619498075861374557

theorem tailTrace_1427257 : CollatzResearch.WordTrace tailWord_1427257 prefixEnd_1427257 244289619498075861374557 := by
  unfold tailWord_1427257
  simp only [CollatzResearch.WordTrace]
  refine ⟨52056339390299119934296025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34704226260199413289530683 52056339390299119934296025)
  ·
    refine ⟨39042254542724339950722019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52056339390299119934296025 39042254542724339950722019)
    ·
      refine ⟨58563381814086509926083029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39042254542724339950722019 58563381814086509926083029)
      ·
        refine ⟨1372579261267652576392571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 58563381814086509926083029 1372579261267652576392571)
        ·
          refine ⟨2058868891901478864588857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372579261267652576392571 2058868891901478864588857)
          ·
            refine ⟨1544151668926109148441643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2058868891901478864588857 1544151668926109148441643)
            ·
              refine ⟨2316227503389163722662465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544151668926109148441643 2316227503389163722662465)
              ·
                refine ⟨1737170627541872791996849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316227503389163722662465 1737170627541872791996849)
                ·
                  refine ⟨1302877970656404593997637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1737170627541872791996849 1302877970656404593997637)
                  ·
                    refine ⟨244289619498075861374557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1302877970656404593997637 244289619498075861374557)
                    ·
                      rfl

theorem cell23_1427257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 4].length) (baseStart_1427257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427257 prefixEnd_1427257 := by exact prefixLift 1427257
  have htrace : WordTrace (prefixWord ++ tailWord_1427257) baseStart_1427257 baseEnd_1427257 := by
    simpa [prefixWord, tailWord_1427257, baseEnd_1427257] using wordTrace_append hprefix tailTrace_1427257
  have hstable : (prefixWord ++ tailWord_1427257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427257).length < 2 ^ (prefixWord ++ tailWord_1427257).sum := by decide
  have hdescent : baseEnd_1427257 < baseStart_1427257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427290 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2]
def baseStart_1427290 : Nat := 118140960795 + 1427290 * 2 ^ 59
def prefixEnd_1427290 : Nat := 4983230072969 + 3 ^ 40 * 1427290 * 2
def baseEnd_1427290 : Nat := 732885803355825955011019

theorem tailTrace_1427290 : CollatzResearch.WordTrace tailWord_1427290 prefixEnd_1427290 732885803355825955011019 := by
  unfold tailWord_1427290
  simp only [CollatzResearch.WordTrace]
  refine ⟨13014385749794891642561831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34705028666119711046831549 13014385749794891642561831)
  ·
    refine ⟨19521578624692337463842747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13014385749794891642561831 19521578624692337463842747)
    ·
      refine ⟨29282367937038506195764121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19521578624692337463842747 29282367937038506195764121)
      ·
        refine ⟨21961775952778879646823091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29282367937038506195764121 21961775952778879646823091)
        ·
          refine ⟨32942663929168319470234637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21961775952778879646823091 32942663929168319470234637)
          ·
            refine ⟨12353498973438119801337989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32942663929168319470234637 12353498973438119801337989)
            ·
              refine ⟨2316281057519647462750873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12353498973438119801337989 2316281057519647462750873)
              ·
                refine ⟨1737210793139735597063155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316281057519647462750873 1737210793139735597063155)
                ·
                  refine ⟨2605816189709603395594733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737210793139735597063155 2605816189709603395594733)
                  ·
                    refine ⟨977181071141101273348025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2605816189709603395594733 977181071141101273348025)
                    ·
                      refine ⟨732885803355825955011019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977181071141101273348025 732885803355825955011019)
                      ·
                        rfl

theorem cell23_1427290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_1427290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427290 prefixEnd_1427290 := by exact prefixLift 1427290
  have htrace : WordTrace (prefixWord ++ tailWord_1427290) baseStart_1427290 baseEnd_1427290 := by
    simpa [prefixWord, tailWord_1427290, baseEnd_1427290] using wordTrace_append hprefix tailTrace_1427290
  have hstable : (prefixWord ++ tailWord_1427290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427290).length < 2 ^ (prefixWord ++ tailWord_1427290).sum := by decide
  have hdescent : baseEnd_1427290 < baseStart_1427290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427303 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_1427303 : Nat := 118140960795 + 1427303 * 2 ^ 59
def prefixEnd_1427303 : Nat := 4983230072969 + 3 ^ 40 * 1427303 * 2
def baseEnd_1427303 : Nat := 732892478604334404148459

theorem tailTrace_1427303 : CollatzResearch.WordTrace tailWord_1427303 prefixEnd_1427303 732892478604334404148459 := by
  unfold tailWord_1427303
  simp only [CollatzResearch.WordTrace]
  refine ⟨52058017148132469790470563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34705344765421646526980375 52058017148132469790470563)
  ·
    refine ⟨78087025722198704685705845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52058017148132469790470563 78087025722198704685705845)
    ·
      refine ⟨7320658661456128564284923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78087025722198704685705845 7320658661456128564284923)
      ·
        refine ⟨10980987992184192846427385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7320658661456128564284923 10980987992184192846427385)
        ·
          refine ⟨8235740994138144634820539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10980987992184192846427385 8235740994138144634820539)
          ·
            refine ⟨12353611491207216952230809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8235740994138144634820539 12353611491207216952230809)
            ·
              refine ⟨9265208618405412714173107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12353611491207216952230809 9265208618405412714173107)
              ·
                refine ⟨13897812927608119071259661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9265208618405412714173107 13897812927608119071259661)
                ·
                  refine ⟨5211679847853044651722373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13897812927608119071259661 5211679847853044651722373)
                  ·
                    refine ⟨977189971472445872197945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211679847853044651722373 977189971472445872197945)
                    ·
                      refine ⟨732892478604334404148459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977189971472445872197945 732892478604334404148459)
                      ·
                        rfl

theorem cell23_1427303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_1427303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427303 prefixEnd_1427303 := by exact prefixLift 1427303
  have htrace : WordTrace (prefixWord ++ tailWord_1427303) baseStart_1427303 baseEnd_1427303 := by
    simpa [prefixWord, tailWord_1427303, baseEnd_1427303] using wordTrace_append hprefix tailTrace_1427303
  have hstable : (prefixWord ++ tailWord_1427303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427303).length < 2 ^ (prefixWord ++ tailWord_1427303).sum := by decide
  have hdescent : baseEnd_1427303 < baseStart_1427303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427377 : List Nat := [1, 2, 2, 4, 2, 3, 2, 2, 5]
def baseStart_1427377 : Nat := 118140960795 + 1427377 * 2 ^ 59
def prefixEnd_1427377 : Nat := 4983230072969 + 3 ^ 40 * 1427377 * 2
def baseEnd_1427377 : Nat := 81436719574751901624791

theorem tailTrace_1427377 : CollatzResearch.WordTrace tailWord_1427377 prefixEnd_1427377 81436719574751901624791 := by
  unfold tailWord_1427377
  simp only [CollatzResearch.WordTrace]
  refine ⟨52060716149864380428664385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34707144099909586952442923 52060716149864380428664385)
  ·
    refine ⟨39045537112398285321498289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52060716149864380428664385 39045537112398285321498289)
    ·
      refine ⟨29284152834298713991123717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39045537112398285321498289 29284152834298713991123717)
      ·
        refine ⟨5490778656431008873335697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29284152834298713991123717 5490778656431008873335697)
        ·
          refine ⟨4118083992323256655001773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5490778656431008873335697 4118083992323256655001773)
          ·
            refine ⟨1544281497121221245625665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4118083992323256655001773 1544281497121221245625665)
            ·
              refine ⟨1158211122840915934219249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1544281497121221245625665 1158211122840915934219249)
              ·
                refine ⟨868658342130686950664437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1158211122840915934219249 868658342130686950664437)
                ·
                  refine ⟨81436719574751901624791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 868658342130686950664437 81436719574751901624791)
                  ·
                    rfl

theorem cell23_1427377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 5].length) (baseStart_1427377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427377 prefixEnd_1427377 := by exact prefixLift 1427377
  have htrace : WordTrace (prefixWord ++ tailWord_1427377) baseStart_1427377 baseEnd_1427377 := by
    simpa [prefixWord, tailWord_1427377, baseEnd_1427377] using wordTrace_append hprefix tailTrace_1427377
  have hstable : (prefixWord ++ tailWord_1427377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427377).length < 2 ^ (prefixWord ++ tailWord_1427377).sum := by decide
  have hdescent : baseEnd_1427377 < baseStart_1427377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427403 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 3, 4]
def baseStart_1427403 : Nat := 118140960795 + 1427403 * 2 ^ 59
def prefixEnd_1427403 : Nat := 4983230072969 + 3 ^ 40 * 1427403 * 2
def baseEnd_1427403 : Nat := 244314608889928004299333

theorem tailTrace_1427403 : CollatzResearch.WordTrace tailWord_1427403 prefixEnd_1427403 244314608889928004299333 := by
  unfold tailWord_1427403
  simp only [CollatzResearch.WordTrace]
  refine ⟨52061664447770186869110863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34707776298513457912740575 52061664447770186869110863)
  ·
    refine ⟨78092496671655280303666295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52061664447770186869110863 78092496671655280303666295)
    ·
      refine ⟨117138745007482920455499443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78092496671655280303666295 117138745007482920455499443)
      ·
        refine ⟨175708117511224380683249165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117138745007482920455499443 175708117511224380683249165)
        ·
          refine ⟨65890544066709142756218437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175708117511224380683249165 65890544066709142756218437)
          ·
            refine ⟨12354477012507964266790957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65890544066709142756218437 12354477012507964266790957)
            ·
              refine ⟨4632928879690486600046609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12354477012507964266790957 4632928879690486600046609)
              ·
                refine ⟨3474696659767864950034957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4632928879690486600046609 3474696659767864950034957)
                ·
                  refine ⟨1303011247412949356263109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3474696659767864950034957 1303011247412949356263109)
                  ·
                    refine ⟨244314608889928004299333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1303011247412949356263109 244314608889928004299333)
                    ·
                      rfl

theorem cell23_1427403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 4].length) (baseStart_1427403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427403 prefixEnd_1427403 := by exact prefixLift 1427403
  have htrace : WordTrace (prefixWord ++ tailWord_1427403) baseStart_1427403 baseEnd_1427403 := by
    simpa [prefixWord, tailWord_1427403, baseEnd_1427403] using wordTrace_append hprefix tailTrace_1427403
  have hstable : (prefixWord ++ tailWord_1427403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427403).length < 2 ^ (prefixWord ++ tailWord_1427403).sum := by decide
  have hdescent : baseEnd_1427403 < baseStart_1427403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427410 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1427410 : Nat := 118140960795 + 1427410 * 2 ^ 59
def prefixEnd_1427410 : Nat := 4983230072969 + 3 ^ 40 * 1427410 * 2
def baseEnd_1427410 : Nat := 732947421034365485510467

theorem tailTrace_1427410 : CollatzResearch.WordTrace tailWord_1427410 prefixEnd_1427410 732947421034365485510467 := by
  unfold tailWord_1427410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13015479939686206766153921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34707946505829884709743789 13015479939686206766153921)
  ·
    refine ⟨9761609954764655074615441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13015479939686206766153921 9761609954764655074615441)
    ·
      refine ⟨7321207466073491305961581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9761609954764655074615441 7321207466073491305961581)
      ·
        refine ⟨2745452799777559239735593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7321207466073491305961581 2745452799777559239735593)
        ·
          refine ⟨2059089599833169429801695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2745452799777559239735593 2059089599833169429801695)
          ·
            refine ⟨3088634399749754144702543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059089599833169429801695 3088634399749754144702543)
            ·
              refine ⟨4632951599624631217053815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088634399749754144702543 4632951599624631217053815)
              ·
                refine ⟨6949427399436946825580723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632951599624631217053815 6949427399436946825580723)
                ·
                  refine ⟨10424141099155420238371085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6949427399436946825580723 10424141099155420238371085)
                  ·
                    refine ⟨3909052912183282589389157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10424141099155420238371085 3909052912183282589389157)
                    ·
                      refine ⟨732947421034365485510467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3909052912183282589389157 732947421034365485510467)
                      ·
                        rfl

theorem cell23_1427410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1427410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427410 prefixEnd_1427410 := by exact prefixLift 1427410
  have htrace : WordTrace (prefixWord ++ tailWord_1427410) baseStart_1427410 baseEnd_1427410 := by
    simpa [prefixWord, tailWord_1427410, baseEnd_1427410] using wordTrace_append hprefix tailTrace_1427410
  have hstable : (prefixWord ++ tailWord_1427410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427410).length < 2 ^ (prefixWord ++ tailWord_1427410).sum := by decide
  have hdescent : baseEnd_1427410 < baseStart_1427410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427416 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 8]
def baseStart_1427416 : Nat := 118140960795 + 1427416 * 2 ^ 59
def prefixEnd_1427416 : Nat := 4983230072969 + 3 ^ 40 * 1427416 * 2
def baseEnd_1427416 : Nat := 81438944657588051337271

theorem tailTrace_1427416 : CollatzResearch.WordTrace tailWord_1427416 prefixEnd_1427416 81438944657588051337271 := by
  unfold tailWord_1427416
  simp only [CollatzResearch.WordTrace]
  refine ⟨26031069298361545044667051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34708092397815393392889401 26031069298361545044667051)
  ·
    refine ⟨39046603947542317567000577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26031069298361545044667051 39046603947542317567000577)
    ·
      refine ⟨29284952960656738175250433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39046603947542317567000577 29284952960656738175250433)
      ·
        refine ⟨21963714720492553631437825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29284952960656738175250433 21963714720492553631437825)
        ·
          refine ⟨16472786040369415223578369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21963714720492553631437825 16472786040369415223578369)
          ·
            refine ⟨12354589530277061417683777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16472786040369415223578369 12354589530277061417683777)
            ·
              refine ⟨9265942147707796063262833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12354589530277061417683777 9265942147707796063262833)
              ·
                refine ⟨6949456610780847047447125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9265942147707796063262833 6949456610780847047447125)
                ·
                  refine ⟨81438944657588051337271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6949456610780847047447125 81438944657588051337271)
                  ·
                    rfl

theorem cell23_1427416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 8].length) (baseStart_1427416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427416 prefixEnd_1427416 := by exact prefixLift 1427416
  have htrace : WordTrace (prefixWord ++ tailWord_1427416) baseStart_1427416 baseEnd_1427416 := by
    simpa [prefixWord, tailWord_1427416, baseEnd_1427416] using wordTrace_append hprefix tailTrace_1427416
  have hstable : (prefixWord ++ tailWord_1427416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427416).length < 2 ^ (prefixWord ++ tailWord_1427416).sum := by decide
  have hdescent : baseEnd_1427416 < baseStart_1427416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427470 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2]
def baseStart_1427470 : Nat := 118140960795 + 1427470 * 2 ^ 59
def prefixEnd_1427470 : Nat := 4983230072969 + 3 ^ 40 * 1427470 * 2
def baseEnd_1427470 : Nat := 732978229873635250760191

theorem tailTrace_1427470 : CollatzResearch.WordTrace tailWord_1427470 prefixEnd_1427470 732978229873635250760191 := by
  unfold tailWord_1427470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6508013517315932163974983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34709405425684971541199909 6508013517315932163974983)
  ·
    refine ⟨9762020275973898245962475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6508013517315932163974983 9762020275973898245962475)
    ·
      refine ⟨14643030413960847368943713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9762020275973898245962475 14643030413960847368943713)
      ·
        refine ⟨10982272810470635526707785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14643030413960847368943713 10982272810470635526707785)
        ·
          refine ⟨8236704607852976645030839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10982272810470635526707785 8236704607852976645030839)
          ·
            refine ⟨12355056911779464967546259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8236704607852976645030839 12355056911779464967546259)
            ·
              refine ⟨18532585367669197451319389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12355056911779464967546259 18532585367669197451319389)
              ·
                refine ⟨6949719512875949044244771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18532585367669197451319389 6949719512875949044244771)
                ·
                  refine ⟨10424579269313923566367157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6949719512875949044244771 10424579269313923566367157)
                  ·
                    refine ⟨977304306498180334346921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10424579269313923566367157 977304306498180334346921)
                    ·
                      refine ⟨732978229873635250760191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977304306498180334346921 732978229873635250760191)
                      ·
                        rfl

theorem cell23_1427470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_1427470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427470 prefixEnd_1427470 := by exact prefixLift 1427470
  have htrace : WordTrace (prefixWord ++ tailWord_1427470) baseStart_1427470 baseEnd_1427470 := by
    simpa [prefixWord, tailWord_1427470, baseEnd_1427470] using wordTrace_append hprefix tailTrace_1427470
  have hstable : (prefixWord ++ tailWord_1427470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427470).length < 2 ^ (prefixWord ++ tailWord_1427470).sum := by decide
  have hdescent : baseEnd_1427470 < baseStart_1427470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427510 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1427510 : Nat := 118140960795 + 1427510 * 2 ^ 59
def prefixEnd_1427510 : Nat := 4983230072969 + 3 ^ 40 * 1427510 * 2
def baseEnd_1427510 : Nat := 244332923033271698086669

theorem tailTrace_1427510 : CollatzResearch.WordTrace tailWord_1427510 prefixEnd_1427510 244332923033271698086669 := by
  unfold tailWord_1427510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254097941148909008953499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34710378038921696095503989 3254097941148909008953499)
  ·
    refine ⟨4881146911723363513430249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254097941148909008953499 4881146911723363513430249)
    ·
      refine ⟨3660860183792522635072687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4881146911723363513430249 3660860183792522635072687)
      ·
        refine ⟨5491290275688783952609031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3660860183792522635072687 5491290275688783952609031)
        ·
          refine ⟨8236935413533175928913547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491290275688783952609031 8236935413533175928913547)
          ·
            refine ⟨12355403120299763893370321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8236935413533175928913547 12355403120299763893370321)
            ·
              refine ⟨9266552340224822920027741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12355403120299763893370321 9266552340224822920027741)
              ·
                refine ⟨3474957127584308595010403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9266552340224822920027741 3474957127584308595010403)
                ·
                  refine ⟨5212435691376462892515605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474957127584308595010403 5212435691376462892515605)
                  ·
                    refine ⟨244332923033271698086669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5212435691376462892515605 244332923033271698086669)
                    ·
                      rfl

theorem cell23_1427510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1427510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427510 prefixEnd_1427510 := by exact prefixLift 1427510
  have htrace : WordTrace (prefixWord ++ tailWord_1427510) baseStart_1427510 baseEnd_1427510 := by
    simpa [prefixWord, tailWord_1427510, baseEnd_1427510] using wordTrace_append hprefix tailTrace_1427510
  have hstable : (prefixWord ++ tailWord_1427510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427510).length < 2 ^ (prefixWord ++ tailWord_1427510).sum := by decide
  have hdescent : baseEnd_1427510 < baseStart_1427510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427517 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 5, 2, 2]
def baseStart_1427517 : Nat := 118140960795 + 1427517 * 2 ^ 59
def prefixEnd_1427517 : Nat := 4983230072969 + 3 ^ 40 * 1427517 * 2
def baseEnd_1427517 : Nat := 733002363464396566872475

theorem tailTrace_1427517 : CollatzResearch.WordTrace tailWord_1427517 prefixEnd_1427517 733002363464396566872475 := by
  unfold tailWord_1427517
  simp only [CollatzResearch.WordTrace]
  refine ⟨52065822369357184338760805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34710548246238122892507203 52065822369357184338760805)
  ·
    refine ⟨9762341694254472063517651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52065822369357184338760805 9762341694254472063517651)
    ·
      refine ⟨14643512541381708095276477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9762341694254472063517651 14643512541381708095276477)
      ·
        refine ⟨5491317203018140535728679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14643512541381708095276477 5491317203018140535728679)
        ·
          refine ⟨8236975804527210803593019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491317203018140535728679 8236975804527210803593019)
          ·
            refine ⟨12355463706790816205389529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8236975804527210803593019 12355463706790816205389529)
            ·
              refine ⟨9266597780093112154042147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12355463706790816205389529 9266597780093112154042147)
              ·
                refine ⟨13899896670139668231063221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9266597780093112154042147 13899896670139668231063221)
                ·
                  refine ⟨1303115312825593896662177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13899896670139668231063221 1303115312825593896662177)
                  ·
                    refine ⟨977336484619195422496633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1303115312825593896662177 977336484619195422496633)
                    ·
                      refine ⟨733002363464396566872475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977336484619195422496633 733002363464396566872475)
                      ·
                        rfl

theorem cell23_1427517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_1427517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427517 prefixEnd_1427517 := by exact prefixLift 1427517
  have htrace : WordTrace (prefixWord ++ tailWord_1427517) baseStart_1427517 baseEnd_1427517 := by
    simpa [prefixWord, tailWord_1427517, baseEnd_1427517] using wordTrace_append hprefix tailTrace_1427517
  have hstable : (prefixWord ++ tailWord_1427517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427517).length < 2 ^ (prefixWord ++ tailWord_1427517).sum := by decide
  have hdescent : baseEnd_1427517 < baseStart_1427517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427520 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 3]
def baseStart_1427520 : Nat := 118140960795 + 1427520 * 2 ^ 59
def prefixEnd_1427520 : Nat := 4983230072969 + 3 ^ 40 * 1427520 * 2
def baseEnd_1427520 : Nat := 733003903906360055134961

theorem tailTrace_1427520 : CollatzResearch.WordTrace tailWord_1427520 prefixEnd_1427520 733003903906360055134961 := by
  unfold tailWord_1427520
  simp only [CollatzResearch.WordTrace]
  refine ⟨26032965894173157925560007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34710621192230877234080009 26032965894173157925560007)
  ·
    refine ⟨39049448841259736888340011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26032965894173157925560007 39049448841259736888340011)
    ·
      refine ⟨58574173261889605332510017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39049448841259736888340011 58574173261889605332510017)
      ·
        refine ⟨43930629946417203999382513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58574173261889605332510017 43930629946417203999382513)
        ·
          refine ⟨32947972459812902999536885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43930629946417203999382513 32947972459812902999536885)
          ·
            refine ⟨3088872418107459656206583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32947972459812902999536885 3088872418107459656206583)
            ·
              refine ⟨4633308627161189484309875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088872418107459656206583 4633308627161189484309875)
              ·
                refine ⟨6949962940741784226464813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4633308627161189484309875 6949962940741784226464813)
                ·
                  refine ⟨2606236102778169084924305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6949962940741784226464813 2606236102778169084924305)
                  ·
                    refine ⟨1954677077083626813693229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2606236102778169084924305 1954677077083626813693229)
                    ·
                      refine ⟨733003903906360055134961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1954677077083626813693229 733003903906360055134961)
                      ·
                        rfl

theorem cell23_1427520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_1427520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427520 prefixEnd_1427520 := by exact prefixLift 1427520
  have htrace : WordTrace (prefixWord ++ tailWord_1427520) baseStart_1427520 baseEnd_1427520 := by
    simpa [prefixWord, tailWord_1427520, baseEnd_1427520] using wordTrace_append hprefix tailTrace_1427520
  have hstable : (prefixWord ++ tailWord_1427520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427520).length < 2 ^ (prefixWord ++ tailWord_1427520).sum := by decide
  have hdescent : baseEnd_1427520 < baseStart_1427520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427567 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 2, 1, 3]
def baseStart_1427567 : Nat := 118140960795 + 1427567 * 2 ^ 59
def prefixEnd_1427567 : Nat := 4983230072969 + 3 ^ 40 * 1427567 * 2
def baseEnd_1427567 : Nat := 733028037497121371247245

theorem tailTrace_1427567 : CollatzResearch.WordTrace tailWord_1427567 prefixEnd_1427567 733028037497121371247245 := by
  unfold tailWord_1427567
  simp only [CollatzResearch.WordTrace]
  refine ⟨52067646019176042878080955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34711764012784028585387303 52067646019176042878080955)
  ·
    refine ⟨78101469028764064317121433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52067646019176042878080955 78101469028764064317121433)
    ·
      refine ⟨58576101771573048237841075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78101469028764064317121433 58576101771573048237841075)
      ·
        refine ⟨87864152657359572356761613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58576101771573048237841075 87864152657359572356761613)
        ·
          refine ⟨32949057246509839633785605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87864152657359572356761613 32949057246509839633785605)
          ·
            refine ⟨6177948233720594931334801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32949057246509839633785605 6177948233720594931334801)
            ·
              refine ⟨4633461175290446198501101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6177948233720594931334801 4633461175290446198501101)
              ·
                refine ⟨1737547940733917324437913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4633461175290446198501101 1737547940733917324437913)
                ·
                  refine ⟨1303160955550437993328435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1737547940733917324437913 1303160955550437993328435)
                  ·
                    refine ⟨1954741433325656989992653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1303160955550437993328435 1954741433325656989992653)
                    ·
                      refine ⟨733028037497121371247245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1954741433325656989992653 733028037497121371247245)
                      ·
                        rfl

theorem cell23_1427567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 1, 3].length) (baseStart_1427567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427567 prefixEnd_1427567 := by exact prefixLift 1427567
  have htrace : WordTrace (prefixWord ++ tailWord_1427567) baseStart_1427567 baseEnd_1427567 := by
    simpa [prefixWord, tailWord_1427567, baseEnd_1427567] using wordTrace_append hprefix tailTrace_1427567
  have hstable : (prefixWord ++ tailWord_1427567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427567).length < 2 ^ (prefixWord ++ tailWord_1427567).sum := by decide
  have hdescent : baseEnd_1427567 < baseStart_1427567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427577 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 3, 3, 2]
def baseStart_1427577 : Nat := 118140960795 + 1427577 * 2 ^ 59
def prefixEnd_1427577 : Nat := 4983230072969 + 3 ^ 40 * 1427577 * 2
def baseEnd_1427577 : Nat := 733033172303666332122199

theorem tailTrace_1427577 : CollatzResearch.WordTrace tailWord_1427577 prefixEnd_1427577 733033172303666332122199 := by
  unfold tailWord_1427577
  simp only [CollatzResearch.WordTrace]
  refine ⟨52068010749139814585944985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34712007166093209723963323 52068010749139814585944985)
  ·
    refine ⟨39051008061854860939458739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52068010749139814585944985 39051008061854860939458739)
    ·
      refine ⟨58576512092782291409188109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39051008061854860939458739 58576512092782291409188109)
      ·
        refine ⟨21966192034793359278445541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58576512092782291409188109 21966192034793359278445541)
        ·
          refine ⟨4118661006523754864708539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21966192034793359278445541 4118661006523754864708539)
          ·
            refine ⟨6177991509785632297062809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4118661006523754864708539 6177991509785632297062809)
            ·
              refine ⟨4633493632339224222797107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6177991509785632297062809 4633493632339224222797107)
              ·
                refine ⟨6950240448508836334195661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4633493632339224222797107 6950240448508836334195661)
                ·
                  refine ⟨2606340168190813625323373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6950240448508836334195661 2606340168190813625323373)
                  ·
                    refine ⟨977377563071555109496265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606340168190813625323373 977377563071555109496265)
                    ·
                      refine ⟨733033172303666332122199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977377563071555109496265 733033172303666332122199)
                      ·
                        rfl

theorem cell23_1427577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_1427577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427577 prefixEnd_1427577 := by exact prefixLift 1427577
  have htrace : WordTrace (prefixWord ++ tailWord_1427577) baseStart_1427577 baseEnd_1427577 := by
    simpa [prefixWord, tailWord_1427577, baseEnd_1427577] using wordTrace_append hprefix tailTrace_1427577
  have hstable : (prefixWord ++ tailWord_1427577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427577).length < 2 ^ (prefixWord ++ tailWord_1427577).sum := by decide
  have hdescent : baseEnd_1427577 < baseStart_1427577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427593 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_1427593 : Nat := 118140960795 + 1427593 * 2 ^ 59
def prefixEnd_1427593 : Nat := 4983230072969 + 3 ^ 40 * 1427593 * 2
def baseEnd_1427593 : Nat := 733041387994138269522125

theorem tailTrace_1427593 : CollatzResearch.WordTrace tailWord_1427593 prefixEnd_1427593 733041387994138269522125 := by
  unfold tailWord_1427593
  simp only [CollatzResearch.WordTrace]
  refine ⟨52068594317081849318527433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34712396211387899545684955 52068594317081849318527433)
  ·
    refine ⟨39051445737811386988895575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52068594317081849318527433 39051445737811386988895575)
    ·
      refine ⟨58577168606717080483343363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39051445737811386988895575 58577168606717080483343363)
      ·
        refine ⟨87865752910075620725015045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58577168606717080483343363 87865752910075620725015045)
        ·
          refine ⟨16474828670639178885940321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87865752910075620725015045 16474828670639178885940321)
          ·
            refine ⟨12356121502979384164455241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16474828670639178885940321 12356121502979384164455241)
            ·
              refine ⟨9267091127234538123341431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12356121502979384164455241 9267091127234538123341431)
              ·
                refine ⟨13900636690851807185012147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9267091127234538123341431 13900636690851807185012147)
                ·
                  refine ⟨20850955036277710777518221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13900636690851807185012147 20850955036277710777518221)
                  ·
                    refine ⟨7819108138604141541569333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20850955036277710777518221 7819108138604141541569333)
                    ·
                      refine ⟨733041387994138269522125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7819108138604141541569333 733041387994138269522125)
                      ·
                        rfl

theorem cell23_1427593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_1427593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427593 prefixEnd_1427593 := by exact prefixLift 1427593
  have htrace : WordTrace (prefixWord ++ tailWord_1427593) baseStart_1427593 baseEnd_1427593 := by
    simpa [prefixWord, tailWord_1427593, baseEnd_1427593] using wordTrace_append hprefix tailTrace_1427593
  have hstable : (prefixWord ++ tailWord_1427593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427593).length < 2 ^ (prefixWord ++ tailWord_1427593).sum := by decide
  have hdescent : baseEnd_1427593 < baseStart_1427593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427594 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2]
def baseStart_1427594 : Nat := 118140960795 + 1427594 * 2 ^ 59
def prefixEnd_1427594 : Nat := 4983230072969 + 3 ^ 40 * 1427594 * 2
def baseEnd_1427594 : Nat := 733041901474792765609621

theorem tailTrace_1427594 : CollatzResearch.WordTrace tailWord_1427594 prefixEnd_1427594 733041901474792765609621 := by
  unfold tailWord_1427594
  simp only [CollatzResearch.WordTrace]
  refine ⟨13017157697519556622328459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34712420526718817659542557 13017157697519556622328459)
  ·
    refine ⟨19525736546279334933492689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13017157697519556622328459 19525736546279334933492689)
    ·
      refine ⟨14644302409709501200119517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19525736546279334933492689 14644302409709501200119517)
      ·
        refine ⟨5491613403641062950044819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14644302409709501200119517 5491613403641062950044819)
        ·
          refine ⟨8237420105461594425067229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491613403641062950044819 8237420105461594425067229)
          ·
            refine ⟨3089032539548097909400211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8237420105461594425067229 3089032539548097909400211)
            ·
              refine ⟨4633548809322146864100317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089032539548097909400211 4633548809322146864100317)
              ·
                refine ⟨1737580803495805074037619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4633548809322146864100317 1737580803495805074037619)
                ·
                  refine ⟨2606371205243707611056429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737580803495805074037619 2606371205243707611056429)
                  ·
                    refine ⟨977389201966390354146161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606371205243707611056429 977389201966390354146161)
                    ·
                      refine ⟨733041901474792765609621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977389201966390354146161 733041901474792765609621)
                      ·
                        rfl

theorem cell23_1427594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_1427594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427594 prefixEnd_1427594 := by exact prefixLift 1427594
  have htrace : WordTrace (prefixWord ++ tailWord_1427594) baseStart_1427594 baseEnd_1427594 := by
    simpa [prefixWord, tailWord_1427594, baseEnd_1427594] using wordTrace_append hprefix tailTrace_1427594
  have hstable : (prefixWord ++ tailWord_1427594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427594).length < 2 ^ (prefixWord ++ tailWord_1427594).sum := by decide
  have hdescent : baseEnd_1427594 < baseStart_1427594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427643 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 1, 7]
def baseStart_1427643 : Nat := 118140960795 + 1427643 * 2 ^ 59
def prefixEnd_1427643 : Nat := 4983230072969 + 3 ^ 40 * 1427643 * 2
def baseEnd_1427643 : Nat := 244355687342287691298965

theorem tailTrace_1427643 : CollatzResearch.WordTrace tailWord_1427643 prefixEnd_1427643 244355687342287691298965 := by
  unfold tailWord_1427643
  simp only [CollatzResearch.WordTrace]
  refine ⟨52070417966900707857847583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34713611977933805238565055 52070417966900707857847583)
  ·
    refine ⟨78105626950351061786771375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52070417966900707857847583 78105626950351061786771375)
    ·
      refine ⟨117158440425526592680157063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78105626950351061786771375 117158440425526592680157063)
      ·
        refine ⟨175737660638289889020235595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117158440425526592680157063 175737660638289889020235595)
        ·
          refine ⟨263606490957434833530353393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175737660638289889020235595 263606490957434833530353393)
          ·
            refine ⟨197704868218076125147765045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263606490957434833530353393 197704868218076125147765045)
            ·
              refine ⟨18534831395444636732602973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197704868218076125147765045 18534831395444636732602973)
              ·
                refine ⟨6950561773291738774726115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18534831395444636732602973 6950561773291738774726115)
                ·
                  refine ⟨10425842659937608162089173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6950561773291738774726115 10425842659937608162089173)
                  ·
                    refine ⟨244355687342287691298965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10425842659937608162089173 244355687342287691298965)
                    ·
                      rfl

theorem cell23_1427643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 7].length) (baseStart_1427643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427643 prefixEnd_1427643 := by exact prefixLift 1427643
  have htrace : WordTrace (prefixWord ++ tailWord_1427643) baseStart_1427643 baseEnd_1427643 := by
    simpa [prefixWord, tailWord_1427643, baseEnd_1427643] using wordTrace_append hprefix tailTrace_1427643
  have hstable : (prefixWord ++ tailWord_1427643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427643).length < 2 ^ (prefixWord ++ tailWord_1427643).sum := by decide
  have hdescent : baseEnd_1427643 < baseStart_1427643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427680 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 4]
def baseStart_1427680 : Nat := 118140960795 + 1427680 * 2 ^ 59
def prefixEnd_1427680 : Nat := 4983230072969 + 3 ^ 40 * 1427680 * 2
def baseEnd_1427680 : Nat := 733086060811079429134225

theorem tailTrace_1427680 : CollatzResearch.WordTrace tailWord_1427680 prefixEnd_1427680 733086060811079429134225 := by
  unfold tailWord_1427680
  simp only [CollatzResearch.WordTrace]
  refine ⟨26035883733883331588472247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34714511645177775451296329 26035883733883331588472247)
  ·
    refine ⟨39053825600824997382708371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26035883733883331588472247 39053825600824997382708371)
    ·
      refine ⟨58580738401237496074062557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39053825600824997382708371 58580738401237496074062557)
      ·
        refine ⟨21967776900464061027773459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58580738401237496074062557 21967776900464061027773459)
        ·
          refine ⟨32951665350696091541660189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21967776900464061027773459 32951665350696091541660189)
          ·
            refine ⟨12356874506511034328122571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32951665350696091541660189 12356874506511034328122571)
            ·
              refine ⟨18535311759766551492183857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12356874506511034328122571 18535311759766551492183857)
              ·
                refine ⟨13901483819824913619137893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18535311759766551492183857 13901483819824913619137893)
                ·
                  refine ⟨2606528216217171303588355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13901483819824913619137893 2606528216217171303588355)
                  ·
                    refine ⟨3909792324325756955382533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2606528216217171303588355 3909792324325756955382533)
                    ·
                      refine ⟨733086060811079429134225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3909792324325756955382533 733086060811079429134225)
                      ·
                        rfl

theorem cell23_1427680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_1427680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427680 prefixEnd_1427680 := by exact prefixLift 1427680
  have htrace : WordTrace (prefixWord ++ tailWord_1427680) baseStart_1427680 baseEnd_1427680 := by
    simpa [prefixWord, tailWord_1427680, baseEnd_1427680] using wordTrace_append hprefix tailTrace_1427680
  have hstable : (prefixWord ++ tailWord_1427680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427680).length < 2 ^ (prefixWord ++ tailWord_1427680).sum := by decide
  have hdescent : baseEnd_1427680 < baseStart_1427680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427714 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1427714 : Nat := 118140960795 + 1427714 * 2 ^ 59
def prefixEnd_1427714 : Nat := 4983230072969 + 3 ^ 40 * 1427714 * 2
def baseEnd_1427714 : Nat := 733103519153332296109069

theorem tailTrace_1427714 : CollatzResearch.WordTrace tailWord_1427714 prefixEnd_1427714 733103519153332296109069 := by
  unfold tailWord_1427714
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018251887410871745920549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34715338366428991322454797 13018251887410871745920549)
  ·
    refine ⟨2440922228889538452360103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13018251887410871745920549 2440922228889538452360103)
    ·
      refine ⟨3661383343334307678540155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2440922228889538452360103 3661383343334307678540155)
      ·
        refine ⟨5492075015001461517810233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3661383343334307678540155 5492075015001461517810233)
        ·
          refine ⟨4119056261251096138357675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5492075015001461517810233 4119056261251096138357675)
          ·
            refine ⟨6178584391876644207536513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4119056261251096138357675 6178584391876644207536513)
            ·
              refine ⟨4633938293907483155652385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6178584391876644207536513 4633938293907483155652385)
              ·
                refine ⟨3475453720430612366739289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4633938293907483155652385 3475453720430612366739289)
                ·
                  refine ⟨2606590290322959275054467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3475453720430612366739289 2606590290322959275054467)
                  ·
                    refine ⟨3909885435484438912581701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2606590290322959275054467 3909885435484438912581701)
                    ·
                      refine ⟨733103519153332296109069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3909885435484438912581701 733103519153332296109069)
                      ·
                        rfl

theorem cell23_1427714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1427714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427714 prefixEnd_1427714 := by exact prefixLift 1427714
  have htrace : WordTrace (prefixWord ++ tailWord_1427714) baseStart_1427714 baseEnd_1427714 := by
    simpa [prefixWord, tailWord_1427714, baseEnd_1427714] using wordTrace_append hprefix tailTrace_1427714
  have hstable : (prefixWord ++ tailWord_1427714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427714).length < 2 ^ (prefixWord ++ tailWord_1427714).sum := by decide
  have hdescent : baseEnd_1427714 < baseStart_1427714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427724 : List Nat := [2, 2, 1, 2, 2, 2, 3, 4, 1, 4]
def baseStart_1427724 : Nat := 118140960795 + 1427724 * 2 ^ 59
def prefixEnd_1427724 : Nat := 4983230072969 + 3 ^ 40 * 1427724 * 2
def baseEnd_1427724 : Nat := 244369551319959085661341

theorem tailTrace_1427724 : CollatzResearch.WordTrace tailWord_1427724 prefixEnd_1427724 244369551319959085661341 := by
  unfold tailWord_1427724
  simp only [CollatzResearch.WordTrace]
  refine ⟨26036686139803629345773113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34715581519738172461030817 26036686139803629345773113)
  ·
    refine ⟨19527514604852722009329835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26036686139803629345773113 19527514604852722009329835)
    ·
      refine ⟨29291271907279083013994753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19527514604852722009329835 29291271907279083013994753)
      ·
        refine ⟨21968453930459312260496065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29291271907279083013994753 21968453930459312260496065)
        ·
          refine ⟨16476340447844484195372049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21968453930459312260496065 16476340447844484195372049)
          ·
            refine ⟨12357255335883363146529037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16476340447844484195372049 12357255335883363146529037)
            ·
              refine ⟨4633970750956261179948389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12357255335883363146529037 4633970750956261179948389)
              ·
                refine ⟨868869515804298971240323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4633970750956261179948389 868869515804298971240323)
                ·
                  refine ⟨1303304273706448456860485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868869515804298971240323 1303304273706448456860485)
                  ·
                    refine ⟨244369551319959085661341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1303304273706448456860485 244369551319959085661341)
                    ·
                      rfl

theorem cell23_1427724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_1427724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427724 prefixEnd_1427724 := by exact prefixLift 1427724
  have htrace : WordTrace (prefixWord ++ tailWord_1427724) baseStart_1427724 baseEnd_1427724 := by
    simpa [prefixWord, tailWord_1427724, baseEnd_1427724] using wordTrace_append hprefix tailTrace_1427724
  have hstable : (prefixWord ++ tailWord_1427724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427724).length < 2 ^ (prefixWord ++ tailWord_1427724).sum := by decide
  have hdescent : baseEnd_1427724 < baseStart_1427724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427807 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 3]
def baseStart_1427807 : Nat := 118140960795 + 1427807 * 2 ^ 59
def prefixEnd_1427807 : Nat := 4983230072969 + 3 ^ 40 * 1427807 * 2
def baseEnd_1427807 : Nat := 733151272854200432246141

theorem tailTrace_1427807 : CollatzResearch.WordTrace tailWord_1427807 prefixEnd_1427807 733151272854200432246141 := by
  unfold tailWord_1427807
  simp only [CollatzResearch.WordTrace]
  refine ⟨52076399538306563866817675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34717599692204375911211783 52076399538306563866817675)
  ·
    refine ⟨78114599307459845800226513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52076399538306563866817675 78114599307459845800226513)
    ·
      refine ⟨58585949480594884350169885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78114599307459845800226513 58585949480594884350169885)
      ·
        refine ⟨21969731055223081631313707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58585949480594884350169885 21969731055223081631313707)
        ·
          refine ⟨32954596582834622446970561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21969731055223081631313707 32954596582834622446970561)
          ·
            refine ⟨24715947437125966835227921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32954596582834622446970561 24715947437125966835227921)
            ·
              refine ⟨18536960577844475126420941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24715947437125966835227921 18536960577844475126420941)
              ·
                refine ⟨6951360216691678172407853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18536960577844475126420941 6951360216691678172407853)
                ·
                  refine ⟨2606760081259379314652945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6951360216691678172407853 2606760081259379314652945)
                  ·
                    refine ⟨1955070060944534485989709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2606760081259379314652945 1955070060944534485989709)
                    ·
                      refine ⟨733151272854200432246141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1955070060944534485989709 733151272854200432246141)
                      ·
                        rfl

theorem cell23_1427807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_1427807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427807 prefixEnd_1427807 := by exact prefixLift 1427807
  have htrace : WordTrace (prefixWord ++ tailWord_1427807) baseStart_1427807 baseEnd_1427807 := by
    simpa [prefixWord, tailWord_1427807, baseEnd_1427807] using wordTrace_append hprefix tailTrace_1427807
  have hstable : (prefixWord ++ tailWord_1427807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427807).length < 2 ^ (prefixWord ++ tailWord_1427807).sum := by decide
  have hdescent : baseEnd_1427807 < baseStart_1427807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427824 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 3]
def baseStart_1427824 : Nat := 118140960795 + 1427824 * 2 ^ 59
def prefixEnd_1427824 : Nat := 4983230072969 + 3 ^ 40 * 1427824 * 2
def baseEnd_1427824 : Nat := 733160002025326865733563

theorem tailTrace_1427824 : CollatzResearch.WordTrace tailWord_1427824 prefixEnd_1427824 733160002025326865733563 := by
  unfold tailWord_1427824
  simp only [CollatzResearch.WordTrace]
  refine ⟨26038509789622487885093263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34718013052829983846791017 26038509789622487885093263)
  ·
    refine ⟨39057764684433731827639895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26038509789622487885093263 39057764684433731827639895)
    ·
      refine ⟨58586647026650597741459843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39057764684433731827639895 58586647026650597741459843)
      ·
        refine ⟨87879970539975896612189765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58586647026650597741459843 87879970539975896612189765)
        ·
          refine ⟨16477494476245480614785581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87879970539975896612189765 16477494476245480614785581)
          ·
            refine ⟨6179060428592055230544593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16477494476245480614785581 6179060428592055230544593)
            ·
              refine ⟨4634295321444041422908445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6179060428592055230544593 4634295321444041422908445)
              ·
                refine ⟨1737860745541515533590667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4634295321444041422908445 1737860745541515533590667)
                ·
                  refine ⟨2606791118312273300386001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737860745541515533590667 2606791118312273300386001)
                  ·
                    refine ⟨1955093338734204975289501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2606791118312273300386001 1955093338734204975289501)
                    ·
                      refine ⟨733160002025326865733563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1955093338734204975289501 733160002025326865733563)
                      ·
                        rfl

theorem cell23_1427824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 3].length) (baseStart_1427824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427824 prefixEnd_1427824 := by exact prefixLift 1427824
  have htrace : WordTrace (prefixWord ++ tailWord_1427824) baseStart_1427824 baseEnd_1427824 := by
    simpa [prefixWord, tailWord_1427824, baseEnd_1427824] using wordTrace_append hprefix tailTrace_1427824
  have hstable : (prefixWord ++ tailWord_1427824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427824).length < 2 ^ (prefixWord ++ tailWord_1427824).sum := by decide
  have hdescent : baseEnd_1427824 < baseStart_1427824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427905 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1427905 : Nat := 118140960795 + 1427905 * 2 ^ 59
def prefixEnd_1427905 : Nat := 4983230072969 + 3 ^ 40 * 1427905 * 2
def baseEnd_1427905 : Nat := 733201593958341048820691

theorem tailTrace_1427905 : CollatzResearch.WordTrace tailWord_1427905 prefixEnd_1427905 733201593958341048820691 := by
  unfold tailWord_1427905
  simp only [CollatzResearch.WordTrace]
  refine ⟨52079973891951526603885169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34719982594634351069256779 52079973891951526603885169)
  ·
    refine ⟨39059980418963644952913877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52079973891951526603885169 39059980418963644952913877)
    ·
      refine ⟨915468291069460428583919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39059980418963644952913877 915468291069460428583919)
      ·
        refine ⟨1373202436604190642875879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915468291069460428583919 1373202436604190642875879)
        ·
          refine ⟨2059803654906285964313819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373202436604190642875879 2059803654906285964313819)
          ·
            refine ⟨3089705482359428946470729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059803654906285964313819 3089705482359428946470729)
            ·
              refine ⟨2317279111769571709853047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089705482359428946470729 2317279111769571709853047)
              ·
                refine ⟨3475918667654357564779571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317279111769571709853047 3475918667654357564779571)
                ·
                  refine ⟨5213878001481536347169357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475918667654357564779571 5213878001481536347169357)
                  ·
                    refine ⟨1955204250555576130188509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5213878001481536347169357 1955204250555576130188509)
                    ·
                      refine ⟨733201593958341048820691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1955204250555576130188509 733201593958341048820691)
                      ·
                        rfl

theorem cell23_1427905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1427905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427905 prefixEnd_1427905 := by exact prefixLift 1427905
  have htrace : WordTrace (prefixWord ++ tailWord_1427905) baseStart_1427905 baseEnd_1427905 := by
    simpa [prefixWord, tailWord_1427905, baseEnd_1427905] using wordTrace_append hprefix tailTrace_1427905
  have hstable : (prefixWord ++ tailWord_1427905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427905).length < 2 ^ (prefixWord ++ tailWord_1427905).sum := by decide
  have hdescent : baseEnd_1427905 < baseStart_1427905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427911 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 1, 4, 2]
def baseStart_1427911 : Nat := 118140960795 + 1427911 * 2 ^ 59
def prefixEnd_1427911 : Nat := 4983230072969 + 3 ^ 40 * 1427911 * 2
def baseEnd_1427911 : Nat := 733204674842268025345663

theorem tailTrace_1427911 : CollatzResearch.WordTrace tailWord_1427911 prefixEnd_1427911 733204674842268025345663 := by
  unfold tailWord_1427911
  simp only [CollatzResearch.WordTrace]
  refine ⟨52080192729929789628603587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34720128486619859752402391 52080192729929789628603587)
  ·
    refine ⟨78120289094894684442905381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52080192729929789628603587 78120289094894684442905381)
    ·
      refine ⟨14647554205292753333044759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78120289094894684442905381 14647554205292753333044759)
      ·
        refine ⟨21971331307939129999567139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14647554205292753333044759 21971331307939129999567139)
        ·
          refine ⟨32956996961908694999350709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21971331307939129999567139 32956996961908694999350709)
          ·
            refine ⟨3089718465178940156189129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32956996961908694999350709 3089718465178940156189129)
            ·
              refine ⟨2317288848884205117141847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089718465178940156189129 2317288848884205117141847)
              ·
                refine ⟨3475933273326307675712771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317288848884205117141847 3475933273326307675712771)
                ·
                  refine ⟨5213899909989461513569157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475933273326307675712771 5213899909989461513569157)
                  ·
                    refine ⟨977606233123024033794217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5213899909989461513569157 977606233123024033794217)
                    ·
                      refine ⟨733204674842268025345663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977606233123024033794217 733204674842268025345663)
                      ·
                        rfl

theorem cell23_1427911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_1427911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427911 prefixEnd_1427911 := by exact prefixLift 1427911
  have htrace : WordTrace (prefixWord ++ tailWord_1427911) baseStart_1427911 baseEnd_1427911 := by
    simpa [prefixWord, tailWord_1427911, baseEnd_1427911] using wordTrace_append hprefix tailTrace_1427911
  have hstable : (prefixWord ++ tailWord_1427911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427911).length < 2 ^ (prefixWord ++ tailWord_1427911).sum := by decide
  have hdescent : baseEnd_1427911 < baseStart_1427911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427944 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_1427944 : Nat := 118140960795 + 1427944 * 2 ^ 59
def prefixEnd_1427944 : Nat := 4983230072969 + 3 ^ 40 * 1427944 * 2
def baseEnd_1427944 : Nat := 733221619703866396233011

theorem tailTrace_1427944 : CollatzResearch.WordTrace tailWord_1427944 prefixEnd_1427944 733221619703866396233011 := by
  unfold tailWord_1427944
  simp only [CollatzResearch.WordTrace]
  refine ⟨26040698169405118132277443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34720930892540157509703257 26040698169405118132277443)
  ·
    refine ⟨39061047254107677198416165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26040698169405118132277443 39061047254107677198416165)
    ·
      refine ⟨7323946360145189474703031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39061047254107677198416165 7323946360145189474703031)
      ·
        refine ⟨10985919540217784212054547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7323946360145189474703031 10985919540217784212054547)
        ·
          refine ⟨16478879310326676318081821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10985919540217784212054547 16478879310326676318081821)
          ·
            refine ⟨6179579741372503619280683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16478879310326676318081821 6179579741372503619280683)
            ·
              refine ⟨9269369612058755428921025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6179579741372503619280683 9269369612058755428921025)
              ·
                refine ⟨6952027209044066571690769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9269369612058755428921025 6952027209044066571690769)
                ·
                  refine ⟨5214020406783049928768077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6952027209044066571690769 5214020406783049928768077)
                  ·
                    refine ⟨1955257652543643723288029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5214020406783049928768077 1955257652543643723288029)
                    ·
                      refine ⟨733221619703866396233011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1955257652543643723288029 733221619703866396233011)
                      ·
                        rfl

theorem cell23_1427944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_1427944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427944 prefixEnd_1427944 := by exact prefixLift 1427944
  have htrace : WordTrace (prefixWord ++ tailWord_1427944) baseStart_1427944 baseEnd_1427944 := by
    simpa [prefixWord, tailWord_1427944, baseEnd_1427944] using wordTrace_append hprefix tailTrace_1427944
  have hstable : (prefixWord ++ tailWord_1427944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427944).length < 2 ^ (prefixWord ++ tailWord_1427944).sum := by decide
  have hdescent : baseEnd_1427944 < baseStart_1427944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427947 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 4, 5]
def baseStart_1427947 : Nat := 118140960795 + 1427947 * 2 ^ 59
def prefixEnd_1427947 : Nat := 4983230072969 + 3 ^ 40 * 1427947 * 2
def baseEnd_1427947 : Nat := 244407720048609961498499

theorem tailTrace_1427947 : CollatzResearch.WordTrace tailWord_1427947 prefixEnd_1427947 244407720048609961498499 := by
  unfold tailWord_1427947
  simp only [CollatzResearch.WordTrace]
  refine ⟨52081505757799367776914095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34721003838532911851276063 52081505757799367776914095)
  ·
    refine ⟨78122258636699051665371143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52081505757799367776914095 78122258636699051665371143)
    ·
      refine ⟨117183387955048577498056715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78122258636699051665371143 117183387955048577498056715)
      ·
        refine ⟨175775081932572866247085073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117183387955048577498056715 175775081932572866247085073)
        ·
          refine ⟨131831311449429649685313805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175775081932572866247085073 131831311449429649685313805)
          ·
            refine ⟨49436741793536118631992677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131831311449429649685313805 49436741793536118631992677)
            ·
              refine ⟨9269389086288022243498627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49436741793536118631992677 9269389086288022243498627)
              ·
                refine ⟨13904083629432033365247941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9269389086288022243498627 13904083629432033365247941)
                ·
                  refine ⟨2607015680518506255983989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13904083629432033365247941 2607015680518506255983989)
                  ·
                    refine ⟨244407720048609961498499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2607015680518506255983989 244407720048609961498499)
                    ·
                      rfl

theorem cell23_1427947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 5].length) (baseStart_1427947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427947 prefixEnd_1427947 := by exact prefixLift 1427947
  have htrace : WordTrace (prefixWord ++ tailWord_1427947) baseStart_1427947 baseEnd_1427947 := by
    simpa [prefixWord, tailWord_1427947, baseEnd_1427947] using wordTrace_append hprefix tailTrace_1427947
  have hstable : (prefixWord ++ tailWord_1427947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427947).length < 2 ^ (prefixWord ++ tailWord_1427947).sum := by decide
  have hdescent : baseEnd_1427947 < baseStart_1427947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427967 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_1427967 : Nat := 118140960795 + 1427967 * 2 ^ 59
def prefixEnd_1427967 : Nat := 4983230072969 + 3 ^ 40 * 1427967 * 2
def baseEnd_1427967 : Nat := 733233429758919806245405

theorem tailTrace_1427967 : CollatzResearch.WordTrace tailWord_1427967 prefixEnd_1427967 733233429758919806245405 := by
  unfold tailWord_1427967
  simp only [CollatzResearch.WordTrace]
  refine ⟨52082235217726911192642155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34721490145151274128428103 52082235217726911192642155)
  ·
    refine ⟨78123352826590366788963233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52082235217726911192642155 78123352826590366788963233)
    ·
      refine ⟨58592514619942775091722425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78123352826590366788963233 58592514619942775091722425)
      ·
        refine ⟨43944385964957081318791819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58592514619942775091722425 43944385964957081318791819)
        ·
          refine ⟨65916578947435621978187729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43944385964957081318791819 65916578947435621978187729)
          ·
            refine ⟨49437434210576716483640797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65916578947435621978187729 49437434210576716483640797)
            ·
              refine ⟨18539037828966268681365299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49437434210576716483640797 18539037828966268681365299)
              ·
                refine ⟨27808556743449403022047949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18539037828966268681365299 27808556743449403022047949)
                ·
                  refine ⟨10428208778793526133267981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27808556743449403022047949 10428208778793526133267981)
                  ·
                    refine ⟨3910578292047572299975493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10428208778793526133267981 3910578292047572299975493)
                    ·
                      refine ⟨733233429758919806245405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3910578292047572299975493 733233429758919806245405)
                      ·
                        rfl

theorem cell23_1427967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_1427967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427967 prefixEnd_1427967 := by exact prefixLift 1427967
  have htrace : WordTrace (prefixWord ++ tailWord_1427967) baseStart_1427967 baseEnd_1427967 := by
    simpa [prefixWord, tailWord_1427967, baseEnd_1427967] using wordTrace_append hprefix tailTrace_1427967
  have hstable : (prefixWord ++ tailWord_1427967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427967).length < 2 ^ (prefixWord ++ tailWord_1427967).sum := by decide
  have hdescent : baseEnd_1427967 < baseStart_1427967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427994 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_1427994 : Nat := 118140960795 + 1427994 * 2 ^ 59
def prefixEnd_1427994 : Nat := 4983230072969 + 3 ^ 40 * 1427994 * 2
def baseEnd_1427994 : Nat := 244415764578863733535927

theorem tailTrace_1427994 : CollatzResearch.WordTrace tailWord_1427994 prefixEnd_1427994 244415764578863733535927 := by
  unfold tailWord_1427994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13020804997157273700968759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34722146659086063202583357 13020804997157273700968759)
  ·
    refine ⟨19531207495735910551453139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13020804997157273700968759 19531207495735910551453139)
    ·
      refine ⟨29296811243603865827179709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19531207495735910551453139 29296811243603865827179709)
      ·
        refine ⟨10986304216351449685192391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29296811243603865827179709 10986304216351449685192391)
        ·
          refine ⟨16479456324527174527788587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10986304216351449685192391 16479456324527174527788587)
          ·
            refine ⟨24719184486790761791682881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16479456324527174527788587 24719184486790761791682881)
            ·
              refine ⟨18539388365093071343762161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24719184486790761791682881 18539388365093071343762161)
              ·
                refine ⟨13904541273819803507821621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18539388365093071343762161 13904541273819803507821621)
                ·
                  refine ⟨1303550744420606578858277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13904541273819803507821621 1303550744420606578858277)
                  ·
                    refine ⟨244415764578863733535927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1303550744420606578858277 244415764578863733535927)
                    ·
                      rfl

theorem cell23_1427994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_1427994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1427994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1427994 prefixEnd_1427994 := by exact prefixLift 1427994
  have htrace : WordTrace (prefixWord ++ tailWord_1427994) baseStart_1427994 baseEnd_1427994 := by
    simpa [prefixWord, tailWord_1427994, baseEnd_1427994] using wordTrace_append hprefix tailTrace_1427994
  have hstable : (prefixWord ++ tailWord_1427994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427994).length < 2 ^ (prefixWord ++ tailWord_1427994).sum := by decide
  have hdescent : baseEnd_1427994 < baseStart_1427994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428011 : List Nat := [1, 1, 1, 1, 2, 1, 3, 8, 1, 4]
def baseStart_1428011 : Nat := 118140960795 + 1428011 * 2 ^ 59
def prefixEnd_1428011 : Nat := 4983230072969 + 3 ^ 40 * 1428011 * 2
def baseEnd_1428011 : Nat := 244418674302572544698401

theorem tailTrace_1428011 : CollatzResearch.WordTrace tailWord_1428011 prefixEnd_1428011 244418674302572544698401 := by
  unfold tailWord_1428011
  simp only [CollatzResearch.WordTrace]
  refine ⟨52083840029567506707243887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34722560019711671138162591 52083840029567506707243887)
  ·
    refine ⟨78125760044351260060865831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52083840029567506707243887 78125760044351260060865831)
    ·
      refine ⟨117188640066526890091298747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78125760044351260060865831 117188640066526890091298747)
      ·
        refine ⟨175782960099790335136948121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117188640066526890091298747 175782960099790335136948121)
        ·
          refine ⟨131837220074842751352711091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175782960099790335136948121 131837220074842751352711091)
          ·
            refine ⟨197755830112264127029066637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131837220074842751352711091 197755830112264127029066637)
            ·
              refine ⟨74158436292099047635899989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197755830112264127029066637 74158436292099047635899989)
              ·
                refine ⟨869044175298035714483203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 74158436292099047635899989 869044175298035714483203)
                ·
                  refine ⟨1303566262947053571724805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869044175298035714483203 1303566262947053571724805)
                  ·
                    refine ⟨244418674302572544698401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1303566262947053571724805 244418674302572544698401)
                    ·
                      rfl

theorem cell23_1428011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 1, 4].length) (baseStart_1428011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428011 prefixEnd_1428011 := by exact prefixLift 1428011
  have htrace : WordTrace (prefixWord ++ tailWord_1428011) baseStart_1428011 baseEnd_1428011 := by
    simpa [prefixWord, tailWord_1428011, baseEnd_1428011] using wordTrace_append hprefix tailTrace_1428011
  have hstable : (prefixWord ++ tailWord_1428011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428011).length < 2 ^ (prefixWord ++ tailWord_1428011).sum := by decide
  have hdescent : baseEnd_1428011 < baseStart_1428011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428013 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1428013 : Nat := 118140960795 + 1428013 * 2 ^ 59
def prefixEnd_1428013 : Nat := 4983230072969 + 3 ^ 40 * 1428013 * 2
def baseEnd_1428013 : Nat := 733257049869026626270195

theorem tailTrace_1428013 : CollatzResearch.WordTrace tailWord_1428013 prefixEnd_1428013 733257049869026626270195 := by
  unfold tailWord_1428013
  simp only [CollatzResearch.WordTrace]
  refine ⟨52083912975560261048816693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34722608650373507365877795 52083912975560261048816693)
  ·
    refine ⟨4882866841458774473326565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52083912975560261048816693 4882866841458774473326565)
    ·
      refine ⟨915537532773520213748731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4882866841458774473326565 915537532773520213748731)
      ·
        refine ⟨1373306299160280320623097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915537532773520213748731 1373306299160280320623097)
        ·
          refine ⟨1029979724370210240467323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1373306299160280320623097 1029979724370210240467323)
          ·
            refine ⟨1544969586555315360700985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029979724370210240467323 1544969586555315360700985)
            ·
              refine ⟨1158727189916486520525739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1544969586555315360700985 1158727189916486520525739)
              ·
                refine ⟨1738090784874729780788609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158727189916486520525739 1738090784874729780788609)
                ·
                  refine ⟨1303568088656047335591457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1738090784874729780788609 1303568088656047335591457)
                  ·
                    refine ⟨977676066492035501693593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1303568088656047335591457 977676066492035501693593)
                    ·
                      refine ⟨733257049869026626270195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977676066492035501693593 733257049869026626270195)
                      ·
                        rfl

theorem cell23_1428013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1428013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428013 prefixEnd_1428013 := by exact prefixLift 1428013
  have htrace : WordTrace (prefixWord ++ tailWord_1428013) baseStart_1428013 baseEnd_1428013 := by
    simpa [prefixWord, tailWord_1428013, baseEnd_1428013] using wordTrace_append hprefix tailTrace_1428013
  have hstable : (prefixWord ++ tailWord_1428013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428013).length < 2 ^ (prefixWord ++ tailWord_1428013).sum := by decide
  have hdescent : baseEnd_1428013 < baseStart_1428013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428024 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 6]
def baseStart_1428024 : Nat := 118140960795 + 1428024 * 2 ^ 59
def prefixEnd_1428024 : Nat := 4983230072969 + 3 ^ 40 * 1428024 * 2
def baseEnd_1428024 : Nat := 81473633128469564803627

theorem tailTrace_1428024 : CollatzResearch.WordTrace tailWord_1428024 prefixEnd_1428024 81473633128469564803627 := by
  unfold tailWord_1428024
  simp only [CollatzResearch.WordTrace]
  refine ⟨26042157089260204963733563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34722876119013606618311417 26042157089260204963733563)
  ·
    refine ⟨39063235633890307445600345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26042157089260204963733563 39063235633890307445600345)
    ·
      refine ⟨29297426725417730584200259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39063235633890307445600345 29297426725417730584200259)
      ·
        refine ⟨43946140088126595876300389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29297426725417730584200259 43946140088126595876300389)
        ·
          refine ⟨8239901266523736726806323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43946140088126595876300389 8239901266523736726806323)
          ·
            refine ⟨12359851899785605090209485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8239901266523736726806323 12359851899785605090209485)
            ·
              refine ⟨4634944462419601908828557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12359851899785605090209485 4634944462419601908828557)
              ·
                refine ⟨1738104173407350715810709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4634944462419601908828557 1738104173407350715810709)
                ·
                  refine ⟨81473633128469564803627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1738104173407350715810709 81473633128469564803627)
                  ·
                    rfl

theorem cell23_1428024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 6].length) (baseStart_1428024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428024 prefixEnd_1428024 := by exact prefixLift 1428024
  have htrace : WordTrace (prefixWord ++ tailWord_1428024) baseStart_1428024 baseEnd_1428024 := by
    simpa [prefixWord, tailWord_1428024, baseEnd_1428024] using wordTrace_append hprefix tailTrace_1428024
  have hstable : (prefixWord ++ tailWord_1428024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428024).length < 2 ^ (prefixWord ++ tailWord_1428024).sum := by decide
  have hdescent : baseEnd_1428024 < baseStart_1428024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428085 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1428085 : Nat := 118140960795 + 1428085 * 2 ^ 59
def prefixEnd_1428085 : Nat := 4983230072969 + 3 ^ 40 * 1428085 * 2
def baseEnd_1428085 : Nat := 733294020476150344569863

theorem tailTrace_1428085 : CollatzResearch.WordTrace tailWord_1428085 prefixEnd_1428085 733294020476150344569863 := by
  unfold tailWord_1428085
  simp only [CollatzResearch.WordTrace]
  refine ⟨52086539031299417345437709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34724359354199611563625139 52086539031299417345437709)
  ·
    refine ⟨19532452136737281504539141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52086539031299417345437709 19532452136737281504539141)
    ·
      refine ⟨3662334775638240282101089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19532452136737281504539141 3662334775638240282101089)
      ·
        refine ⟨2746751081728680211575817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3662334775638240282101089 2746751081728680211575817)
        ·
          refine ⟨2060063311296510158681863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2746751081728680211575817 2060063311296510158681863)
          ·
            refine ⟨3090094966944765238022795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060063311296510158681863 3090094966944765238022795)
            ·
              refine ⟨4635142450417147857034193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3090094966944765238022795 4635142450417147857034193)
              ·
                refine ⟨3476356837812860892775645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4635142450417147857034193 3476356837812860892775645)
                ·
                  refine ⟨1303633814179822834790867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3476356837812860892775645 1303633814179822834790867)
                  ·
                    refine ⟨1955450721269734252186301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1303633814179822834790867 1955450721269734252186301)
                    ·
                      refine ⟨733294020476150344569863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1955450721269734252186301 733294020476150344569863)
                      ·
                        rfl

theorem cell23_1428085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1428085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428085 prefixEnd_1428085 := by exact prefixLift 1428085
  have htrace : WordTrace (prefixWord ++ tailWord_1428085) baseStart_1428085 baseEnd_1428085 := by
    simpa [prefixWord, tailWord_1428085, baseEnd_1428085] using wordTrace_append hprefix tailTrace_1428085
  have hstable : (prefixWord ++ tailWord_1428085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428085).length < 2 ^ (prefixWord ++ tailWord_1428085).sum := by decide
  have hdescent : baseEnd_1428085 < baseStart_1428085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428111 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 1, 2, 3]
def baseStart_1428111 : Nat := 118140960795 + 1428111 * 2 ^ 59
def prefixEnd_1428111 : Nat := 4983230072969 + 3 ^ 40 * 1428111 * 2
def baseEnd_1428111 : Nat := 733307370973167242844743

theorem tailTrace_1428111 : CollatzResearch.WordTrace tailWord_1428111 prefixEnd_1428111 733307370973167242844743 := by
  unfold tailWord_1428111
  simp only [CollatzResearch.WordTrace]
  refine ⟨52087487329205223785884187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34724991552803482523922791 52087487329205223785884187)
  ·
    refine ⟨78131230993807835678826281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52087487329205223785884187 78131230993807835678826281)
    ·
      refine ⟨58598423245355876759119711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78131230993807835678826281 58598423245355876759119711)
      ·
        refine ⟨87897634868033815138679567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58598423245355876759119711 87897634868033815138679567)
        ·
          refine ⟨131846452302050722708019351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87897634868033815138679567 131846452302050722708019351)
          ·
            refine ⟨197769678453076084062029027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131846452302050722708019351 197769678453076084062029027)
            ·
              refine ⟨296654517679614126093043541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197769678453076084062029027 296654517679614126093043541)
              ·
                refine ⟨1738210064528989020076427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 296654517679614126093043541 1738210064528989020076427)
                ·
                  refine ⟨2607315096793483530114641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1738210064528989020076427 2607315096793483530114641)
                  ·
                    refine ⟨1955486322595112647585981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2607315096793483530114641 1955486322595112647585981)
                    ·
                      refine ⟨733307370973167242844743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1955486322595112647585981 733307370973167242844743)
                      ·
                        rfl

theorem cell23_1428111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 2, 3].length) (baseStart_1428111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428111 prefixEnd_1428111 := by exact prefixLift 1428111
  have htrace : WordTrace (prefixWord ++ tailWord_1428111) baseStart_1428111 baseEnd_1428111 := by
    simpa [prefixWord, tailWord_1428111, baseEnd_1428111] using wordTrace_append hprefix tailTrace_1428111
  have hstable : (prefixWord ++ tailWord_1428111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428111).length < 2 ^ (prefixWord ++ tailWord_1428111).sum := by decide
  have hdescent : baseEnd_1428111 < baseStart_1428111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428135 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1428135 : Nat := 118140960795 + 1428135 * 2 ^ 59
def prefixEnd_1428135 : Nat := 4983230072969 + 3 ^ 40 * 1428135 * 2
def baseEnd_1428135 : Nat := 244439898169625049648211

theorem tailTrace_1428135 : CollatzResearch.WordTrace tailWord_1428135 prefixEnd_1428135 244439898169625049648211 := by
  unfold tailWord_1428135
  simp only [CollatzResearch.WordTrace]
  refine ⟨52088362681118275884757859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34725575120745517256505239 52088362681118275884757859)
  ·
    refine ⟨78132544021677413827136789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52088362681118275884757859 78132544021677413827136789)
    ·
      refine ⟨3662463001016128773147037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78132544021677413827136789 3662463001016128773147037)
      ·
        refine ⟨1373423625381048289930139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3662463001016128773147037 1373423625381048289930139)
        ·
          refine ⟨2060135438071572434895209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373423625381048289930139 2060135438071572434895209)
          ·
            refine ⟨1545101578553679326171407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2060135438071572434895209 1545101578553679326171407)
            ·
              refine ⟨2317652367830518989257111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545101578553679326171407 2317652367830518989257111)
              ·
                refine ⟨3476478551745778483885667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317652367830518989257111 3476478551745778483885667)
                ·
                  refine ⟨5214717827618667725828501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476478551745778483885667 5214717827618667725828501)
                  ·
                    refine ⟨244439898169625049648211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5214717827618667725828501 244439898169625049648211)
                    ·
                      rfl

theorem cell23_1428135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1428135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428135 prefixEnd_1428135 := by exact prefixLift 1428135
  have htrace : WordTrace (prefixWord ++ tailWord_1428135) baseStart_1428135 baseEnd_1428135 := by
    simpa [prefixWord, tailWord_1428135, baseEnd_1428135] using wordTrace_append hprefix tailTrace_1428135
  have hstable : (prefixWord ++ tailWord_1428135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428135).length < 2 ^ (prefixWord ++ tailWord_1428135).sum := by decide
  have hdescent : baseEnd_1428135 < baseStart_1428135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428142 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_1428142 : Nat := 118140960795 + 1428142 * 2 ^ 59
def prefixEnd_1428142 : Nat := 4983230072969 + 3 ^ 40 * 1428142 * 2
def baseEnd_1428142 : Nat := 733323288873456621557101

theorem tailTrace_1428142 : CollatzResearch.WordTrace tailWord_1428142 prefixEnd_1428142 733323288873456621557101 := by
  unfold tailWord_1428142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511077249011614510032835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34725745328061944053508453 6511077249011614510032835)
  ·
    refine ⟨9766615873517421765049253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6511077249011614510032835 9766615873517421765049253)
    ·
      refine ⟨1831240476284516580946735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9766615873517421765049253 1831240476284516580946735)
      ·
        refine ⟨2746860714426774871420103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831240476284516580946735 2746860714426774871420103)
        ·
          refine ⟨4120291071640162307130155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2746860714426774871420103 4120291071640162307130155)
          ·
            refine ⟨6180436607460243460695233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4120291071640162307130155 6180436607460243460695233)
            ·
              refine ⟨4635327455595182595521425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6180436607460243460695233 4635327455595182595521425)
              ·
                refine ⟨3476495591696386946641069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4635327455595182595521425 3476495591696386946641069)
                ·
                  refine ⟨1303685846886145104990401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3476495591696386946641069 1303685846886145104990401)
                  ·
                    refine ⟨977764385164608828742801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1303685846886145104990401 977764385164608828742801)
                    ·
                      refine ⟨733323288873456621557101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977764385164608828742801 733323288873456621557101)
                      ·
                        rfl

theorem cell23_1428142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_1428142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428142 prefixEnd_1428142 := by exact prefixLift 1428142
  have htrace : WordTrace (prefixWord ++ tailWord_1428142) baseStart_1428142 baseEnd_1428142 := by
    simpa [prefixWord, tailWord_1428142, baseEnd_1428142] using wordTrace_append hprefix tailTrace_1428142
  have hstable : (prefixWord ++ tailWord_1428142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428142).length < 2 ^ (prefixWord ++ tailWord_1428142).sum := by decide
  have hdescent : baseEnd_1428142 < baseStart_1428142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428154 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_1428154 : Nat := 118140960795 + 1428154 * 2 ^ 59
def prefixEnd_1428154 : Nat := 4983230072969 + 3 ^ 40 * 1428154 * 2
def baseEnd_1428154 : Nat := 733329450641310574607045

theorem tailTrace_1428154 : CollatzResearch.WordTrace tailWord_1428154 prefixEnd_1428154 733329450641310574607045 := by
  unfold tailWord_1428154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13022263917012360532424879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34726037112032961419799677 13022263917012360532424879)
  ·
    refine ⟨19533395875518540798637319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13022263917012360532424879 19533395875518540798637319)
    ·
      refine ⟨29300093813277811197955979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19533395875518540798637319 29300093813277811197955979)
      ·
        refine ⟨43950140719916716796933969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29300093813277811197955979 43950140719916716796933969)
        ·
          refine ⟨32962605539937537597700477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43950140719916716796933969 32962605539937537597700477)
          ·
            refine ⟨12360977077476576599137679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32962605539937537597700477 12360977077476576599137679)
            ·
              refine ⟨18541465616214864898706519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360977077476576599137679 18541465616214864898706519)
              ·
                refine ⟨27812198424322297348059779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18541465616214864898706519 27812198424322297348059779)
                ·
                  refine ⟨41718297636483446022089669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27812198424322297348059779 41718297636483446022089669)
                  ·
                    refine ⟨7822180806840646129141813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41718297636483446022089669 7822180806840646129141813)
                    ·
                      refine ⟨733329450641310574607045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7822180806840646129141813 733329450641310574607045)
                      ·
                        rfl

theorem cell23_1428154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_1428154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428154 prefixEnd_1428154 := by exact prefixLift 1428154
  have htrace : WordTrace (prefixWord ++ tailWord_1428154) baseStart_1428154 baseEnd_1428154 := by
    simpa [prefixWord, tailWord_1428154, baseEnd_1428154] using wordTrace_append hprefix tailTrace_1428154
  have hstable : (prefixWord ++ tailWord_1428154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428154).length < 2 ^ (prefixWord ++ tailWord_1428154).sum := by decide
  have hdescent : baseEnd_1428154 < baseStart_1428154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428158 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_1428158 : Nat := 118140960795 + 1428158 * 2 ^ 59
def prefixEnd_1428158 : Nat := 4983230072969 + 3 ^ 40 * 1428158 * 2
def baseEnd_1428158 : Nat := 733331504563928558957027

theorem tailTrace_1428158 : CollatzResearch.WordTrace tailWord_1428158 prefixEnd_1428158 733331504563928558957027 := by
  unfold tailWord_1428158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511150195004368851605641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34726134373356633875230085 6511150195004368851605641)
  ·
    refine ⟨4883362646253276638704231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6511150195004368851605641 4883362646253276638704231)
    ·
      refine ⟨7325043969379914958056347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4883362646253276638704231 7325043969379914958056347)
      ·
        refine ⟨10987565954069872437084521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7325043969379914958056347 10987565954069872437084521)
        ·
          refine ⟨8240674465552404327813391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10987565954069872437084521 8240674465552404327813391)
          ·
            refine ⟨12361011698328606491720087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8240674465552404327813391 12361011698328606491720087)
            ·
              refine ⟨18541517547492909737580131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12361011698328606491720087 18541517547492909737580131)
              ·
                refine ⟨27812276321239364606370197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18541517547492909737580131 27812276321239364606370197)
                ·
                  refine ⟨1303700452558095215923603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27812276321239364606370197 1303700452558095215923603)
                  ·
                    refine ⟨1955550678837142823885405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1303700452558095215923603 1955550678837142823885405)
                    ·
                      refine ⟨733331504563928558957027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1955550678837142823885405 733331504563928558957027)
                      ·
                        rfl

theorem cell23_1428158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_1428158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428158 prefixEnd_1428158 := by exact prefixLift 1428158
  have htrace : WordTrace (prefixWord ++ tailWord_1428158) baseStart_1428158 baseEnd_1428158 := by
    simpa [prefixWord, tailWord_1428158, baseEnd_1428158] using wordTrace_append hprefix tailTrace_1428158
  have hstable : (prefixWord ++ tailWord_1428158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428158).length < 2 ^ (prefixWord ++ tailWord_1428158).sum := by decide
  have hdescent : baseEnd_1428158 < baseStart_1428158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428204 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 9]
def baseStart_1428204 : Nat := 118140960795 + 1428204 * 2 ^ 59
def prefixEnd_1428204 : Nat := 4983230072969 + 3 ^ 40 * 1428204 * 2
def baseEnd_1428204 : Nat := 81483902741559486553535

theorem tailTrace_1428204 : CollatzResearch.WordTrace tailWord_1428204 prefixEnd_1428204 81483902741559486553535 := by
  unfold tailWord_1428204
  simp only [CollatzResearch.WordTrace]
  refine ⟨26045439658934150334509833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34727252878578867112679777 26045439658934150334509833)
  ·
    refine ⟨19534079744200612750882375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26045439658934150334509833 19534079744200612750882375)
    ·
      refine ⟨29301119616300919126323563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19534079744200612750882375 29301119616300919126323563)
      ·
        refine ⟨43951679424451378689485345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29301119616300919126323563 43951679424451378689485345)
        ·
          refine ⟨32963759568338534017114009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43951679424451378689485345 32963759568338534017114009)
          ·
            refine ⟨24722819676253900512835507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32963759568338534017114009 24722819676253900512835507)
            ·
              refine ⟨37084229514380850769253261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24722819676253900512835507 37084229514380850769253261)
              ·
                refine ⟨13906586067892819038469973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37084229514380850769253261 13906586067892819038469973)
                ·
                  refine ⟨81483902741559486553535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13906586067892819038469973 81483902741559486553535)
                  ·
                    rfl

theorem cell23_1428204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_1428204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428204 prefixEnd_1428204 := by exact prefixLift 1428204
  have htrace : WordTrace (prefixWord ++ tailWord_1428204) baseStart_1428204 baseEnd_1428204 := by
    simpa [prefixWord, tailWord_1428204, baseEnd_1428204] using wordTrace_append hprefix tailTrace_1428204
  have hstable : (prefixWord ++ tailWord_1428204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428204).length < 2 ^ (prefixWord ++ tailWord_1428204).sum := by decide
  have hdescent : baseEnd_1428204 < baseStart_1428204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428224 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_1428224 : Nat := 118140960795 + 1428224 * 2 ^ 59
def prefixEnd_1428224 : Nat := 4983230072969 + 3 ^ 40 * 1428224 * 2
def baseEnd_1428224 : Nat := 733365394287125300731723

theorem tailTrace_1428224 : CollatzResearch.WordTrace tailWord_1428224 prefixEnd_1428224 733365394287125300731723 := by
  unfold tailWord_1428224
  simp only [CollatzResearch.WordTrace]
  refine ⟨26045804388897922042373863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34727739185197229389831817 26045804388897922042373863)
  ·
    refine ⟨39068706583346883063560795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26045804388897922042373863 39068706583346883063560795)
    ·
      refine ⟨58603059875020324595341193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39068706583346883063560795 58603059875020324595341193)
      ·
        refine ⟨43952294906265243446505895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58603059875020324595341193 43952294906265243446505895)
        ·
          refine ⟨65928442359397865169758843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43952294906265243446505895 65928442359397865169758843)
          ·
            refine ⟨98892663539096797754638265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65928442359397865169758843 98892663539096797754638265)
            ·
              refine ⟨74169497654322598315978699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98892663539096797754638265 74169497654322598315978699)
              ·
                refine ⟨111254246481483897473968049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74169497654322598315978699 111254246481483897473968049)
                ·
                  refine ⟨83440684861112923105476037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111254246481483897473968049 83440684861112923105476037)
                  ·
                    refine ⟨15645128411458673082276757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83440684861112923105476037 15645128411458673082276757)
                    ·
                      refine ⟨733365394287125300731723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15645128411458673082276757 733365394287125300731723)
                      ·
                        rfl

theorem cell23_1428224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_1428224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428224 prefixEnd_1428224 := by exact prefixLift 1428224
  have htrace : WordTrace (prefixWord ++ tailWord_1428224) baseStart_1428224 baseEnd_1428224 := by
    simpa [prefixWord, tailWord_1428224, baseEnd_1428224] using wordTrace_append hprefix tailTrace_1428224
  have hstable : (prefixWord ++ tailWord_1428224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428224).length < 2 ^ (prefixWord ++ tailWord_1428224).sum := by decide
  have hdescent : baseEnd_1428224 < baseStart_1428224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428232 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 2, 2, 2]
def baseStart_1428232 : Nat := 118140960795 + 1428232 * 2 ^ 59
def prefixEnd_1428232 : Nat := 4983230072969 + 3 ^ 40 * 1428232 * 2
def baseEnd_1428232 : Nat := 733369502132361269431687

theorem tailTrace_1428232 : CollatzResearch.WordTrace tailWord_1428232 prefixEnd_1428232 733369502132361269431687 := by
  unfold tailWord_1428232
  simp only [CollatzResearch.WordTrace]
  refine ⟨26045950280883430725519475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34727933707844574300692633 26045950280883430725519475)
  ·
    refine ⟨39068925421325146088279213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26045950280883430725519475 39068925421325146088279213)
    ·
      refine ⟨14650847032996929783104705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39068925421325146088279213 14650847032996929783104705)
      ·
        refine ⟨10988135274747697337328529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14650847032996929783104705 10988135274747697337328529)
        ·
          refine ⟨8241101456060773002996397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10988135274747697337328529 8241101456060773002996397)
          ·
            refine ⟨3090413046022789876123649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8241101456060773002996397 3090413046022789876123649)
            ·
              refine ⟨2317809784517092407092737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090413046022789876123649 2317809784517092407092737)
              ·
                refine ⟨1738357338387819305319553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317809784517092407092737 1738357338387819305319553)
                ·
                  refine ⟨1303768003790864478989665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1738357338387819305319553 1303768003790864478989665)
                  ·
                    refine ⟨977826002843148359242249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1303768003790864478989665 977826002843148359242249)
                    ·
                      refine ⟨733369502132361269431687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977826002843148359242249 733369502132361269431687)
                      ·
                        rfl

theorem cell23_1428232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_1428232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428232 prefixEnd_1428232 := by exact prefixLift 1428232
  have htrace : WordTrace (prefixWord ++ tailWord_1428232) baseStart_1428232 baseEnd_1428232 := by
    simpa [prefixWord, tailWord_1428232, baseEnd_1428232] using wordTrace_append hprefix tailTrace_1428232
  have hstable : (prefixWord ++ tailWord_1428232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428232).length < 2 ^ (prefixWord ++ tailWord_1428232).sum := by decide
  have hdescent : baseEnd_1428232 < baseStart_1428232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428342 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1428342 : Nat := 118140960795 + 1428342 * 2 ^ 59
def prefixEnd_1428342 : Nat := 4983230072969 + 3 ^ 40 * 1428342 * 2
def baseEnd_1428342 : Nat := 733425985004355839056181

theorem tailTrace_1428342 : CollatzResearch.WordTrace tailWord_1428342 prefixEnd_1428342 733425985004355839056181 := by
  unfold tailWord_1428342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3255994536960521889846455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34730608394245566825028853 3255994536960521889846455)
  ·
    refine ⟨4883991805440782834769683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3255994536960521889846455 4883991805440782834769683)
    ·
      refine ⟨7325987708161174252154525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4883991805440782834769683 7325987708161174252154525)
      ·
        refine ⟨2747245390560440344557947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7325987708161174252154525 2747245390560440344557947)
        ·
          refine ⟨4120868085840660516836921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747245390560440344557947 4120868085840660516836921)
          ·
            refine ⟨3090651064380495387627691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4120868085840660516836921 3090651064380495387627691)
            ·
              refine ⟨4635976596570743081441537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3090651064380495387627691 4635976596570743081441537)
              ·
                refine ⟨3476982447428057311081153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4635976596570743081441537 3476982447428057311081153)
                ·
                  refine ⟨2607736835571042983310865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3476982447428057311081153 2607736835571042983310865)
                  ·
                    refine ⟨1955802626678282237483149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2607736835571042983310865 1955802626678282237483149)
                    ·
                      refine ⟨733425985004355839056181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1955802626678282237483149 733425985004355839056181)
                      ·
                        rfl

theorem cell23_1428342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1428342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428342 prefixEnd_1428342 := by exact prefixLift 1428342
  have htrace : WordTrace (prefixWord ++ tailWord_1428342) baseStart_1428342 baseEnd_1428342 := by
    simpa [prefixWord, tailWord_1428342, baseEnd_1428342] using wordTrace_append hprefix tailTrace_1428342
  have hstable : (prefixWord ++ tailWord_1428342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428342).length < 2 ^ (prefixWord ++ tailWord_1428342).sum := by decide
  have hdescent : baseEnd_1428342 < baseStart_1428342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428362 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 6]
def baseStart_1428362 : Nat := 118140960795 + 1428362 * 2 ^ 59
def prefixEnd_1428362 : Nat := 4983230072969 + 3 ^ 40 * 1428362 * 2
def baseEnd_1428362 : Nat := 81492917179716195645121

theorem tailTrace_1428362 : CollatzResearch.WordTrace tailWord_1428362 prefixEnd_1428362 81492917179716195645121 := by
  unfold tailWord_1428362
  simp only [CollatzResearch.WordTrace]
  refine ⟨13024160512823973413317835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34731094700863929102180893 13024160512823973413317835)
  ·
    refine ⟨19536240769235960119976753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13024160512823973413317835 19536240769235960119976753)
    ·
      refine ⟨14652180576926970089982565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19536240769235960119976753 14652180576926970089982565)
      ·
        refine ⟨2747283858173806891871731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14652180576926970089982565 2747283858173806891871731)
        ·
          refine ⟨4120925787260710337807597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747283858173806891871731 4120925787260710337807597)
          ·
            refine ⟨1545347170222766376677849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4120925787260710337807597 1545347170222766376677849)
            ·
              refine ⟨1159010377667074782508387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1545347170222766376677849 1159010377667074782508387)
              ·
                refine ⟨1738515566500612173762581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159010377667074782508387 1738515566500612173762581)
                ·
                  refine ⟨81492917179716195645121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1738515566500612173762581 81492917179716195645121)
                  ·
                    rfl

theorem cell23_1428362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_1428362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428362 prefixEnd_1428362 := by exact prefixLift 1428362
  have htrace : WordTrace (prefixWord ++ tailWord_1428362) baseStart_1428362 baseEnd_1428362 := by
    simpa [prefixWord, tailWord_1428362, baseEnd_1428362] using wordTrace_append hprefix tailTrace_1428362
  have hstable : (prefixWord ++ tailWord_1428362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428362).length < 2 ^ (prefixWord ++ tailWord_1428362).sum := by decide
  have hdescent : baseEnd_1428362 < baseStart_1428362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428388 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_1428388 : Nat := 118140960795 + 1428388 * 2 ^ 59
def prefixEnd_1428388 : Nat := 4983230072969 + 3 ^ 40 * 1428388 * 2
def baseEnd_1428388 : Nat := 244483201704820886360323

theorem tailTrace_1428388 : CollatzResearch.WordTrace tailWord_1428388 prefixEnd_1428388 244483201704820886360323 := by
  unfold tailWord_1428388
  simp only [CollatzResearch.WordTrace]
  refine ⟨26048795174600850046858909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34731726899467800062478545 26048795174600850046858909)
  ·
    refine ⟨9768298190475318767572091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26048795174600850046858909 9768298190475318767572091)
    ·
      refine ⟨14652447285712978151358137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9768298190475318767572091 14652447285712978151358137)
      ·
        refine ⟨10989335464284733613518603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14652447285712978151358137 10989335464284733613518603)
        ·
          refine ⟨16484003196427100420277905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10989335464284733613518603 16484003196427100420277905)
          ·
            refine ⟨12363002397320325315208429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16484003196427100420277905 12363002397320325315208429)
            ·
              refine ⟨4636125898995121993203161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12363002397320325315208429 4636125898995121993203161)
              ·
                refine ⟨3477094424246341494902371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4636125898995121993203161 3477094424246341494902371)
                ·
                  refine ⟨5215641636369512242353557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477094424246341494902371 5215641636369512242353557)
                  ·
                    refine ⟨244483201704820886360323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5215641636369512242353557 244483201704820886360323)
                    ·
                      rfl

theorem cell23_1428388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_1428388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428388 prefixEnd_1428388 := by exact prefixLift 1428388
  have htrace : WordTrace (prefixWord ++ tailWord_1428388) baseStart_1428388 baseEnd_1428388 := by
    simpa [prefixWord, tailWord_1428388, baseEnd_1428388] using wordTrace_append hprefix tailTrace_1428388
  have hstable : (prefixWord ++ tailWord_1428388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428388).length < 2 ^ (prefixWord ++ tailWord_1428388).sum := by decide
  have hdescent : baseEnd_1428388 < baseStart_1428388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428395 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 5, 2, 2]
def baseStart_1428395 : Nat := 118140960795 + 1428395 * 2 ^ 59
def prefixEnd_1428395 : Nat := 4983230072969 + 3 ^ 40 * 1428395 * 2
def baseEnd_1428395 : Nat := 733453199479044131693437

theorem tailTrace_1428395 : CollatzResearch.WordTrace tailWord_1428395 prefixEnd_1428395 733453199479044131693437 := by
  unfold tailWord_1428395
  simp only [CollatzResearch.WordTrace]
  refine ⟨52097845660176340289222639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34731897106784226859481759 52097845660176340289222639)
  ·
    refine ⟨78146768490264510433833959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52097845660176340289222639 78146768490264510433833959)
    ·
      refine ⟨117220152735396765650750939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78146768490264510433833959 117220152735396765650750939)
      ·
        refine ⟨175830229103095148476126409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117220152735396765650750939 175830229103095148476126409)
        ·
          refine ⟨131872671827321361357094807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175830229103095148476126409 131872671827321361357094807)
          ·
            refine ⟨197809007740982042035642211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131872671827321361357094807 197809007740982042035642211)
            ·
              refine ⟨296713511611473063053463317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197809007740982042035642211 296713511611473063053463317)
              ·
                refine ⟨13908445856787799830631093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 296713511611473063053463317 13908445856787799830631093)
                ·
                  refine ⟨1303916799073856234121665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13908445856787799830631093 1303916799073856234121665)
                  ·
                    refine ⟨977937599305392175591249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1303916799073856234121665 977937599305392175591249)
                    ·
                      refine ⟨733453199479044131693437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 977937599305392175591249 733453199479044131693437)
                      ·
                        rfl

theorem cell23_1428395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 2, 2].length) (baseStart_1428395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428395 prefixEnd_1428395 := by exact prefixLift 1428395
  have htrace : WordTrace (prefixWord ++ tailWord_1428395) baseStart_1428395 baseEnd_1428395 := by
    simpa [prefixWord, tailWord_1428395, baseEnd_1428395] using wordTrace_append hprefix tailTrace_1428395
  have hstable : (prefixWord ++ tailWord_1428395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428395).length < 2 ^ (prefixWord ++ tailWord_1428395).sum := by decide
  have hdescent : baseEnd_1428395 < baseStart_1428395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428401 : List Nat := [1, 2, 2, 4, 14]
def baseStart_1428401 : Nat := 118140960795 + 1428401 * 2 ^ 59
def prefixEnd_1428401 : Nat := 4983230072969 + 3 ^ 40 * 1428401 * 2
def baseEnd_1428401 : Nat := 1006112867438917843921

theorem tailTrace_1428401 : CollatzResearch.WordTrace tailWord_1428401 prefixEnd_1428401 1006112867438917843921 := by
  unfold tailWord_1428401
  simp only [CollatzResearch.WordTrace]
  refine ⟨52098064498154603313941057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34732042998769735542627371 52098064498154603313941057)
  ·
    refine ⟨39073548373615952485455793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52098064498154603313941057 39073548373615952485455793)
    ·
      refine ⟨29305161280211964364091845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39073548373615952485455793 29305161280211964364091845)
      ·
        refine ⟨5494717740039743318267221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29305161280211964364091845 5494717740039743318267221)
        ·
          refine ⟨1006112867438917843921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 5494717740039743318267221 1006112867438917843921)
          ·
            rfl

theorem cell23_1428401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 14].length) (baseStart_1428401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428401 prefixEnd_1428401 := by exact prefixLift 1428401
  have htrace : WordTrace (prefixWord ++ tailWord_1428401) baseStart_1428401 baseEnd_1428401 := by
    simpa [prefixWord, tailWord_1428401, baseEnd_1428401] using wordTrace_append hprefix tailTrace_1428401
  have hstable : (prefixWord ++ tailWord_1428401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428401).length < 2 ^ (prefixWord ++ tailWord_1428401).sum := by decide
  have hdescent : baseEnd_1428401 < baseStart_1428401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428536 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 2, 2, 2]
def baseStart_1428536 : Nat := 118140960795 + 1428536 * 2 ^ 59
def prefixEnd_1428536 : Nat := 4983230072969 + 3 ^ 40 * 1428536 * 2
def baseEnd_1428536 : Nat := 733525600251328080030289

theorem tailTrace_1428536 : CollatzResearch.WordTrace tailWord_1428536 prefixEnd_1428536 733525600251328080030289 := by
  unfold tailWord_1428536
  simp only [CollatzResearch.WordTrace]
  refine ⟨26051494176332760685052731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34735325568443680913403641 26051494176332760685052731)
  ·
    refine ⟨39077241264499141027579097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26051494176332760685052731 39077241264499141027579097)
    ·
      refine ⟨29307930948374355770684323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39077241264499141027579097 29307930948374355770684323)
      ·
        refine ⟨43961896422561533656026485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29307930948374355770684323 43961896422561533656026485)
        ·
          refine ⟨4121427789615143780252483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43961896422561533656026485 4121427789615143780252483)
          ·
            refine ⟨6182141684422715670378725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121427789615143780252483 6182141684422715670378725)
            ·
              refine ⟨1159151565829259188196011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6182141684422715670378725 1159151565829259188196011)
              ·
                refine ⟨1738727348743888782294017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159151565829259188196011 1738727348743888782294017)
                ·
                  refine ⟨1304045511557916586720513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1738727348743888782294017 1304045511557916586720513)
                  ·
                    refine ⟨978034133668437440040385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1304045511557916586720513 978034133668437440040385)
                    ·
                      refine ⟨733525600251328080030289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978034133668437440040385 733525600251328080030289)
                      ·
                        rfl

theorem cell23_1428536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_1428536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428536 prefixEnd_1428536 := by exact prefixLift 1428536
  have htrace : WordTrace (prefixWord ++ tailWord_1428536) baseStart_1428536 baseEnd_1428536 := by
    simpa [prefixWord, tailWord_1428536, baseEnd_1428536] using wordTrace_append hprefix tailTrace_1428536
  have hstable : (prefixWord ++ tailWord_1428536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428536).length < 2 ^ (prefixWord ++ tailWord_1428536).sum := by decide
  have hdescent : baseEnd_1428536 < baseStart_1428536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428538 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_1428538 : Nat := 118140960795 + 1428538 * 2 ^ 59
def prefixEnd_1428538 : Nat := 4983230072969 + 3 ^ 40 * 1428538 * 2
def baseEnd_1428538 : Nat := 244508875737545690735093

theorem tailTrace_1428538 : CollatzResearch.WordTrace tailWord_1428538 prefixEnd_1428538 244508875737545690735093 := by
  unfold tailWord_1428538
  simp only [CollatzResearch.WordTrace]
  refine ⟨13025765324664568927919567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34735374199105517141118845 13025765324664568927919567)
  ·
    refine ⟨19538647986996853391879351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13025765324664568927919567 19538647986996853391879351)
    ·
      refine ⟨29307971980495280087819027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19538647986996853391879351 29307971980495280087819027)
      ·
        refine ⟨43961957970742920131728541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29307971980495280087819027 43961957970742920131728541)
        ·
          refine ⟨16485734239028595049398203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43961957970742920131728541 16485734239028595049398203)
          ·
            refine ⟨24728601358542892574097305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16485734239028595049398203 24728601358542892574097305)
            ·
              refine ⟨18546451018907169430572979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24728601358542892574097305 18546451018907169430572979)
              ·
                refine ⟨27819676528360754145859469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18546451018907169430572979 27819676528360754145859469)
                ·
                  refine ⟨10432378698135282804697301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27819676528360754145859469 10432378698135282804697301)
                  ·
                    refine ⟨244508875737545690735093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10432378698135282804697301 244508875737545690735093)
                    ·
                      rfl

theorem cell23_1428538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_1428538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428538 prefixEnd_1428538 := by exact prefixLift 1428538
  have htrace : WordTrace (prefixWord ++ tailWord_1428538) baseStart_1428538 baseEnd_1428538 := by
    simpa [prefixWord, tailWord_1428538, baseEnd_1428538] using wordTrace_append hprefix tailTrace_1428538
  have hstable : (prefixWord ++ tailWord_1428538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428538).length < 2 ^ (prefixWord ++ tailWord_1428538).sum := by decide
  have hdescent : baseEnd_1428538 < baseStart_1428538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428575 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 4]
def baseStart_1428575 : Nat := 118140960795 + 1428575 * 2 ^ 59
def prefixEnd_1428575 : Nat := 4983230072969 + 3 ^ 40 * 1428575 * 2
def baseEnd_1428575 : Nat := 733545625996853427442609

theorem tailTrace_1428575 : CollatzResearch.WordTrace tailWord_1428575 prefixEnd_1428575 733545625996853427442609 := by
  unfold tailWord_1428575
  simp only [CollatzResearch.WordTrace]
  refine ⟨52104410799524231030775179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34736273866349487353850119 52104410799524231030775179)
  ·
    refine ⟨78156616199286346546162769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52104410799524231030775179 78156616199286346546162769)
    ·
      refine ⟨58617462149464759909622077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78156616199286346546162769 58617462149464759909622077)
      ·
        refine ⟨21981548306049284966108279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58617462149464759909622077 21981548306049284966108279)
        ·
          refine ⟨32972322459073927449162419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21981548306049284966108279 32972322459073927449162419)
          ·
            refine ⟨49458483688610891173743629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32972322459073927449162419 49458483688610891173743629)
            ·
              refine ⟨18546931383229084190153861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49458483688610891173743629 18546931383229084190153861)
              ·
                refine ⟨3477549634355453285653849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18546931383229084190153861 3477549634355453285653849)
                ·
                  refine ⟨2608162225766589964240387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3477549634355453285653849 2608162225766589964240387)
                  ·
                    refine ⟨3912243338649884946360581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2608162225766589964240387 3912243338649884946360581)
                    ·
                      refine ⟨733545625996853427442609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3912243338649884946360581 733545625996853427442609)
                      ·
                        rfl

theorem cell23_1428575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_1428575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428575 prefixEnd_1428575 := by exact prefixLift 1428575
  have htrace : WordTrace (prefixWord ++ tailWord_1428575) baseStart_1428575 baseEnd_1428575 := by
    simpa [prefixWord, tailWord_1428575, baseEnd_1428575] using wordTrace_append hprefix tailTrace_1428575
  have hstable : (prefixWord ++ tailWord_1428575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428575).length < 2 ^ (prefixWord ++ tailWord_1428575).sum := by decide
  have hdescent : baseEnd_1428575 < baseStart_1428575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428592 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 2, 4, 2]
def baseStart_1428592 : Nat := 118140960795 + 1428592 * 2 ^ 59
def prefixEnd_1428592 : Nat := 4983230072969 + 3 ^ 40 * 1428592 * 2
def baseEnd_1428592 : Nat := 733554355167979860930031

theorem tailTrace_1428592 : CollatzResearch.WordTrace tailWord_1428592 prefixEnd_1428592 733554355167979860930031 := by
  unfold tailWord_1428592
  simp only [CollatzResearch.WordTrace]
  refine ⟨26052515420231321467072015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34736687226975095289429353 26052515420231321467072015)
  ·
    refine ⟨39078773130346982200608023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26052515420231321467072015 39078773130346982200608023)
    ·
      refine ⟨58618159695520473300912035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39078773130346982200608023 58618159695520473300912035)
      ·
        refine ⟨87927239543280709951368053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58618159695520473300912035 87927239543280709951368053)
        ·
          refine ⟨8243178707182566557940755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87927239543280709951368053 8243178707182566557940755)
          ·
            refine ⟨12364768060773849836911133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8243178707182566557940755 12364768060773849836911133)
            ·
              refine ⟨4636788022790193688841675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12364768060773849836911133 4636788022790193688841675)
              ·
                refine ⟨6955182034185290533262513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4636788022790193688841675 6955182034185290533262513)
                ·
                  refine ⟨5216386525638967899946885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6955182034185290533262513 5216386525638967899946885)
                  ·
                    refine ⟨978072473557306481240041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5216386525638967899946885 978072473557306481240041)
                    ·
                      refine ⟨733554355167979860930031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978072473557306481240041 733554355167979860930031)
                      ·
                        rfl

theorem cell23_1428592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 4, 2].length) (baseStart_1428592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428592 prefixEnd_1428592 := by exact prefixLift 1428592
  have htrace : WordTrace (prefixWord ++ tailWord_1428592) baseStart_1428592 baseEnd_1428592 := by
    simpa [prefixWord, tailWord_1428592, baseEnd_1428592] using wordTrace_append hprefix tailTrace_1428592
  have hstable : (prefixWord ++ tailWord_1428592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428592).length < 2 ^ (prefixWord ++ tailWord_1428592).sum := by decide
  have hdescent : baseEnd_1428592 < baseStart_1428592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428606 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1428606 : Nat := 118140960795 + 1428606 * 2 ^ 59
def prefixEnd_1428606 : Nat := 4983230072969 + 3 ^ 40 * 1428606 * 2
def baseEnd_1428606 : Nat := 244520514632380935384989

theorem tailTrace_1428606 : CollatzResearch.WordTrace tailWord_1428606 prefixEnd_1428606 244520514632380935384989 := by
  unfold tailWord_1428606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6513192682801490415644209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34737027641607948883435781 6513192682801490415644209)
  ·
    refine ⟨4884894512101117811733157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6513192682801490415644209 4884894512101117811733157)
    ·
      refine ⟨915917721018959589699967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4884894512101117811733157 915917721018959589699967)
      ·
        refine ⟨1373876581528439384549951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915917721018959589699967 1373876581528439384549951)
        ·
          refine ⟨2060814872292659076824927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373876581528439384549951 2060814872292659076824927)
          ·
            refine ⟨3091222308438988615237391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060814872292659076824927 3091222308438988615237391)
            ·
              refine ⟨4636833462658482922856087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091222308438988615237391 4636833462658482922856087)
              ·
                refine ⟨6955250193987724384284131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4636833462658482922856087 6955250193987724384284131)
                ·
                  refine ⟨10432875290981586576426197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955250193987724384284131 10432875290981586576426197)
                  ·
                    refine ⟨244520514632380935384989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10432875290981586576426197 244520514632380935384989)
                    ·
                      rfl

theorem cell23_1428606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1428606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428606 prefixEnd_1428606 := by exact prefixLift 1428606
  have htrace : WordTrace (prefixWord ++ tailWord_1428606) baseStart_1428606 baseEnd_1428606 := by
    simpa [prefixWord, tailWord_1428606, baseEnd_1428606] using wordTrace_append hprefix tailTrace_1428606
  have hstable : (prefixWord ++ tailWord_1428606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428606).length < 2 ^ (prefixWord ++ tailWord_1428606).sum := by decide
  have hdescent : baseEnd_1428606 < baseStart_1428606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428609 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1428609 : Nat := 118140960795 + 1428609 * 2 ^ 59
def prefixEnd_1428609 : Nat := 4983230072969 + 3 ^ 40 * 1428609 * 2
def baseEnd_1428609 : Nat := 733563084339106294417453

theorem tailTrace_1428609 : CollatzResearch.WordTrace tailWord_1428609 prefixEnd_1428609 733563084339106294417453 := by
  unfold tailWord_1428609
  simp only [CollatzResearch.WordTrace]
  refine ⟨52105650881401054837512881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34737100587600703225008587 52105650881401054837512881)
  ·
    refine ⟨39079238161050791128134661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52105650881401054837512881 39079238161050791128134661)
    ·
      refine ⟨7327357155197023336525249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39079238161050791128134661 7327357155197023336525249)
      ·
        refine ⟨5495517866397767502393937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7327357155197023336525249 5495517866397767502393937)
        ·
          refine ⟨4121638399798325626795453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5495517866397767502393937 4121638399798325626795453)
          ·
            refine ⟨1545614399924372110048295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4121638399798325626795453 1545614399924372110048295)
            ·
              refine ⟨2318421599886558165072443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545614399924372110048295 2318421599886558165072443)
              ·
                refine ⟨3477632399829837247608665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318421599886558165072443 3477632399829837247608665)
                ·
                  refine ⟨2608224299872377935706499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3477632399829837247608665 2608224299872377935706499)
                  ·
                    refine ⟨3912336449808566903559749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2608224299872377935706499 3912336449808566903559749)
                    ·
                      refine ⟨733563084339106294417453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3912336449808566903559749 733563084339106294417453)
                      ·
                        rfl

theorem cell23_1428609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1428609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428609 prefixEnd_1428609 := by exact prefixLift 1428609
  have htrace : WordTrace (prefixWord ++ tailWord_1428609) baseStart_1428609 baseEnd_1428609 := by
    simpa [prefixWord, tailWord_1428609, baseEnd_1428609] using wordTrace_append hprefix tailTrace_1428609
  have hstable : (prefixWord ++ tailWord_1428609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428609).length < 2 ^ (prefixWord ++ tailWord_1428609).sum := by decide
  have hdescent : baseEnd_1428609 < baseStart_1428609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428612 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_1428612 : Nat := 118140960795 + 1428612 * 2 ^ 59
def prefixEnd_1428612 : Nat := 4983230072969 + 3 ^ 40 * 1428612 * 2
def baseEnd_1428612 : Nat := 733564624781069782679939

theorem tailTrace_1428612 : CollatzResearch.WordTrace tailWord_1428612 prefixEnd_1428612 733564624781069782679939 := by
  unfold tailWord_1428612
  simp only [CollatzResearch.WordTrace]
  refine ⟨26052880150195093174936045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34737173533593457566581393 26052880150195093174936045)
  ·
    refine ⟨9769830056323159940601017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26052880150195093174936045 9769830056323159940601017)
    ·
      refine ⟨7327372542242369955450763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9769830056323159940601017 7327372542242369955450763)
      ·
        refine ⟨10991058813363554933176145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7327372542242369955450763 10991058813363554933176145)
        ·
          refine ⟨8243294110022666199882109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10991058813363554933176145 8243294110022666199882109)
          ·
            refine ⟨3091235291258499824955791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8243294110022666199882109 3091235291258499824955791)
            ·
              refine ⟨4636852936887749737433687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091235291258499824955791 4636852936887749737433687)
              ·
                refine ⟨6955279405331624606150531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4636852936887749737433687 6955279405331624606150531)
                ·
                  refine ⟨10432919107997436909225797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955279405331624606150531 10432919107997436909225797)
                  ·
                    refine ⟨1956172332749519420479837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10432919107997436909225797 1956172332749519420479837)
                    ·
                      refine ⟨733564624781069782679939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1956172332749519420479837 733564624781069782679939)
                      ·
                        rfl

theorem cell23_1428612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_1428612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428612 prefixEnd_1428612 := by exact prefixLift 1428612
  have htrace : WordTrace (prefixWord ++ tailWord_1428612) baseStart_1428612 baseEnd_1428612 := by
    simpa [prefixWord, tailWord_1428612, baseEnd_1428612] using wordTrace_append hprefix tailTrace_1428612
  have hstable : (prefixWord ++ tailWord_1428612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428612).length < 2 ^ (prefixWord ++ tailWord_1428612).sum := by decide
  have hdescent : baseEnd_1428612 < baseStart_1428612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428632 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 6]
def baseStart_1428632 : Nat := 118140960795 + 1428632 * 2 ^ 59
def prefixEnd_1428632 : Nat := 4983230072969 + 3 ^ 40 * 1428632 * 2
def baseEnd_1428632 : Nat := 81508321599351078269983

theorem tailTrace_1428632 : CollatzResearch.WordTrace tailWord_1428632 prefixEnd_1428632 81508321599351078269983 := by
  unfold tailWord_1428632
  simp only [CollatzResearch.WordTrace]
  refine ⟨26053244880158864882800075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34737659840211819843733433 26053244880158864882800075)
  ·
    refine ⟨39079867320238297324200113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26053244880158864882800075 39079867320238297324200113)
    ·
      refine ⟨29309900490178722993150085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39079867320238297324200113 29309900490178722993150085)
      ·
        refine ⟨5495606341908510561215641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29309900490178722993150085 5495606341908510561215641)
        ·
          refine ⟨4121704756431382920911731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5495606341908510561215641 4121704756431382920911731)
          ·
            refine ⟨6182557134647074381367597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121704756431382920911731 6182557134647074381367597)
            ·
              refine ⟨2318458925492652893012849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6182557134647074381367597 2318458925492652893012849)
              ·
                refine ⟨1738844194119489669759637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2318458925492652893012849 1738844194119489669759637)
                ·
                  refine ⟨81508321599351078269983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1738844194119489669759637 81508321599351078269983)
                  ·
                    rfl

theorem cell23_1428632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 6].length) (baseStart_1428632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428632 prefixEnd_1428632 := by exact prefixLift 1428632
  have htrace : WordTrace (prefixWord ++ tailWord_1428632) baseStart_1428632 baseEnd_1428632 := by
    simpa [prefixWord, tailWord_1428632, baseEnd_1428632] using wordTrace_append hprefix tailTrace_1428632
  have hstable : (prefixWord ++ tailWord_1428632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428632).length < 2 ^ (prefixWord ++ tailWord_1428632).sum := by decide
  have hdescent : baseEnd_1428632 < baseStart_1428632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428652 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 6, 3, 2]
def baseStart_1428652 : Nat := 118140960795 + 1428652 * 2 ^ 59
def prefixEnd_1428652 : Nat := 4983230072969 + 3 ^ 40 * 1428652 * 2
def baseEnd_1428652 : Nat := 733585164007249626179755

theorem tailTrace_1428652 : CollatzResearch.WordTrace tailWord_1428652 prefixEnd_1428652 733585164007249626179755 := by
  unfold tailWord_1428652
  simp only [CollatzResearch.WordTrace]
  refine ⟨26053609610122636590664105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34738146146830182120885473 26053609610122636590664105)
  ·
    refine ⟨19540207207591977442998079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26053609610122636590664105 19540207207591977442998079)
    ·
      refine ⟨29310310811387966164497119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19540207207591977442998079 29310310811387966164497119)
      ·
        refine ⟨43965466217081949246745679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29310310811387966164497119 43965466217081949246745679)
        ·
          refine ⟨65948199325622923870118519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43965466217081949246745679 65948199325622923870118519)
          ·
            refine ⟨98922298988434385805177779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65948199325622923870118519 98922298988434385805177779)
            ·
              refine ⟨148383448482651578707766669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98922298988434385805177779 148383448482651578707766669)
              ·
                refine ⟨55643793180994342015412501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148383448482651578707766669 55643793180994342015412501)
                ·
                  refine ⟨2608302805359109781972461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55643793180994342015412501 2608302805359109781972461)
                  ·
                    refine ⟨978113552009666168239673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608302805359109781972461 978113552009666168239673)
                    ·
                      refine ⟨733585164007249626179755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978113552009666168239673 733585164007249626179755)
                      ·
                        rfl

theorem cell23_1428652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_1428652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428652 prefixEnd_1428652 := by exact prefixLift 1428652
  have htrace : WordTrace (prefixWord ++ tailWord_1428652) baseStart_1428652 baseEnd_1428652 := by
    simpa [prefixWord, tailWord_1428652, baseEnd_1428652] using wordTrace_append hprefix tailTrace_1428652
  have hstable : (prefixWord ++ tailWord_1428652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428652).length < 2 ^ (prefixWord ++ tailWord_1428652).sum := by decide
  have hdescent : baseEnd_1428652 < baseStart_1428652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428686 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2]
def baseStart_1428686 : Nat := 118140960795 + 1428686 * 2 ^ 59
def prefixEnd_1428686 : Nat := 4983230072969 + 3 ^ 40 * 1428686 * 2
def baseEnd_1428686 : Nat := 733602622349502493154599

theorem tailTrace_1428686 : CollatzResearch.WordTrace tailWord_1428686 prefixEnd_1428686 733602622349502493154599 := by
  unfold tailWord_1428686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6513557412765262123508239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34738972868081397992043941 6513557412765262123508239)
  ·
    refine ⟨9770336119147893185262359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6513557412765262123508239 9770336119147893185262359)
    ·
      refine ⟨14655504178721839777893539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9770336119147893185262359 14655504178721839777893539)
      ·
        refine ⟨21983256268082759666840309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14655504178721839777893539 21983256268082759666840309)
        ·
          refine ⟨2060930275132758718766279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21983256268082759666840309 2060930275132758718766279)
          ·
            refine ⟨3091395412699138078149419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060930275132758718766279 3091395412699138078149419)
            ·
              refine ⟨4637093119048707117224129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091395412699138078149419 4637093119048707117224129)
              ·
                refine ⟨3477819839286530337918097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4637093119048707117224129 3477819839286530337918097)
                ·
                  refine ⟨2608364879464897753438573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3477819839286530337918097 2608364879464897753438573)
                  ·
                    refine ⟨978136829799336657539465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608364879464897753438573 978136829799336657539465)
                    ·
                      refine ⟨733602622349502493154599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978136829799336657539465 733602622349502493154599)
                      ·
                        rfl

theorem cell23_1428686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_1428686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428686 prefixEnd_1428686 := by exact prefixLift 1428686
  have htrace : WordTrace (prefixWord ++ tailWord_1428686) baseStart_1428686 baseEnd_1428686 := by
    simpa [prefixWord, tailWord_1428686, baseEnd_1428686] using wordTrace_append hprefix tailTrace_1428686
  have hstable : (prefixWord ++ tailWord_1428686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428686).length < 2 ^ (prefixWord ++ tailWord_1428686).sum := by decide
  have hdescent : baseEnd_1428686 < baseStart_1428686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428695 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_1428695 : Nat := 118140960795 + 1428695 * 2 ^ 59
def prefixEnd_1428695 : Nat := 4983230072969 + 3 ^ 40 * 1428695 * 2
def baseEnd_1428695 : Nat := 733607243675392957942057

theorem tailTrace_1428695 : CollatzResearch.WordTrace tailWord_1428695 prefixEnd_1428695 733607243675392957942057 := by
  unfold tailWord_1428695
  simp only [CollatzResearch.WordTrace]
  refine ⟨52108787559089491525143539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34739191706059661016762359 52108787559089491525143539)
  ·
    refine ⟨78163181338634237287715309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52108787559089491525143539 78163181338634237287715309)
    ·
      refine ⟨29311193001987838982893241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78163181338634237287715309 29311193001987838982893241)
      ·
        refine ⟨21983394751490879237169931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29311193001987838982893241 21983394751490879237169931)
        ·
          refine ⟨32975092127236318855754897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21983394751490879237169931 32975092127236318855754897)
          ·
            refine ⟨24731319095427239141816173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32975092127236318855754897 24731319095427239141816173)
            ·
              refine ⟨9274244660785214678181065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24731319095427239141816173 9274244660785214678181065)
              ·
                refine ⟨6955683495588911008635799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9274244660785214678181065 6955683495588911008635799)
                ·
                  refine ⟨10433525243383366512953699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955683495588911008635799 10433525243383366512953699)
                  ·
                    refine ⟨15650287865075049769430549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10433525243383366512953699 15650287865075049769430549)
                    ·
                      refine ⟨733607243675392957942057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15650287865075049769430549 733607243675392957942057)
                      ·
                        rfl

theorem cell23_1428695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_1428695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428695 prefixEnd_1428695 := by exact prefixLift 1428695
  have htrace : WordTrace (prefixWord ++ tailWord_1428695) baseStart_1428695 baseEnd_1428695 := by
    simpa [prefixWord, tailWord_1428695, baseEnd_1428695] using wordTrace_append hprefix tailTrace_1428695
  have hstable : (prefixWord ++ tailWord_1428695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428695).length < 2 ^ (prefixWord ++ tailWord_1428695).sum := by decide
  have hdescent : baseEnd_1428695 < baseStart_1428695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428705 : List Nat := [1, 2, 3, 1, 3, 2, 1, 10]
def baseStart_1428705 : Nat := 118140960795 + 1428705 * 2 ^ 59
def prefixEnd_1428705 : Nat := 4983230072969 + 3 ^ 40 * 1428705 * 2
def baseEnd_1428705 : Nat := 27170828832664367363593

theorem tailTrace_1428705 : CollatzResearch.WordTrace tailWord_1428705 prefixEnd_1428705 27170828832664367363593 := by
  unfold tailWord_1428705
  simp only [CollatzResearch.WordTrace]
  refine ⟨52109152289053263233007569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34739434859368842155338379 52109152289053263233007569)
  ·
    refine ⟨39081864216789947424755677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52109152289053263233007569 39081864216789947424755677)
    ·
      refine ⟨14655699081296230284283379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39081864216789947424755677 14655699081296230284283379)
      ·
        refine ⟨21983548621944345426425069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14655699081296230284283379 21983548621944345426425069)
        ·
          refine ⟨8243830733229129534909401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21983548621944345426425069 8243830733229129534909401)
          ·
            refine ⟨6182873049921847151182051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8243830733229129534909401 6182873049921847151182051)
            ·
              refine ⟨9274309574882770726773077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6182873049921847151182051 9274309574882770726773077)
              ·
                refine ⟨27170828832664367363593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9274309574882770726773077 27170828832664367363593)
                ·
                  rfl

theorem cell23_1428705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 10].length) (baseStart_1428705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428705 prefixEnd_1428705 := by exact prefixLift 1428705
  have htrace : WordTrace (prefixWord ++ tailWord_1428705) baseStart_1428705 baseEnd_1428705 := by
    simpa [prefixWord, tailWord_1428705, baseEnd_1428705] using wordTrace_append hprefix tailTrace_1428705
  have hstable : (prefixWord ++ tailWord_1428705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428705).length < 2 ^ (prefixWord ++ tailWord_1428705).sum := by decide
  have hdescent : baseEnd_1428705 < baseStart_1428705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428712 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_1428712 : Nat := 118140960795 + 1428712 * 2 ^ 59
def prefixEnd_1428712 : Nat := 4983230072969 + 3 ^ 40 * 1428712 * 2
def baseEnd_1428712 : Nat := 733615972846519391429479

theorem tailTrace_1428712 : CollatzResearch.WordTrace tailWord_1428712 prefixEnd_1428712 733615972846519391429479 := by
  unfold tailWord_1428712
  simp only [CollatzResearch.WordTrace]
  refine ⟨26054703800013951714256195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34739605066685268952341593 26054703800013951714256195)
  ·
    refine ⟨39082055700020927571384293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26054703800013951714256195 39082055700020927571384293)
    ·
      refine ⟨7327885443753923919634555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39082055700020927571384293 7327885443753923919634555)
      ·
        refine ⟨10991828165630885879451833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7327885443753923919634555 10991828165630885879451833)
        ·
          refine ⟨8243871124223164409588875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10991828165630885879451833 8243871124223164409588875)
          ·
            refine ⟨12365806686334746614383313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8243871124223164409588875 12365806686334746614383313)
            ·
              refine ⟨9274355014751059960787485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12365806686334746614383313 9274355014751059960787485)
              ·
                refine ⟨3477883130531647485295307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9274355014751059960787485 3477883130531647485295307)
                ·
                  refine ⟨5216824695797471227942961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477883130531647485295307 5216824695797471227942961)
                  ·
                    refine ⟨3912618521848103420957221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5216824695797471227942961 3912618521848103420957221)
                    ·
                      refine ⟨733615972846519391429479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3912618521848103420957221 733615972846519391429479)
                      ·
                        rfl

theorem cell23_1428712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_1428712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428712 prefixEnd_1428712 := by exact prefixLift 1428712
  have htrace : WordTrace (prefixWord ++ tailWord_1428712) baseStart_1428712 baseEnd_1428712 := by
    simpa [prefixWord, tailWord_1428712, baseEnd_1428712] using wordTrace_append hprefix tailTrace_1428712
  have hstable : (prefixWord ++ tailWord_1428712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428712).length < 2 ^ (prefixWord ++ tailWord_1428712).sum := by decide
  have hdescent : baseEnd_1428712 < baseStart_1428712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428719 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 3]
def baseStart_1428719 : Nat := 118140960795 + 1428719 * 2 ^ 59
def prefixEnd_1428719 : Nat := 4983230072969 + 3 ^ 40 * 1428719 * 2
def baseEnd_1428719 : Nat := 733619567211100864041947

theorem tailTrace_1428719 : CollatzResearch.WordTrace tailWord_1428719 prefixEnd_1428719 733619567211100864041947 := by
  unfold tailWord_1428719
  simp only [CollatzResearch.WordTrace]
  refine ⟨52109662911002543624017211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34739775274001695749344807 52109662911002543624017211)
  ·
    refine ⟨78164494366503815436025817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52109662911002543624017211 78164494366503815436025817)
    ·
      refine ⟨58623370774877861577019363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78164494366503815436025817 58623370774877861577019363)
      ·
        refine ⟨87935056162316792365529045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58623370774877861577019363 87935056162316792365529045)
        ·
          refine ⟨2060977878804299821067087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 87935056162316792365529045 2060977878804299821067087)
          ·
            refine ⟨3091466818206449731600631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060977878804299821067087 3091466818206449731600631)
            ·
              refine ⟨4637200227309674597400947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091466818206449731600631 4637200227309674597400947)
              ·
                refine ⟨6955800340964511896101421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4637200227309674597400947 6955800340964511896101421)
                ·
                  refine ⟨2608425127861691961038033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6955800340964511896101421 2608425127861691961038033)
                  ·
                    refine ⟨1956318845896268970778525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2608425127861691961038033 1956318845896268970778525)
                    ·
                      refine ⟨733619567211100864041947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1956318845896268970778525 733619567211100864041947)
                      ·
                        rfl

theorem cell23_1428719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 3].length) (baseStart_1428719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428719 prefixEnd_1428719 := by exact prefixLift 1428719
  have htrace : WordTrace (prefixWord ++ tailWord_1428719) baseStart_1428719 baseEnd_1428719 := by
    simpa [prefixWord, tailWord_1428719, baseEnd_1428719] using wordTrace_append hprefix tailTrace_1428719
  have hstable : (prefixWord ++ tailWord_1428719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428719).length < 2 ^ (prefixWord ++ tailWord_1428719).sum := by decide
  have hdescent : baseEnd_1428719 < baseStart_1428719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428750 : List Nat := [4, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2]
def baseStart_1428750 : Nat := 118140960795 + 1428750 * 2 ^ 59
def prefixEnd_1428750 : Nat := 4983230072969 + 3 ^ 40 * 1428750 * 2
def baseEnd_1428750 : Nat := 733635485111390242754305

theorem tailTrace_1428750 : CollatzResearch.WordTrace tailWord_1428750 prefixEnd_1428750 733635485111390242754305 := by
  unfold tailWord_1428750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6513849196736279489799463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34740529049260157278930469 6513849196736279489799463)
  ·
    refine ⟨9770773795104419234699195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6513849196736279489799463 9770773795104419234699195)
    ·
      refine ⟨14656160692656628852048793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9770773795104419234699195 14656160692656628852048793)
      ·
        refine ⟨10992120519492471639036595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14656160692656628852048793 10992120519492471639036595)
        ·
          refine ⟨16488180779238707458554893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10992120519492471639036595 16488180779238707458554893)
          ·
            refine ⟨6183067792214515296958085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16488180779238707458554893 6183067792214515296958085)
            ·
              refine ⟨1159325211040221618179641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6183067792214515296958085 1159325211040221618179641)
              ·
                refine ⟨869493908280166213634731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1159325211040221618179641 869493908280166213634731)
                ·
                  refine ⟨1304240862420249320452097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869493908280166213634731 1304240862420249320452097)
                  ·
                    refine ⟨978180646815186990339073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1304240862420249320452097 978180646815186990339073)
                    ·
                      refine ⟨733635485111390242754305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978180646815186990339073 733635485111390242754305)
                      ·
                        rfl

theorem cell23_1428750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_1428750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428750 prefixEnd_1428750 := by exact prefixLift 1428750
  have htrace : WordTrace (prefixWord ++ tailWord_1428750) baseStart_1428750 baseEnd_1428750 := by
    simpa [prefixWord, tailWord_1428750, baseEnd_1428750] using wordTrace_append hprefix tailTrace_1428750
  have hstable : (prefixWord ++ tailWord_1428750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428750).length < 2 ^ (prefixWord ++ tailWord_1428750).sum := by decide
  have hdescent : baseEnd_1428750 < baseStart_1428750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428759 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 5, 3, 2]
def baseStart_1428759 : Nat := 118140960795 + 1428759 * 2 ^ 59
def prefixEnd_1428759 : Nat := 4983230072969 + 3 ^ 40 * 1428759 * 2
def baseEnd_1428759 : Nat := 733640106437280707541763

theorem tailTrace_1428759 : CollatzResearch.WordTrace tailWord_1428759 prefixEnd_1428759 733640106437280707541763 := by
  unfold tailWord_1428759
  simp only [CollatzResearch.WordTrace]
  refine ⟨52111121830857630455473331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34740747887238420303648887 52111121830857630455473331)
  ·
    refine ⟨78166682746286445683209997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52111121830857630455473331 78166682746286445683209997)
    ·
      refine ⟨29312506029857417131203749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78166682746286445683209997 29312506029857417131203749)
      ·
        refine ⟨5496094880598265712100703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29312506029857417131203749 5496094880598265712100703)
        ·
          refine ⟨8244142320897398568151055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496094880598265712100703 8244142320897398568151055)
          ·
            refine ⟨12366213481346097852226583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8244142320897398568151055 12366213481346097852226583)
            ·
              refine ⟨18549320222019146778339875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12366213481346097852226583 18549320222019146778339875)
              ·
                refine ⟨27823980333028720167509813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18549320222019146778339875 27823980333028720167509813)
                ·
                  refine ⟨2608498156221442515704045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27823980333028720167509813 2608498156221442515704045)
                  ·
                    refine ⟨978186808583040943389017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608498156221442515704045 978186808583040943389017)
                    ·
                      refine ⟨733640106437280707541763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978186808583040943389017 733640106437280707541763)
                      ·
                        rfl

theorem cell23_1428759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_1428759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428759 prefixEnd_1428759 := by exact prefixLift 1428759
  have htrace : WordTrace (prefixWord ++ tailWord_1428759) baseStart_1428759 baseEnd_1428759 := by
    simpa [prefixWord, tailWord_1428759, baseEnd_1428759] using wordTrace_append hprefix tailTrace_1428759
  have hstable : (prefixWord ++ tailWord_1428759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428759).length < 2 ^ (prefixWord ++ tailWord_1428759).sum := by decide
  have hdescent : baseEnd_1428759 < baseStart_1428759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428772 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1428772 : Nat := 118140960795 + 1428772 * 2 ^ 59
def prefixEnd_1428772 : Nat := 4983230072969 + 3 ^ 40 * 1428772 * 2
def baseEnd_1428772 : Nat := 733646781685789156679203

theorem tailTrace_1428772 : CollatzResearch.WordTrace tailWord_1428772 prefixEnd_1428772 733646781685789156679203 := by
  unfold tailWord_1428772
  simp only [CollatzResearch.WordTrace]
  refine ⟨26055797989905266837848285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34741063986540355783797713 26055797989905266837848285)
  ·
    refine ⟨9770924246214475064193107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26055797989905266837848285 9770924246214475064193107)
    ·
      refine ⟨14656386369321712596289661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9770924246214475064193107 14656386369321712596289661)
      ·
        refine ⟨5496144888495642223608623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14656386369321712596289661 5496144888495642223608623)
        ·
          refine ⟨8244217332743463335412935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496144888495642223608623 8244217332743463335412935)
          ·
            refine ⟨12366325999115195003119403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8244217332743463335412935 12366325999115195003119403)
            ·
              refine ⟨18549488998672792504679105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12366325999115195003119403 18549488998672792504679105)
              ·
                refine ⟨13912116749004594378509329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18549488998672792504679105 13912116749004594378509329)
                ·
                  refine ⟨10434087561753445783881997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13912116749004594378509329 10434087561753445783881997)
                  ·
                    refine ⟨3912782835657542168955749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10434087561753445783881997 3912782835657542168955749)
                    ·
                      refine ⟨733646781685789156679203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3912782835657542168955749 733646781685789156679203)
                      ·
                        rfl

theorem cell23_1428772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1428772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428772 prefixEnd_1428772 := by exact prefixLift 1428772
  have htrace : WordTrace (prefixWord ++ tailWord_1428772) baseStart_1428772 baseEnd_1428772 := by
    simpa [prefixWord, tailWord_1428772, baseEnd_1428772] using wordTrace_append hprefix tailTrace_1428772
  have hstable : (prefixWord ++ tailWord_1428772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428772).length < 2 ^ (prefixWord ++ tailWord_1428772).sum := by decide
  have hdescent : baseEnd_1428772 < baseStart_1428772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428776 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_1428776 : Nat := 118140960795 + 1428776 * 2 ^ 59
def prefixEnd_1428776 : Nat := 4983230072969 + 3 ^ 40 * 1428776 * 2
def baseEnd_1428776 : Nat := 733648835608407141029185

theorem tailTrace_1428776 : CollatzResearch.WordTrace tailWord_1428776 prefixEnd_1428776 733648835608407141029185 := by
  unfold tailWord_1428776
  simp only [CollatzResearch.WordTrace]
  refine ⟨26055870935898021179421091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34741161247864028239228121 26055870935898021179421091)
  ·
    refine ⟨39083806403847031769131637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26055870935898021179421091 39083806403847031769131637)
    ·
      refine ⟨3664106850360659228356091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39083806403847031769131637 3664106850360659228356091)
      ·
        refine ⟨5496160275540988842534137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3664106850360659228356091 5496160275540988842534137)
        ·
          refine ⟨4122120206655741631900603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5496160275540988842534137 4122120206655741631900603)
          ·
            refine ⟨6183180309983612447850905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122120206655741631900603 6183180309983612447850905)
            ·
              refine ⟨4637385232487709335888179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6183180309983612447850905 4637385232487709335888179)
              ·
                refine ⟨6956077848731564003832269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4637385232487709335888179 6956077848731564003832269)
                ·
                  refine ⟨2608529193274336501437101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6956077848731564003832269 2608529193274336501437101)
                  ·
                    refine ⟨978198447477876188038913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608529193274336501437101 978198447477876188038913)
                    ·
                      refine ⟨733648835608407141029185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978198447477876188038913 733648835608407141029185)
                      ·
                        rfl

theorem cell23_1428776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_1428776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428776 prefixEnd_1428776 := by exact prefixLift 1428776
  have htrace : WordTrace (prefixWord ++ tailWord_1428776) baseStart_1428776 baseEnd_1428776 := by
    simpa [prefixWord, tailWord_1428776, baseEnd_1428776] using wordTrace_append hprefix tailTrace_1428776
  have hstable : (prefixWord ++ tailWord_1428776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428776).length < 2 ^ (prefixWord ++ tailWord_1428776).sum := by decide
  have hdescent : baseEnd_1428776 < baseStart_1428776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428793 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1428793 : Nat := 118140960795 + 1428793 * 2 ^ 59
def prefixEnd_1428793 : Nat := 4983230072969 + 3 ^ 40 * 1428793 * 2
def baseEnd_1428793 : Nat := 733657564779533574516607

theorem tailTrace_1428793 : CollatzResearch.WordTrace tailWord_1428793 prefixEnd_1428793 733657564779533574516607 := by
  unfold tailWord_1428793
  simp only [CollatzResearch.WordTrace]
  refine ⟨52112361912734454262211033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34741574608489636174807355 52112361912734454262211033)
  ·
    refine ⟨39084271434550840696658275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52112361912734454262211033 39084271434550840696658275)
    ·
      refine ⟨58626407151826261044987413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39084271434550840696658275 58626407151826261044987413)
      ·
        refine ⟨2748112835241855986483785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58626407151826261044987413 2748112835241855986483785)
        ·
          refine ⟨2061084626431391989862839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2748112835241855986483785 2061084626431391989862839)
          ·
            refine ⟨3091626939647087984794259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061084626431391989862839 3091626939647087984794259)
            ·
              refine ⟨4637440409470631977191389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091626939647087984794259 4637440409470631977191389)
              ·
                refine ⟨1739040153551486991446771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4637440409470631977191389 1739040153551486991446771)
                ·
                  refine ⟨2608560230327230487170157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739040153551486991446771 2608560230327230487170157)
                  ·
                    refine ⟨978210086372711432688809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608560230327230487170157 978210086372711432688809)
                    ·
                      refine ⟨733657564779533574516607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978210086372711432688809 733657564779533574516607)
                      ·
                        rfl

theorem cell23_1428793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1428793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428793 prefixEnd_1428793 := by exact prefixLift 1428793
  have htrace : WordTrace (prefixWord ++ tailWord_1428793) baseStart_1428793 baseEnd_1428793 := by
    simpa [prefixWord, tailWord_1428793, baseEnd_1428793] using wordTrace_append hprefix tailTrace_1428793
  have hstable : (prefixWord ++ tailWord_1428793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428793).length < 2 ^ (prefixWord ++ tailWord_1428793).sum := by decide
  have hdescent : baseEnd_1428793 < baseStart_1428793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428812 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 7]
def baseStart_1428812 : Nat := 118140960795 + 1428812 * 2 ^ 59
def prefixEnd_1428812 : Nat := 4983230072969 + 3 ^ 40 * 1428812 * 2
def baseEnd_1428812 : Nat := 81518591212441000019891

theorem tailTrace_1428812 : CollatzResearch.WordTrace tailWord_1428812 prefixEnd_1428812 81518591212441000019891 := by
  unfold tailWord_1428812
  simp only [CollatzResearch.WordTrace]
  refine ⟨26056527449832810253576345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34742036599777080338101793 26056527449832810253576345)
  ·
    refine ⟨19542395587374607690182259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26056527449832810253576345 19542395587374607690182259)
    ·
      refine ⟨29313593381061911535273389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19542395587374607690182259 29313593381061911535273389)
      ·
        refine ⟨10992597517898216825727521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29313593381061911535273389 10992597517898216825727521)
        ·
          refine ⟨8244448138423662619295641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10992597517898216825727521 8244448138423662619295641)
          ·
            refine ⟨6183336103817746964471731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8244448138423662619295641 6183336103817746964471731)
            ·
              refine ⟨9275004155726620446707597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6183336103817746964471731 9275004155726620446707597)
              ·
                refine ⟨3478126558397482667515349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9275004155726620446707597 3478126558397482667515349)
                ·
                  refine ⟨81518591212441000019891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3478126558397482667515349 81518591212441000019891)
                  ·
                    rfl

theorem cell23_1428812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_1428812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428812 prefixEnd_1428812 := by exact prefixLift 1428812
  have htrace : WordTrace (prefixWord ++ tailWord_1428812) baseStart_1428812 baseEnd_1428812 := by
    simpa [prefixWord, tailWord_1428812, baseEnd_1428812] using wordTrace_append hprefix tailTrace_1428812
  have hstable : (prefixWord ++ tailWord_1428812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428812).length < 2 ^ (prefixWord ++ tailWord_1428812).sum := by decide
  have hdescent : baseEnd_1428812 < baseStart_1428812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428919 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 6]
def baseStart_1428919 : Nat := 118140960795 + 1428919 * 2 ^ 59
def prefixEnd_1428919 : Nat := 4983230072969 + 3 ^ 40 * 1428919 * 2
def baseEnd_1428919 : Nat := 81524695926888897949003

theorem tailTrace_1428919 : CollatzResearch.WordTrace tailWord_1428919 prefixEnd_1428919 81524695926888897949003 := by
  unfold tailWord_1428919
  simp only [CollatzResearch.WordTrace]
  refine ⟨52116957510277977781297811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34744638340185318520865207 52116957510277977781297811)
  ·
    refine ⟨78175436265416966671946717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52116957510277977781297811 78175436265416966671946717)
    ·
      refine ⟨29315788599531362501980019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78175436265416966671946717 29315788599531362501980019)
      ·
        refine ⟨43973682899297043752970029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29315788599531362501980019 43973682899297043752970029)
        ·
          refine ⟨16490131087236391407363761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43973682899297043752970029 16490131087236391407363761)
          ·
            refine ⟨12367598315427293555522821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16490131087236391407363761 12367598315427293555522821)
            ·
              refine ⟨2318924684142617541660529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12367598315427293555522821 2318924684142617541660529)
              ·
                refine ⟨1739193513106963156245397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2318924684142617541660529 1739193513106963156245397)
                ·
                  refine ⟨81524695926888897949003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1739193513106963156245397 81524695926888897949003)
                  ·
                    rfl

theorem cell23_1428919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 6].length) (baseStart_1428919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428919 prefixEnd_1428919 := by exact prefixLift 1428919
  have htrace : WordTrace (prefixWord ++ tailWord_1428919) baseStart_1428919 baseEnd_1428919 := by
    simpa [prefixWord, tailWord_1428919, baseEnd_1428919] using wordTrace_append hprefix tailTrace_1428919
  have hstable : (prefixWord ++ tailWord_1428919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428919).length < 2 ^ (prefixWord ++ tailWord_1428919).sum := by decide
  have hdescent : baseEnd_1428919 < baseStart_1428919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428949 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_1428949 : Nat := 118140960795 + 1428949 * 2 ^ 59
def prefixEnd_1428949 : Nat := 4983230072969 + 3 ^ 40 * 1428949 * 2
def baseEnd_1428949 : Nat := 244579222587211654721963

theorem tailTrace_1428949 : CollatzResearch.WordTrace tailWord_1428949 prefixEnd_1428949 244579222587211654721963 := by
  unfold tailWord_1428949
  simp only [CollatzResearch.WordTrace]
  refine ⟨52118051700169292904889901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34745367800112861936593267 52118051700169292904889901)
  ·
    refine ⟨19544269387563484839333713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52118051700169292904889901 19544269387563484839333713)
    ·
      refine ⟨14658202040672613629500285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19544269387563484839333713 14658202040672613629500285)
      ·
        refine ⟨5496825765252230111062607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14658202040672613629500285 5496825765252230111062607)
        ·
          refine ⟨8245238647878345166593911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496825765252230111062607 8245238647878345166593911)
          ·
            refine ⟨12367857971817517749890867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8245238647878345166593911 12367857971817517749890867)
            ·
              refine ⟨18551786957726276624836301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12367857971817517749890867 18551786957726276624836301)
              ·
                refine ⟨6956920109147353734313613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18551786957726276624836301 6956920109147353734313613)
                ·
                  refine ⟨2608845040930257650367605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6956920109147353734313613 2608845040930257650367605)
                  ·
                    refine ⟨244579222587211654721963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2608845040930257650367605 244579222587211654721963)
                    ·
                      rfl

theorem cell23_1428949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_1428949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428949 prefixEnd_1428949 := by exact prefixLift 1428949
  have htrace : WordTrace (prefixWord ++ tailWord_1428949) baseStart_1428949 baseEnd_1428949 := by
    simpa [prefixWord, tailWord_1428949, baseEnd_1428949] using wordTrace_append hprefix tailTrace_1428949
  have hstable : (prefixWord ++ tailWord_1428949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428949).length < 2 ^ (prefixWord ++ tailWord_1428949).sum := by decide
  have hdescent : baseEnd_1428949 < baseStart_1428949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428950 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1428950 : Nat := 118140960795 + 1428950 * 2 ^ 59
def prefixEnd_1428950 : Nat := 4983230072969 + 3 ^ 40 * 1428950 * 2
def baseEnd_1428950 : Nat := 733738181242289460253385

theorem tailTrace_1428950 : CollatzResearch.WordTrace tailWord_1428950 prefixEnd_1428950 733738181242289460253385 := by
  unfold tailWord_1428950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257380510822854379729769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34745392115443780050450869 3257380510822854379729769)
  ·
    refine ⟨2443035383117140784797327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3257380510822854379729769 2443035383117140784797327)
    ·
      refine ⟨3664553074675711177195991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443035383117140784797327 3664553074675711177195991)
      ·
        refine ⟨5496829612013566765793987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3664553074675711177195991 5496829612013566765793987)
        ·
          refine ⟨8245244418020350148690981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496829612013566765793987 8245244418020350148690981)
          ·
            refine ⟨1545983328378815652879559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8245244418020350148690981 1545983328378815652879559)
            ·
              refine ⟨2318974992568223479319339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545983328378815652879559 2318974992568223479319339)
              ·
                refine ⟨3478462488852335218979009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318974992568223479319339 3478462488852335218979009)
                ·
                  refine ⟨2608846866639251414234257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3478462488852335218979009 2608846866639251414234257)
                  ·
                    refine ⟨1956635149979438560675693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2608846866639251414234257 1956635149979438560675693)
                    ·
                      refine ⟨733738181242289460253385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1956635149979438560675693 733738181242289460253385)
                      ·
                        rfl

theorem cell23_1428950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1428950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428950 prefixEnd_1428950 := by exact prefixLift 1428950
  have htrace : WordTrace (prefixWord ++ tailWord_1428950) baseStart_1428950 baseEnd_1428950 := by
    simpa [prefixWord, tailWord_1428950, baseEnd_1428950] using wordTrace_append hprefix tailTrace_1428950
  have hstable : (prefixWord ++ tailWord_1428950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428950).length < 2 ^ (prefixWord ++ tailWord_1428950).sum := by decide
  have hdescent : baseEnd_1428950 < baseStart_1428950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428989 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1428989 : Nat := 118140960795 + 1428989 * 2 ^ 59
def prefixEnd_1428989 : Nat := 4983230072969 + 3 ^ 40 * 1428989 * 2
def baseEnd_1428989 : Nat := 733758206987814807665705

theorem tailTrace_1428989 : CollatzResearch.WordTrace tailWord_1428989 prefixEnd_1428989 733758206987814807665705 := by
  unfold tailWord_1428989
  simp only [CollatzResearch.WordTrace]
  refine ⟨52119510620024379736346021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34746340413349586490897347 52119510620024379736346021)
  ·
    refine ⟨9772408241254571200564879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52119510620024379736346021 9772408241254571200564879)
    ·
      refine ⟨14658612361881856800847319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9772408241254571200564879 14658612361881856800847319)
      ·
        refine ⟨21987918542822785201270979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14658612361881856800847319 21987918542822785201270979)
        ·
          refine ⟨32981877814234177801906469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21987918542822785201270979 32981877814234177801906469)
          ·
            refine ⟨6184102090168908337857463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32981877814234177801906469 6184102090168908337857463)
            ·
              refine ⟨9276153135253362506786195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6184102090168908337857463 9276153135253362506786195)
              ·
                refine ⟨13914229702880043760179293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9276153135253362506786195 13914229702880043760179293)
                ·
                  refine ⟨5217836138580016410067235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13914229702880043760179293 5217836138580016410067235)
                  ·
                    refine ⟨7826754207870024615100853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5217836138580016410067235 7826754207870024615100853)
                    ·
                      refine ⟨733758206987814807665705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7826754207870024615100853 733758206987814807665705)
                      ·
                        rfl

theorem cell23_1428989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1428989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1428989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1428989 prefixEnd_1428989 := by exact prefixLift 1428989
  have htrace : WordTrace (prefixWord ++ tailWord_1428989) baseStart_1428989 baseEnd_1428989 := by
    simpa [prefixWord, tailWord_1428989, baseEnd_1428989] using wordTrace_append hprefix tailTrace_1428989
  have hstable : (prefixWord ++ tailWord_1428989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428989).length < 2 ^ (prefixWord ++ tailWord_1428989).sum := by decide
  have hdescent : baseEnd_1428989 < baseStart_1428989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429003 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 4]
def baseStart_1429003 : Nat := 118140960795 + 1429003 * 2 ^ 59
def prefixEnd_1429003 : Nat := 4983230072969 + 3 ^ 40 * 1429003 * 2
def baseEnd_1429003 : Nat := 733765395716977752890641

theorem tailTrace_1429003 : CollatzResearch.WordTrace tailWord_1429003 prefixEnd_1429003 733765395716977752890641 := by
  unfold tailWord_1429003
  simp only [CollatzResearch.WordTrace]
  refine ⟨52120021241973660127355663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34746680827982440084903775 52120021241973660127355663)
  ·
    refine ⟨78180031862960490191033495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52120021241973660127355663 78180031862960490191033495)
    ·
      refine ⟨117270047794440735286550243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78180031862960490191033495 117270047794440735286550243)
      ·
        refine ⟨175905071691661102929825365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117270047794440735286550243 175905071691661102929825365)
        ·
          refine ⟨2061387558886653549958891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 175905071691661102929825365 2061387558886653549958891)
          ·
            refine ⟨3092081338329980324938337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061387558886653549958891 3092081338329980324938337)
            ·
              refine ⟨2319061003747485243703753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3092081338329980324938337 2319061003747485243703753)
              ·
                refine ⟨1739295752810613932777815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2319061003747485243703753 1739295752810613932777815)
                ·
                  refine ⟨2608943629215920899166723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739295752810613932777815 2608943629215920899166723)
                  ·
                    refine ⟨3913415443823881348750085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2608943629215920899166723 3913415443823881348750085)
                    ·
                      refine ⟨733765395716977752890641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3913415443823881348750085 733765395716977752890641)
                      ·
                        rfl

theorem cell23_1429003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 4].length) (baseStart_1429003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429003 prefixEnd_1429003 := by exact prefixLift 1429003
  have htrace : WordTrace (prefixWord ++ tailWord_1429003) baseStart_1429003 baseEnd_1429003 := by
    simpa [prefixWord, tailWord_1429003, baseEnd_1429003] using wordTrace_append hprefix tailTrace_1429003
  have hstable : (prefixWord ++ tailWord_1429003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429003).length < 2 ^ (prefixWord ++ tailWord_1429003).sum := by decide
  have hdescent : baseEnd_1429003 < baseStart_1429003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429106 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1429106 : Nat := 118140960795 + 1429106 * 2 ^ 59
def prefixEnd_1429106 : Nat := 4983230072969 + 3 ^ 40 * 1429106 * 2
def baseEnd_1429106 : Nat := 733818284224390849902667

theorem tailTrace_1429106 : CollatzResearch.WordTrace tailWord_1429106 prefixEnd_1429106 733818284224390849902667 := by
  unfold tailWord_1429106
  simp only [CollatzResearch.WordTrace]
  refine ⟨13030944490150127179588793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34749185307067005812236781 13030944490150127179588793)
  ·
    refine ⟨9773208367612595384691595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13030944490150127179588793 9773208367612595384691595)
    ·
      refine ⟨14659812551418893077037393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9773208367612595384691595 14659812551418893077037393)
      ·
        refine ⟨10994859413564169807778045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14659812551418893077037393 10994859413564169807778045)
        ·
          refine ⟨4123072280086563677916767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10994859413564169807778045 4123072280086563677916767)
          ·
            refine ⟨6184608420129845516875151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123072280086563677916767 6184608420129845516875151)
            ·
              refine ⟨9276912630194768275312727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6184608420129845516875151 9276912630194768275312727)
              ·
                refine ⟨13915368945292152412969091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9276912630194768275312727 13915368945292152412969091)
                ·
                  refine ⟨20873053417938228619453637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13915368945292152412969091 20873053417938228619453637)
                  ·
                    refine ⟨3913697515863417866147557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20873053417938228619453637 3913697515863417866147557)
                    ·
                      refine ⟨733818284224390849902667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3913697515863417866147557 733818284224390849902667)
                      ·
                        rfl

theorem cell23_1429106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1429106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429106 prefixEnd_1429106 := by exact prefixLift 1429106
  have htrace : WordTrace (prefixWord ++ tailWord_1429106) baseStart_1429106 baseEnd_1429106 := by
    simpa [prefixWord, tailWord_1429106, baseEnd_1429106] using wordTrace_append hprefix tailTrace_1429106
  have hstable : (prefixWord ++ tailWord_1429106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429106).length < 2 ^ (prefixWord ++ tailWord_1429106).sum := by decide
  have hdescent : baseEnd_1429106 < baseStart_1429106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429110 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_1429110 : Nat := 118140960795 + 1429110 * 2 ^ 59
def prefixEnd_1429110 : Nat := 4983230072969 + 3 ^ 40 * 1429110 * 2
def baseEnd_1429110 : Nat := 733820338147008834252649

theorem tailTrace_1429110 : CollatzResearch.WordTrace tailWord_1429110 prefixEnd_1429110 733820338147008834252649 := by
  unfold tailWord_1429110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257745240786626087593799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34749282568390678267667189 3257745240786626087593799)
  ·
    refine ⟨4886617861179939131390699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3257745240786626087593799 4886617861179939131390699)
    ·
      refine ⟨7329926791769908697086049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4886617861179939131390699 7329926791769908697086049)
      ·
        refine ⟨5497445093827431522814537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7329926791769908697086049 5497445093827431522814537)
        ·
          refine ⟨4123083820370573642110903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5497445093827431522814537 4123083820370573642110903)
          ·
            refine ⟨6184625730555860463166355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123083820370573642110903 6184625730555860463166355)
            ·
              refine ⟨9276938595833790694749533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6184625730555860463166355 9276938595833790694749533)
              ·
                refine ⟨3478851973437671510531075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9276938595833790694749533 3478851973437671510531075)
                ·
                  refine ⟨5218277960156507265796613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478851973437671510531075 5218277960156507265796613)
                  ·
                    refine ⟨978427117529345112336865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5218277960156507265796613 978427117529345112336865)
                    ·
                      refine ⟨733820338147008834252649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978427117529345112336865 733820338147008834252649)
                      ·
                        rfl

theorem cell23_1429110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_1429110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429110 prefixEnd_1429110 := by exact prefixLift 1429110
  have htrace : WordTrace (prefixWord ++ tailWord_1429110) baseStart_1429110 baseEnd_1429110 := by
    simpa [prefixWord, tailWord_1429110, baseEnd_1429110] using wordTrace_append hprefix tailTrace_1429110
  have hstable : (prefixWord ++ tailWord_1429110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429110).length < 2 ^ (prefixWord ++ tailWord_1429110).sum := by decide
  have hdescent : baseEnd_1429110 < baseStart_1429110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429150 : List Nat := [4, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1429150 : Nat := 118140960795 + 1429150 * 2 ^ 59
def prefixEnd_1429150 : Nat := 4983230072969 + 3 ^ 40 * 1429150 * 2
def baseEnd_1429150 : Nat := 81537875263687630861385

theorem tailTrace_1429150 : CollatzResearch.WordTrace tailWord_1429150 prefixEnd_1429150 81537875263687630861385 := by
  unfold tailWord_1429150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6515672846555138029119613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34750255181627402821971269 6515672846555138029119613)
  ·
    refine ⟨2443377317458176760919855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6515672846555138029119613 2443377317458176760919855)
    ·
      refine ⟨3665065976187265141379783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443377317458176760919855 3665065976187265141379783)
      ·
        refine ⟨5497598964280897712069675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665065976187265141379783 5497598964280897712069675)
        ·
          refine ⟨8246398446421346568104513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497598964280897712069675 8246398446421346568104513)
          ·
            refine ⟨6184798834816009926078385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8246398446421346568104513 6184798834816009926078385)
            ·
              refine ⟨4638599126112007444558789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6184798834816009926078385 4638599126112007444558789)
              ·
                refine ⟨869737336146001395854773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4638599126112007444558789 869737336146001395854773)
                ·
                  refine ⟨81537875263687630861385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 869737336146001395854773 81537875263687630861385)
                  ·
                    rfl

theorem cell23_1429150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1429150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429150 prefixEnd_1429150 := by exact prefixLift 1429150
  have htrace : WordTrace (prefixWord ++ tailWord_1429150) baseStart_1429150 baseEnd_1429150 := by
    simpa [prefixWord, tailWord_1429150, baseEnd_1429150] using wordTrace_append hprefix tailTrace_1429150
  have hstable : (prefixWord ++ tailWord_1429150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429150).length < 2 ^ (prefixWord ++ tailWord_1429150).sum := by decide
  have hdescent : baseEnd_1429150 < baseStart_1429150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429210 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_1429210 : Nat := 118140960795 + 1429210 * 2 ^ 59
def prefixEnd_1429210 : Nat := 4983230072969 + 3 ^ 40 * 1429210 * 2
def baseEnd_1429210 : Nat := 244623895404152814334063

theorem tailTrace_1429210 : CollatzResearch.WordTrace tailWord_1429210 prefixEnd_1429210 244623895404152814334063 := by
  unfold tailWord_1429210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13031892788055933620035271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34751714101482489653427389 13031892788055933620035271)
  ·
    refine ⟨19547839182083900430052907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13031892788055933620035271 19547839182083900430052907)
    ·
      refine ⟨29321758773125850645079361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19547839182083900430052907 29321758773125850645079361)
      ·
        refine ⟨21991319079844387983809521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29321758773125850645079361 21991319079844387983809521)
        ·
          refine ⟨16493489309883290987857141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21991319079844387983809521 16493489309883290987857141)
          ·
            refine ⟨1546264622801558530111607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16493489309883290987857141 1546264622801558530111607)
            ·
              refine ⟨2319396934202337795167411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546264622801558530111607 2319396934202337795167411)
              ·
                refine ⟨3479095401303506692751117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319396934202337795167411 3479095401303506692751117)
                ·
                  refine ⟨1304660775488815009781669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3479095401303506692751117 1304660775488815009781669)
                  ·
                    refine ⟨244623895404152814334063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1304660775488815009781669 244623895404152814334063)
                    ·
                      rfl

theorem cell23_1429210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_1429210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429210 prefixEnd_1429210 := by exact prefixLift 1429210
  have htrace : WordTrace (prefixWord ++ tailWord_1429210) baseStart_1429210 baseEnd_1429210 := by
    simpa [prefixWord, tailWord_1429210, baseEnd_1429210] using wordTrace_append hprefix tailTrace_1429210
  have hstable : (prefixWord ++ tailWord_1429210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429210).length < 2 ^ (prefixWord ++ tailWord_1429210).sum := by decide
  have hdescent : baseEnd_1429210 < baseStart_1429210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429226 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1429226 : Nat := 118140960795 + 1429226 * 2 ^ 59
def prefixEnd_1429226 : Nat := 4983230072969 + 3 ^ 40 * 1429226 * 2
def baseEnd_1429226 : Nat := 733879901902930380402115

theorem tailTrace_1429226 : CollatzResearch.WordTrace tailWord_1429226 prefixEnd_1429226 733879901902930380402115 := by
  unfold tailWord_1429226
  simp only [CollatzResearch.WordTrace]
  refine ⟨13032038680041442303180883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34752103146777179475149021 13032038680041442303180883)
  ·
    refine ⟨19548058020062163454771325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13032038680041442303180883 19548058020062163454771325)
    ·
      refine ⟨7330521757523311295539247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19548058020062163454771325 7330521757523311295539247)
      ·
        refine ⟨10995782636284966943308871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7330521757523311295539247 10995782636284966943308871)
        ·
          refine ⟨16493673954427450414963307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10995782636284966943308871 16493673954427450414963307)
          ·
            refine ⟨24740510931641175622444961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16493673954427450414963307 24740510931641175622444961)
            ·
              refine ⟨18555383198730881716833721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24740510931641175622444961 18555383198730881716833721)
              ·
                refine ⟨13916537399048161287625291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18555383198730881716833721 13916537399048161287625291)
                ·
                  refine ⟨20874806098572241931437937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13916537399048161287625291 20874806098572241931437937)
                  ·
                    refine ⟨15656104573929181448578453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20874806098572241931437937 15656104573929181448578453)
                    ·
                      refine ⟨733879901902930380402115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15656104573929181448578453 733879901902930380402115)
                      ·
                        rfl

theorem cell23_1429226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1429226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429226 prefixEnd_1429226 := by exact prefixLift 1429226
  have htrace : WordTrace (prefixWord ++ tailWord_1429226) baseStart_1429226 baseEnd_1429226 := by
    simpa [prefixWord, tailWord_1429226, baseEnd_1429226] using wordTrace_append hprefix tailTrace_1429226
  have hstable : (prefixWord ++ tailWord_1429226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429226).length < 2 ^ (prefixWord ++ tailWord_1429226).sum := by decide
  have hdescent : baseEnd_1429226 < baseStart_1429226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429260 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 2, 3, 2]
def baseStart_1429260 : Nat := 118140960795 + 1429260 * 2 ^ 59
def prefixEnd_1429260 : Nat := 4983230072969 + 3 ^ 40 * 1429260 * 2
def baseEnd_1429260 : Nat := 733897360245183247376959

theorem tailTrace_1429260 : CollatzResearch.WordTrace tailWord_1429260 prefixEnd_1429260 733897360245183247376959 := by
  unfold tailWord_1429260
  simp only [CollatzResearch.WordTrace]
  refine ⟨26064697401021296509730617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34752929868028395346307489 26064697401021296509730617)
  ·
    refine ⟨19548523050765972382297963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26064697401021296509730617 19548523050765972382297963)
    ·
      refine ⟨29322784576148958573446945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19548523050765972382297963 29322784576148958573446945)
      ·
        refine ⟨21992088432111718930085209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29322784576148958573446945 21992088432111718930085209)
        ·
          refine ⟨16494066324083789197563907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21992088432111718930085209 16494066324083789197563907)
          ·
            refine ⟨24741099486125683796345861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16494066324083789197563907 24741099486125683796345861)
            ·
              refine ⟨4638956153648565711814849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24741099486125683796345861 4638956153648565711814849)
              ·
                refine ⟨3479217115236424283861137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4638956153648565711814849 3479217115236424283861137)
                ·
                  refine ⟨2609412836427318212895853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3479217115236424283861137 2609412836427318212895853)
                  ·
                    refine ⟨978529813660244329835945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609412836427318212895853 978529813660244329835945)
                    ·
                      refine ⟨733897360245183247376959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978529813660244329835945 733897360245183247376959)
                      ·
                        rfl

theorem cell23_1429260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_1429260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429260 prefixEnd_1429260 := by exact prefixLift 1429260
  have htrace : WordTrace (prefixWord ++ tailWord_1429260) baseStart_1429260 baseEnd_1429260 := by
    simpa [prefixWord, tailWord_1429260, baseEnd_1429260] using wordTrace_append hprefix tailTrace_1429260
  have hstable : (prefixWord ++ tailWord_1429260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429260).length < 2 ^ (prefixWord ++ tailWord_1429260).sum := by decide
  have hdescent : baseEnd_1429260 < baseStart_1429260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429300 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1429300 : Nat := 118140960795 + 1429300 * 2 ^ 59
def prefixEnd_1429300 : Nat := 4983230072969 + 3 ^ 40 * 1429300 * 2
def baseEnd_1429300 : Nat := 244639299823787696958925

theorem tailTrace_1429300 : CollatzResearch.WordTrace tailWord_1429300 prefixEnd_1429300 244639299823787696958925 := by
  unfold tailWord_1429300
  simp only [CollatzResearch.WordTrace]
  refine ⟨26065426860948839925458677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34753902481265119900611569 26065426860948839925458677)
  ·
    refine ⟨2443633768213953743011751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26065426860948839925458677 2443633768213953743011751)
    ·
      refine ⟨3665450652320930614517627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443633768213953743011751 3665450652320930614517627)
      ·
        refine ⟨5498175978481395921776441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665450652320930614517627 5498175978481395921776441)
        ·
          refine ⟨4123631983861046941332331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5498175978481395921776441 4123631983861046941332331)
          ·
            refine ⟨6185447975791570411998497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123631983861046941332331 6185447975791570411998497)
            ·
              refine ⟨4639085981843677808998873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6185447975791570411998497 4639085981843677808998873)
              ·
                refine ⟨3479314486382758356749155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4639085981843677808998873 3479314486382758356749155)
                ·
                  refine ⟨5218971729574137535123733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479314486382758356749155 5218971729574137535123733)
                  ·
                    refine ⟨244639299823787696958925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5218971729574137535123733 244639299823787696958925)
                    ·
                      rfl

theorem cell23_1429300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1429300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429300 prefixEnd_1429300 := by exact prefixLift 1429300
  have htrace : WordTrace (prefixWord ++ tailWord_1429300) baseStart_1429300 baseEnd_1429300 := by
    simpa [prefixWord, tailWord_1429300, baseEnd_1429300] using wordTrace_append hprefix tailTrace_1429300
  have hstable : (prefixWord ++ tailWord_1429300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429300).length < 2 ^ (prefixWord ++ tailWord_1429300).sum := by decide
  have hdescent : baseEnd_1429300 < baseStart_1429300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429324 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 3, 2, 2]
def baseStart_1429324 : Nat := 118140960795 + 1429324 * 2 ^ 59
def prefixEnd_1429324 : Nat := 4983230072969 + 3 ^ 40 * 1429324 * 2
def baseEnd_1429324 : Nat := 733930223007070996976665

theorem tailTrace_1429324 : CollatzResearch.WordTrace tailWord_1429324 prefixEnd_1429324 733930223007070996976665 := by
  unfold tailWord_1429324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26065864536905365974895513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34754486049207154633194017 26065864536905365974895513)
  ·
    refine ⟨19549398402679024481171635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26065864536905365974895513 19549398402679024481171635)
    ·
      refine ⟨29324097604018536721757453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19549398402679024481171635 29324097604018536721757453)
      ·
        refine ⟨10996536601506951270659045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29324097604018536721757453 10996536601506951270659045)
        ·
          refine ⟨2061850612782553363248571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10996536601506951270659045 2061850612782553363248571)
          ·
            refine ⟨3092775919173830044872857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061850612782553363248571 3092775919173830044872857)
            ·
              refine ⟨2319581939380372533654643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3092775919173830044872857 2319581939380372533654643)
              ·
                refine ⟨3479372909070558800481965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319581939380372533654643 3479372909070558800481965)
                ·
                  refine ⟨1304764840901459550180737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3479372909070558800481965 1304764840901459550180737)
                  ·
                    refine ⟨978573630676094662635553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1304764840901459550180737 978573630676094662635553)
                    ·
                      refine ⟨733930223007070996976665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978573630676094662635553 733930223007070996976665)
                      ·
                        rfl

theorem cell23_1429324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_1429324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429324 prefixEnd_1429324 := by exact prefixLift 1429324
  have htrace : WordTrace (prefixWord ++ tailWord_1429324) baseStart_1429324 baseEnd_1429324 := by
    simpa [prefixWord, tailWord_1429324, baseEnd_1429324] using wordTrace_append hprefix tailTrace_1429324
  have hstable : (prefixWord ++ tailWord_1429324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429324).length < 2 ^ (prefixWord ++ tailWord_1429324).sum := by decide
  have hdescent : baseEnd_1429324 < baseStart_1429324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429347 : List Nat := [1, 1, 1, 5, 5, 1, 2, 7]
def baseStart_1429347 : Nat := 118140960795 + 1429347 * 2 ^ 59
def prefixEnd_1429347 : Nat := 4983230072969 + 3 ^ 40 * 1429347 * 2
def baseEnd_1429347 : Nat := 27183038261560163221817

theorem tailTrace_1429347 : CollatzResearch.WordTrace tailWord_1429347 prefixEnd_1429347 27183038261560163221817 := by
  unfold tailWord_1429347
  simp only [CollatzResearch.WordTrace]
  refine ⟨52132567952727406877878295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34755045301818271251918863 52132567952727406877878295)
  ·
    refine ⟨78198851929091110316817443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52132567952727406877878295 78198851929091110316817443)
    ·
      refine ⟨117298277893636665475226165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78198851929091110316817443 117298277893636665475226165)
      ·
        refine ⟨10996713552528437388302453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117298277893636665475226165 10996713552528437388302453)
        ·
          refine ⟨1030941895549541005153355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10996713552528437388302453 1030941895549541005153355)
          ·
            refine ⟨1546412843324311507730033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030941895549541005153355 1546412843324311507730033)
            ·
              refine ⟨1159809632493233630797525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546412843324311507730033 1159809632493233630797525)
              ·
                refine ⟨27183038261560163221817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1159809632493233630797525 27183038261560163221817)
                ·
                  rfl

theorem cell23_1429347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 7].length) (baseStart_1429347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429347 prefixEnd_1429347 := by exact prefixLift 1429347
  have htrace : WordTrace (prefixWord ++ tailWord_1429347) baseStart_1429347 baseEnd_1429347 := by
    simpa [prefixWord, tailWord_1429347, baseEnd_1429347] using wordTrace_append hprefix tailTrace_1429347
  have hstable : (prefixWord ++ tailWord_1429347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429347).length < 2 ^ (prefixWord ++ tailWord_1429347).sum := by decide
  have hdescent : baseEnd_1429347 < baseStart_1429347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429358 : List Nat := [4, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_1429358 : Nat := 118140960795 + 1429358 * 2 ^ 59
def prefixEnd_1429358 : Nat := 4983230072969 + 3 ^ 40 * 1429358 * 2
def baseEnd_1429358 : Nat := 733947681349323863951509

theorem tailTrace_1429358 : CollatzResearch.WordTrace tailWord_1429358 prefixEnd_1429358 733947681349323863951509 := by
  unfold tailWord_1429358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6516621144460944469566091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34755312770458370504352485 6516621144460944469566091)
  ·
    refine ⟨9774931716691416704349137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6516621144460944469566091 9774931716691416704349137)
    ·
      refine ⟨7331198787518562528261853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9774931716691416704349137 7331198787518562528261853)
      ·
        refine ⟨2749199545319460948098195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7331198787518562528261853 2749199545319460948098195)
        ·
          refine ⟨4123799317979191422147293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749199545319460948098195 4123799317979191422147293)
          ·
            refine ⟨1546424744242196783305235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4123799317979191422147293 1546424744242196783305235)
            ·
              refine ⟨2319637116363295174957853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546424744242196783305235 2319637116363295174957853)
              ·
                refine ⟨869863918636235690609195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2319637116363295174957853 869863918636235690609195)
                ·
                  refine ⟨1304795877954353535913793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869863918636235690609195 1304795877954353535913793)
                  ·
                    refine ⟨978596908465765151935345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1304795877954353535913793 978596908465765151935345)
                    ·
                      refine ⟨733947681349323863951509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978596908465765151935345 733947681349323863951509)
                      ·
                        rfl

theorem cell23_1429358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_1429358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429358 prefixEnd_1429358 := by exact prefixLift 1429358
  have htrace : WordTrace (prefixWord ++ tailWord_1429358) baseStart_1429358 baseEnd_1429358 := by
    simpa [prefixWord, tailWord_1429358, baseEnd_1429358] using wordTrace_append hprefix tailTrace_1429358
  have hstable : (prefixWord ++ tailWord_1429358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429358).length < 2 ^ (prefixWord ++ tailWord_1429358).sum := by decide
  have hdescent : baseEnd_1429358 < baseStart_1429358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429374 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1429374 : Nat := 118140960795 + 1429374 * 2 ^ 59
def prefixEnd_1429374 : Nat := 4983230072969 + 3 ^ 40 * 1429374 * 2
def baseEnd_1429374 : Nat := 733955897039795801351435

theorem tailTrace_1429374 : CollatzResearch.WordTrace tailWord_1429374 prefixEnd_1429374 733955897039795801351435 := by
  unfold tailWord_1429374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6516694090453698811138897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34755701815753060326074117 6516694090453698811138897)
  ·
    refine ⟨4887520567840274108354173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6516694090453698811138897 4887520567840274108354173)
    ·
      refine ⟨1832820212940102790632815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4887520567840274108354173 1832820212940102790632815)
      ·
        refine ⟨2749230319410154185949223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1832820212940102790632815 2749230319410154185949223)
        ·
          refine ⟨4123845479115231278923835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749230319410154185949223 4123845479115231278923835)
          ·
            refine ⟨6185768218672846918385753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123845479115231278923835 6185768218672846918385753)
            ·
              refine ⟨4639326164004635188789315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6185768218672846918385753 4639326164004635188789315)
              ·
                refine ⟨6958989246006952783183973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639326164004635188789315 6958989246006952783183973)
                ·
                  refine ⟨1304810483626303646846995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6958989246006952783183973 1304810483626303646846995)
                  ·
                    refine ⟨1957215725439455470270493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1304810483626303646846995 1957215725439455470270493)
                    ·
                      refine ⟨733955897039795801351435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1957215725439455470270493 733955897039795801351435)
                      ·
                        rfl

theorem cell23_1429374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1429374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429374 prefixEnd_1429374 := by exact prefixLift 1429374
  have htrace : WordTrace (prefixWord ++ tailWord_1429374) baseStart_1429374 baseEnd_1429374 := by
    simpa [prefixWord, tailWord_1429374, baseEnd_1429374] using wordTrace_append hprefix tailTrace_1429374
  have hstable : (prefixWord ++ tailWord_1429374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429374).length < 2 ^ (prefixWord ++ tailWord_1429374).sum := by decide
  have hdescent : baseEnd_1429374 < baseStart_1429374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429393 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_1429393 : Nat := 118140960795 + 1429393 * 2 ^ 59
def prefixEnd_1429393 : Nat := 4983230072969 + 3 ^ 40 * 1429393 * 2
def baseEnd_1429393 : Nat := 733965653172231227013847

theorem tailTrace_1429393 : CollatzResearch.WordTrace tailWord_1429393 prefixEnd_1429393 733965653172231227013847 := by
  unfold tailWord_1429393
  simp only [CollatzResearch.WordTrace]
  refine ⟨52134245710560756734052833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34756163807040504489368555 52134245710560756734052833)
  ·
    refine ⟨39100684282920567550539625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52134245710560756734052833 39100684282920567550539625)
    ·
      refine ⟨29325513212190425662904719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39100684282920567550539625 29325513212190425662904719)
      ·
        refine ⟨43988269818285638494357079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29325513212190425662904719 43988269818285638494357079)
        ·
          refine ⟨65982404727428457741535619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43988269818285638494357079 65982404727428457741535619)
          ·
            refine ⟨98973607091142686612303429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65982404727428457741535619 98973607091142686612303429)
            ·
              refine ⟨18557551329589253739806893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98973607091142686612303429 18557551329589253739806893)
              ·
                refine ⟨6959081748595970152427585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18557551329589253739806893 6959081748595970152427585)
                ·
                  refine ⟨5219311311446977614320689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6959081748595970152427585 5219311311446977614320689)
                  ·
                    refine ⟨3914483483585233210740517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5219311311446977614320689 3914483483585233210740517)
                    ·
                      refine ⟨733965653172231227013847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3914483483585233210740517 733965653172231227013847)
                      ·
                        rfl

theorem cell23_1429393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_1429393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429393 prefixEnd_1429393 := by exact prefixLift 1429393
  have htrace : WordTrace (prefixWord ++ tailWord_1429393) baseStart_1429393 baseEnd_1429393 := by
    simpa [prefixWord, tailWord_1429393, baseEnd_1429393] using wordTrace_append hprefix tailTrace_1429393
  have hstable : (prefixWord ++ tailWord_1429393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429393).length < 2 ^ (prefixWord ++ tailWord_1429393).sum := by decide
  have hdescent : baseEnd_1429393 < baseStart_1429393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429437 : List Nat := [1, 4, 1, 2, 3, 2, 1, 4, 5]
def baseStart_1429437 : Nat := 118140960795 + 1429437 * 2 ^ 59
def prefixEnd_1429437 : Nat := 4983230072969 + 3 ^ 40 * 1429437 * 2
def baseEnd_1429437 : Nat := 81554249591225450540405

theorem tailTrace_1429437 : CollatzResearch.WordTrace tailWord_1429437 prefixEnd_1429437 81554249591225450540405 := by
  unfold tailWord_1429437
  simp only [CollatzResearch.WordTrace]
  refine ⟨52135850522401352248654565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34757233681600901499103043 52135850522401352248654565)
  ·
    refine ⟨9775471972950253546622731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52135850522401352248654565 9775471972950253546622731)
    ·
      refine ⟨14663207959425380319934097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9775471972950253546622731 14663207959425380319934097)
      ·
        refine ⟨10997405969569035239950573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14663207959425380319934097 10997405969569035239950573)
        ·
          refine ⟨4124027238588388214981465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10997405969569035239950573 4124027238588388214981465)
          ·
            refine ⟨3093020428941291161236099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4124027238588388214981465 3093020428941291161236099)
            ·
              refine ⟨4639530643411936741854149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093020428941291161236099 4639530643411936741854149)
              ·
                refine ⟨869911995639738139097653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4639530643411936741854149 869911995639738139097653)
                ·
                  refine ⟨81554249591225450540405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 869911995639738139097653 81554249591225450540405)
                  ·
                    rfl

theorem cell23_1429437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_1429437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429437 prefixEnd_1429437 := by exact prefixLift 1429437
  have htrace : WordTrace (prefixWord ++ tailWord_1429437) baseStart_1429437 baseEnd_1429437 := by
    simpa [prefixWord, tailWord_1429437, baseEnd_1429437] using wordTrace_append hprefix tailTrace_1429437
  have hstable : (prefixWord ++ tailWord_1429437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429437).length < 2 ^ (prefixWord ++ tailWord_1429437).sum := by decide
  have hdescent : baseEnd_1429437 < baseStart_1429437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429440 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 1, 7, 2]
def baseStart_1429440 : Nat := 118140960795 + 1429440 * 2 ^ 59
def prefixEnd_1429440 : Nat := 4983230072969 + 3 ^ 40 * 1429440 * 2
def baseEnd_1429440 : Nat := 733989786762992543126131

theorem tailTrace_1429440 : CollatzResearch.WordTrace tailWord_1429440 prefixEnd_1429440 733989786762992543126131 := by
  unfold tailWord_1429440
  simp only [CollatzResearch.WordTrace]
  refine ⟨26067979970695241880506887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34757306627593655840675849 26067979970695241880506887)
  ·
    refine ⟨39101969956042862820760331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26067979970695241880506887 39101969956042862820760331)
    ·
      refine ⟨58652954934064294231140497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39101969956042862820760331 58652954934064294231140497)
      ·
        refine ⟨43989716200548220673355373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58652954934064294231140497 43989716200548220673355373)
        ·
          refine ⟨16496143575205582752508265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43989716200548220673355373 16496143575205582752508265)
          ·
            refine ⟨12372107681404187064381199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16496143575205582752508265 12372107681404187064381199)
            ·
              refine ⟨18558161522106280596571799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12372107681404187064381199 18558161522106280596571799)
              ·
                refine ⟨27837242283159420894857699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18558161522106280596571799 27837242283159420894857699)
                ·
                  refine ⟨41755863424739131342286549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27837242283159420894857699 41755863424739131342286549)
                  ·
                    refine ⟨978653049017323390834841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41755863424739131342286549 978653049017323390834841)
                    ·
                      refine ⟨733989786762992543126131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978653049017323390834841 733989786762992543126131)
                      ·
                        rfl

theorem cell23_1429440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_1429440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429440 prefixEnd_1429440 := by exact prefixLift 1429440
  have htrace : WordTrace (prefixWord ++ tailWord_1429440) baseStart_1429440 baseEnd_1429440 := by
    simpa [prefixWord, tailWord_1429440, baseEnd_1429440] using wordTrace_append hprefix tailTrace_1429440
  have hstable : (prefixWord ++ tailWord_1429440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429440).length < 2 ^ (prefixWord ++ tailWord_1429440).sum := by decide
  have hdescent : baseEnd_1429440 < baseStart_1429440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429480 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1429480 : Nat := 118140960795 + 1429480 * 2 ^ 59
def prefixEnd_1429480 : Nat := 4983230072969 + 3 ^ 40 * 1429480 * 2
def baseEnd_1429480 : Nat := 244670108663057462208649

theorem tailTrace_1429480 : CollatzResearch.WordTrace tailWord_1429480 prefixEnd_1429480 244670108663057462208649 := by
  unfold tailWord_1429480
  simp only [CollatzResearch.WordTrace]
  refine ⟨26068709430622785296234947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34758279240830380394979929 26068709430622785296234947)
  ·
    refine ⟨39103064145934177944352421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26068709430622785296234947 39103064145934177944352421)
    ·
      refine ⟨7331824527362658364566079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39103064145934177944352421 7331824527362658364566079)
      ·
        refine ⟨10997736791043987546849119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7331824527362658364566079 10997736791043987546849119)
        ·
          refine ⟨16496605186565981320273679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10997736791043987546849119 16496605186565981320273679)
          ·
            refine ⟨24744907779848971980410519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16496605186565981320273679 24744907779848971980410519)
            ·
              refine ⟨37117361669773457970615779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24744907779848971980410519 37117361669773457970615779)
              ·
                refine ⟨55676042504660186955923669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37117361669773457970615779 55676042504660186955923669)
                ·
                  refine ⟨1304907246202973131779461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 55676042504660186955923669 1304907246202973131779461)
                  ·
                    refine ⟨244670108663057462208649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1304907246202973131779461 244670108663057462208649)
                    ·
                      rfl

theorem cell23_1429480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1429480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429480 prefixEnd_1429480 := by exact prefixLift 1429480
  have htrace : WordTrace (prefixWord ++ tailWord_1429480) baseStart_1429480 baseEnd_1429480 := by
    simpa [prefixWord, tailWord_1429480, baseEnd_1429480] using wordTrace_append hprefix tailTrace_1429480
  have hstable : (prefixWord ++ tailWord_1429480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429480).length < 2 ^ (prefixWord ++ tailWord_1429480).sum := by decide
  have hdescent : baseEnd_1429480 < baseStart_1429480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429483 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 4]
def baseStart_1429483 : Nat := 118140960795 + 1429483 * 2 ^ 59
def prefixEnd_1429483 : Nat := 4983230072969 + 3 ^ 40 * 1429483 * 2
def baseEnd_1429483 : Nat := 734011866431135874888433

theorem tailTrace_1429483 : CollatzResearch.WordTrace tailWord_1429483 prefixEnd_1429483 734011866431135874888433 := by
  unfold tailWord_1429483
  simp only [CollatzResearch.WordTrace]
  refine ⟨52137528280234702104829103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34758352186823134736552735 52137528280234702104829103)
  ·
    refine ⟨78206292420352053157243655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52137528280234702104829103 78206292420352053157243655)
    ·
      refine ⟨117309438630528079735865483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78206292420352053157243655 117309438630528079735865483)
      ·
        refine ⟨175964157945792119603798225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117309438630528079735865483 175964157945792119603798225)
        ·
          refine ⟨131973118459344089702848669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175964157945792119603798225 131973118459344089702848669)
          ·
            refine ⟨49489919422254033638568251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131973118459344089702848669 49489919422254033638568251)
            ·
              refine ⟨74234879133381050457852377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49489919422254033638568251 74234879133381050457852377)
              ·
                refine ⟨55676159350035787843389283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74234879133381050457852377 55676159350035787843389283)
                ·
                  refine ⟨83514239025053681765083925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55676159350035787843389283 83514239025053681765083925)
                  ·
                    refine ⟨3914729954299391332738309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83514239025053681765083925 3914729954299391332738309)
                    ·
                      refine ⟨734011866431135874888433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3914729954299391332738309 734011866431135874888433)
                      ·
                        rfl

theorem cell23_1429483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 4].length) (baseStart_1429483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429483 prefixEnd_1429483 := by exact prefixLift 1429483
  have htrace : WordTrace (prefixWord ++ tailWord_1429483) baseStart_1429483 baseEnd_1429483 := by
    simpa [prefixWord, tailWord_1429483, baseEnd_1429483] using wordTrace_append hprefix tailTrace_1429483
  have hstable : (prefixWord ++ tailWord_1429483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429483).length < 2 ^ (prefixWord ++ tailWord_1429483).sum := by decide
  have hdescent : baseEnd_1429483 < baseStart_1429483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429497 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 3, 4]
def baseStart_1429497 : Nat := 118140960795 + 1429497 * 2 ^ 59
def prefixEnd_1429497 : Nat := 4983230072969 + 3 ^ 40 * 1429497 * 2
def baseEnd_1429497 : Nat := 244673018386766273371123

theorem tailTrace_1429497 : CollatzResearch.WordTrace tailWord_1429497 prefixEnd_1429497 244673018386766273371123 := by
  unfold tailWord_1429497
  simp only [CollatzResearch.WordTrace]
  refine ⟨52138038902183982495838745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34758692601455988330559163 52138038902183982495838745)
  ·
    refine ⟨39103529176637986871879059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52138038902183982495838745 39103529176637986871879059)
    ·
      refine ⟨58655293764956980307818589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39103529176637986871879059 58655293764956980307818589)
      ·
        refine ⟨21995735161858867615431971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58655293764956980307818589 21995735161858867615431971)
        ·
          refine ⟨32993602742788301423147957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21995735161858867615431971 32993602742788301423147957)
          ·
            refine ⟨3093150257136403258420121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32993602742788301423147957 3093150257136403258420121)
            ·
              refine ⟨2319862692852302443815091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3093150257136403258420121 2319862692852302443815091)
              ·
                refine ⟨3479794039278453665722637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319862692852302443815091 3479794039278453665722637)
                ·
                  refine ⟨1304922764729420124645989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3479794039278453665722637 1304922764729420124645989)
                  ·
                    refine ⟨244673018386766273371123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1304922764729420124645989 244673018386766273371123)
                    ·
                      rfl

theorem cell23_1429497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 4].length) (baseStart_1429497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429497 prefixEnd_1429497 := by exact prefixLift 1429497
  have htrace : WordTrace (prefixWord ++ tailWord_1429497) baseStart_1429497 baseEnd_1429497 := by
    simpa [prefixWord, tailWord_1429497, baseEnd_1429497] using wordTrace_append hprefix tailTrace_1429497
  have hstable : (prefixWord ++ tailWord_1429497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429497).length < 2 ^ (prefixWord ++ tailWord_1429497).sum := by decide
  have hdescent : baseEnd_1429497 < baseStart_1429497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429554 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_1429554 : Nat := 118140960795 + 1429554 * 2 ^ 59
def prefixEnd_1429554 : Nat := 4983230072969 + 3 ^ 40 * 1429554 * 2
def baseEnd_1429554 : Nat := 734048323557605097100607

theorem tailTrace_1429554 : CollatzResearch.WordTrace tailWord_1429554 prefixEnd_1429554 734048323557605097100607 := by
  unfold tailWord_1429554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13035029465744370307665929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34760078575318320820442477 13035029465744370307665929)
  ·
    refine ⟨9776272099308277730749447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13035029465744370307665929 9776272099308277730749447)
    ·
      refine ⟨14664408148962416596124171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9776272099308277730749447 14664408148962416596124171)
      ·
        refine ⟨21996612223443624894186257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14664408148962416596124171 21996612223443624894186257)
        ·
          refine ⟨16497459167582718670639693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21996612223443624894186257 16497459167582718670639693)
          ·
            refine ⟨6186547187843519501489885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16497459167582718670639693 6186547187843519501489885)
            ·
              refine ⟨2319955195441319813058707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6186547187843519501489885 2319955195441319813058707)
              ·
                refine ⟨3479932793161979719588061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319955195441319813058707 3479932793161979719588061)
                ·
                  refine ⟨1304974797435742394845523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3479932793161979719588061 1304974797435742394845523)
                  ·
                    refine ⟨1957462196153613592268285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1304974797435742394845523 1957462196153613592268285)
                    ·
                      refine ⟨734048323557605097100607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1957462196153613592268285 734048323557605097100607)
                      ·
                        rfl

theorem cell23_1429554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_1429554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429554 prefixEnd_1429554 := by exact prefixLift 1429554
  have htrace : WordTrace (prefixWord ++ tailWord_1429554) baseStart_1429554 baseEnd_1429554 := by
    simpa [prefixWord, tailWord_1429554, baseEnd_1429554] using wordTrace_append hprefix tailTrace_1429554
  have hstable : (prefixWord ++ tailWord_1429554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429554).length < 2 ^ (prefixWord ++ tailWord_1429554).sum := by decide
  have hdescent : baseEnd_1429554 < baseStart_1429554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429561 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 6]
def baseStart_1429561 : Nat := 118140960795 + 1429561 * 2 ^ 59
def prefixEnd_1429561 : Nat := 4983230072969 + 3 ^ 40 * 1429561 * 2
def baseEnd_1429561 : Nat := 81561324213576285523675

theorem tailTrace_1429561 : CollatzResearch.WordTrace tailWord_1429561 prefixEnd_1429561 81561324213576285523675 := by
  unfold tailWord_1429561
  simp only [CollatzResearch.WordTrace]
  refine ⟨52140373173952121426168537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34760248782634747617445691 52140373173952121426168537)
  ·
    refine ⟨39105279880464091069626403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52140373173952121426168537 39105279880464091069626403)
    ·
      refine ⟨58657919820696136604439605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39105279880464091069626403 58657919820696136604439605)
      ·
        refine ⟨5499179983190262806666213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58657919820696136604439605 5499179983190262806666213)
        ·
          refine ⟨1031096246848174276249915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5499179983190262806666213 1031096246848174276249915)
          ·
            refine ⟨1546644370272261414374873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031096246848174276249915 1546644370272261414374873)
            ·
              refine ⟨1159983277704196060781155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546644370272261414374873 1159983277704196060781155)
              ·
                refine ⟨1739974916556294091171733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159983277704196060781155 1739974916556294091171733)
                ·
                  refine ⟨81561324213576285523675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1739974916556294091171733 81561324213576285523675)
                  ·
                    rfl

theorem cell23_1429561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 6].length) (baseStart_1429561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429561 prefixEnd_1429561 := by exact prefixLift 1429561
  have htrace : WordTrace (prefixWord ++ tailWord_1429561) baseStart_1429561 baseEnd_1429561 := by
    simpa [prefixWord, tailWord_1429561, baseEnd_1429561] using wordTrace_append hprefix tailTrace_1429561
  have hstable : (prefixWord ++ tailWord_1429561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429561).length < 2 ^ (prefixWord ++ tailWord_1429561).sum := by decide
  have hdescent : baseEnd_1429561 < baseStart_1429561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429574 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1429574 : Nat := 118140960795 + 1429574 * 2 ^ 59
def prefixEnd_1429574 : Nat := 4983230072969 + 3 ^ 40 * 1429574 * 2
def baseEnd_1429574 : Nat := 244686197723565006283505

theorem tailTrace_1429574 : CollatzResearch.WordTrace tailWord_1429574 prefixEnd_1429574 244686197723565006283505 := by
  unfold tailWord_1429574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629401478840782020199743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34760564881936683097594517 1629401478840782020199743)
  ·
    refine ⟨2444102218261173030299615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1629401478840782020199743 2444102218261173030299615)
    ·
      refine ⟨3666153327391759545449423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2444102218261173030299615 3666153327391759545449423)
      ·
        refine ⟨5499229991087639318174135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3666153327391759545449423 5499229991087639318174135)
        ·
          refine ⟨8248844986631458977261203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5499229991087639318174135 8248844986631458977261203)
          ·
            refine ⟨12373267479947188465891805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8248844986631458977261203 12373267479947188465891805)
            ·
              refine ⟨4639975304980195674709427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12373267479947188465891805 4639975304980195674709427)
              ·
                refine ⟨6959962957470293512064141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639975304980195674709427 6959962957470293512064141)
                ·
                  refine ⟨2609986109051360067024053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6959962957470293512064141 2609986109051360067024053)
                  ·
                    refine ⟨244686197723565006283505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2609986109051360067024053 244686197723565006283505)
                    ·
                      rfl

theorem cell23_1429574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1429574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429574 prefixEnd_1429574 := by exact prefixLift 1429574
  have htrace : WordTrace (prefixWord ++ tailWord_1429574) baseStart_1429574 baseEnd_1429574 := by
    simpa [prefixWord, tailWord_1429574, baseEnd_1429574] using wordTrace_append hprefix tailTrace_1429574
  have hstable : (prefixWord ++ tailWord_1429574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429574).length < 2 ^ (prefixWord ++ tailWord_1429574).sum := by decide
  have hdescent : baseEnd_1429574 < baseStart_1429574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429580 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1429580 : Nat := 118140960795 + 1429580 * 2 ^ 59
def prefixEnd_1429580 : Nat := 4983230072969 + 3 ^ 40 * 1429580 * 2
def baseEnd_1429580 : Nat := 734061674054621995375487

theorem tailTrace_1429580 : CollatzResearch.WordTrace tailWord_1429580 prefixEnd_1429580 734061674054621995375487 := by
  unfold tailWord_1429580
  simp only [CollatzResearch.WordTrace]
  refine ⟨26070533080441643835555097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34760710773922191780740129 26070533080441643835555097)
  ·
    refine ⟨19552899810331232876666323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26070533080441643835555097 19552899810331232876666323)
    ·
      refine ⟨29329349715496849314999485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19552899810331232876666323 29329349715496849314999485)
      ·
        refine ⟨10998506143311318493124807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29329349715496849314999485 10998506143311318493124807)
        ·
          refine ⟨16497759214966977739687211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10998506143311318493124807 16497759214966977739687211)
          ·
            refine ⟨24746638822450466609530817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16497759214966977739687211 24746638822450466609530817)
            ·
              refine ⟨18559979116837849957148113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24746638822450466609530817 18559979116837849957148113)
              ·
                refine ⟨13919984337628387467861085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18559979116837849957148113 13919984337628387467861085)
                ·
                  refine ⟨5219994126610645300447907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13919984337628387467861085 5219994126610645300447907)
                  ·
                    refine ⟨7829991189915967950671861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5219994126610645300447907 7829991189915967950671861)
                    ·
                      refine ⟨734061674054621995375487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7829991189915967950671861 734061674054621995375487)
                      ·
                        rfl

theorem cell23_1429580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1429580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429580 prefixEnd_1429580 := by exact prefixLift 1429580
  have htrace : WordTrace (prefixWord ++ tailWord_1429580) baseStart_1429580 baseEnd_1429580 := by
    simpa [prefixWord, tailWord_1429580, baseEnd_1429580] using wordTrace_append hprefix tailTrace_1429580
  have hstable : (prefixWord ++ tailWord_1429580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429580).length < 2 ^ (prefixWord ++ tailWord_1429580).sum := by decide
  have hdescent : baseEnd_1429580 < baseStart_1429580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429581 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_1429581 : Nat := 118140960795 + 1429581 * 2 ^ 59
def prefixEnd_1429581 : Nat := 4983230072969 + 3 ^ 40 * 1429581 * 2
def baseEnd_1429581 : Nat := 734062187535276491462983

theorem tailTrace_1429581 : CollatzResearch.WordTrace tailWord_1429581 prefixEnd_1429581 734062187535276491462983 := by
  unfold tailWord_1429581
  simp only [CollatzResearch.WordTrace]
  refine ⟨52141102633879664841896597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34760735089253109894597731 52141102633879664841896597)
  ·
    refine ⟨2444114185963109289463903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52141102633879664841896597 2444114185963109289463903)
    ·
      refine ⟨3666171278944663934195855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2444114185963109289463903 3666171278944663934195855)
      ·
        refine ⟨5499256918416995901293783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3666171278944663934195855 5499256918416995901293783)
        ·
          refine ⟨8248885377625493851940675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5499256918416995901293783 8248885377625493851940675)
          ·
            refine ⟨12373328066438240777911013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8248885377625493851940675 12373328066438240777911013)
            ·
              refine ⟨2319999012457170145858315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12373328066438240777911013 2319999012457170145858315)
              ·
                refine ⟨3479998518685755218787473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319999012457170145858315 3479998518685755218787473)
                ·
                  refine ⟨2609998889014316414090605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3479998518685755218787473 2609998889014316414090605)
                  ·
                    refine ⟨978749583380368655283977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609998889014316414090605 978749583380368655283977)
                    ·
                      refine ⟨734062187535276491462983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978749583380368655283977 734062187535276491462983)
                      ·
                        rfl

theorem cell23_1429581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_1429581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429581 prefixEnd_1429581 := by exact prefixLift 1429581
  have htrace : WordTrace (prefixWord ++ tailWord_1429581) baseStart_1429581 baseEnd_1429581 := by
    simpa [prefixWord, tailWord_1429581, baseEnd_1429581] using wordTrace_append hprefix tailTrace_1429581
  have hstable : (prefixWord ++ tailWord_1429581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429581).length < 2 ^ (prefixWord ++ tailWord_1429581).sum := by decide
  have hdescent : baseEnd_1429581 < baseStart_1429581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429594 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4]
def baseStart_1429594 : Nat := 118140960795 + 1429594 * 2 ^ 59
def prefixEnd_1429594 : Nat := 4983230072969 + 3 ^ 40 * 1429594 * 2
def baseEnd_1429594 : Nat := 734068862783784940600423

theorem tailTrace_1429594 : CollatzResearch.WordTrace tailWord_1429594 prefixEnd_1429594 734068862783784940600423 := by
  unfold tailWord_1429594
  simp only [CollatzResearch.WordTrace]
  refine ⟨13035394195708142015529959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34761051188555045374746557 13035394195708142015529959)
  ·
    refine ⟨19553091293562213023294939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13035394195708142015529959 19553091293562213023294939)
    ·
      refine ⟨29329636940343319534942409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19553091293562213023294939 29329636940343319534942409)
      ·
        refine ⟨21997227705257489651206807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29329636940343319534942409 21997227705257489651206807)
        ·
          refine ⟨32995841557886234476810211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21997227705257489651206807 32995841557886234476810211)
          ·
            refine ⟨49493762336829351715215317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32995841557886234476810211 49493762336829351715215317)
            ·
              refine ⟨1160010054769437930825359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49493762336829351715215317 1160010054769437930825359)
              ·
                refine ⟨1740015082154156896238039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160010054769437930825359 1740015082154156896238039)
                ·
                  refine ⟨2610022623231235344357059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740015082154156896238039 2610022623231235344357059)
                  ·
                    refine ⟨3915033934846853016535589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2610022623231235344357059 3915033934846853016535589)
                    ·
                      refine ⟨734068862783784940600423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3915033934846853016535589 734068862783784940600423)
                      ·
                        rfl

theorem cell23_1429594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_1429594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429594 prefixEnd_1429594 := by exact prefixLift 1429594
  have htrace : WordTrace (prefixWord ++ tailWord_1429594) baseStart_1429594 baseEnd_1429594 := by
    simpa [prefixWord, tailWord_1429594, baseEnd_1429594] using wordTrace_append hprefix tailTrace_1429594
  have hstable : (prefixWord ++ tailWord_1429594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429594).length < 2 ^ (prefixWord ++ tailWord_1429594).sum := by decide
  have hdescent : baseEnd_1429594 < baseStart_1429594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429627 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 8, 1, 3]
def baseStart_1429627 : Nat := 118140960795 + 1429627 * 2 ^ 59
def prefixEnd_1429627 : Nat := 4983230072969 + 3 ^ 40 * 1429627 * 2
def baseEnd_1429627 : Nat := 734085807645383311487771

theorem tailTrace_1429627 : CollatzResearch.WordTrace tailWord_1429627 prefixEnd_1429627 734085807645383311487771 := by
  unfold tailWord_1429627
  simp only [CollatzResearch.WordTrace]
  refine ⟨52142780391713014698071135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34761853594475343132047423 52142780391713014698071135)
  ·
    refine ⟨78214170587569522047106703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52142780391713014698071135 78214170587569522047106703)
    ·
      refine ⟨117321255881354283070660055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78214170587569522047106703 117321255881354283070660055)
      ·
        refine ⟨175981883822031424605990083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117321255881354283070660055 175981883822031424605990083)
        ·
          refine ⟨263972825733047136908985125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175981883822031424605990083 263972825733047136908985125)
          ·
            refine ⟨49494904824946338170434711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263972825733047136908985125 49494904824946338170434711)
            ·
              refine ⟨74242357237419507255652067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49494904824946338170434711 74242357237419507255652067)
              ·
                refine ⟨111363535856129260883478101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74242357237419507255652067 111363535856129260883478101)
                ·
                  refine ⟨1305041435814014775978259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 111363535856129260883478101 1305041435814014775978259)
                  ·
                    refine ⟨1957562153721022163967389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1305041435814014775978259 1957562153721022163967389)
                    ·
                      refine ⟨734085807645383311487771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1957562153721022163967389 734085807645383311487771)
                      ·
                        rfl

theorem cell23_1429627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 1, 3].length) (baseStart_1429627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429627 prefixEnd_1429627 := by exact prefixLift 1429627
  have htrace : WordTrace (prefixWord ++ tailWord_1429627) baseStart_1429627 baseEnd_1429627 := by
    simpa [prefixWord, tailWord_1429627, baseEnd_1429627] using wordTrace_append hprefix tailTrace_1429627
  have hstable : (prefixWord ++ tailWord_1429627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429627).length < 2 ^ (prefixWord ++ tailWord_1429627).sum := by decide
  have hdescent : baseEnd_1429627 < baseStart_1429627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429661 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_1429661 : Nat := 118140960795 + 1429661 * 2 ^ 59
def prefixEnd_1429661 : Nat := 4983230072969 + 3 ^ 40 * 1429661 * 2
def baseEnd_1429661 : Nat := 734103265987636178462615

theorem tailTrace_1429661 : CollatzResearch.WordTrace tailWord_1429661 prefixEnd_1429661 734103265987636178462615 := by
  unfold tailWord_1429661
  simp only [CollatzResearch.WordTrace]
  refine ⟨52144020473589838504808837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34762680315726559003205891 52144020473589838504808837)
  ·
    refine ⟨9777003838798094719651657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52144020473589838504808837 9777003838798094719651657)
    ·
      refine ⟨7332752879098571039738743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9777003838798094719651657 7332752879098571039738743)
      ·
        refine ⟨10999129318647856559608115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7332752879098571039738743 10999129318647856559608115)
        ·
          refine ⟨16498693977971784839412173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10999129318647856559608115 16498693977971784839412173)
          ·
            refine ⟨6187010241739419314779565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16498693977971784839412173 6187010241739419314779565)
            ·
              refine ⟨2320128840652282243042337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6187010241739419314779565 2320128840652282243042337)
              ·
                refine ⟨1740096630489211682281753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2320128840652282243042337 1740096630489211682281753)
                ·
                  refine ⟨1305072472866908761711315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1740096630489211682281753 1305072472866908761711315)
                  ·
                    refine ⟨1957608709300363142566973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1305072472866908761711315 1957608709300363142566973)
                    ·
                      refine ⟨734103265987636178462615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1957608709300363142566973 734103265987636178462615)
                      ·
                        rfl

theorem cell23_1429661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_1429661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429661 prefixEnd_1429661 := by exact prefixLift 1429661
  have htrace : WordTrace (prefixWord ++ tailWord_1429661) baseStart_1429661 baseEnd_1429661 := by
    simpa [prefixWord, tailWord_1429661, baseEnd_1429661] using wordTrace_append hprefix tailTrace_1429661
  have hstable : (prefixWord ++ tailWord_1429661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429661).length < 2 ^ (prefixWord ++ tailWord_1429661).sum := by decide
  have hdescent : baseEnd_1429661 < baseStart_1429661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429667 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 2, 8, 2]
def baseStart_1429667 : Nat := 118140960795 + 1429667 * 2 ^ 59
def prefixEnd_1429667 : Nat := 4983230072969 + 3 ^ 40 * 1429667 * 2
def baseEnd_1429667 : Nat := 734106346871563154987587

theorem tailTrace_1429667 : CollatzResearch.WordTrace tailWord_1429667 prefixEnd_1429667 734106346871563154987587 := by
  unfold tailWord_1429667
  simp only [CollatzResearch.WordTrace]
  refine ⟨52144239311568101529527255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34762826207712067686351503 52144239311568101529527255)
  ·
    refine ⟨78216358967352152294290883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52144239311568101529527255 78216358967352152294290883)
    ·
      refine ⟨117324538451028228441436325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78216358967352152294290883 117324538451028228441436325)
      ·
        refine ⟨21998350959567792832769311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117324538451028228441436325 21998350959567792832769311)
        ·
          refine ⟨32997526439351689249153967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21998350959567792832769311 32997526439351689249153967)
          ·
            refine ⟨49496289659027533873730951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32997526439351689249153967 49496289659027533873730951)
            ·
              refine ⟨74244434488541300810596427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49496289659027533873730951 74244434488541300810596427)
              ·
                refine ⟨111366651732811951215894641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74244434488541300810596427 111366651732811951215894641)
                ·
                  refine ⟨83524988799608963411920981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111366651732811951215894641 83524988799608963411920981)
                  ·
                    refine ⟨978808462495417539983449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83524988799608963411920981 978808462495417539983449)
                    ·
                      refine ⟨734106346871563154987587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978808462495417539983449 734106346871563154987587)
                      ·
                        rfl

theorem cell23_1429667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_1429667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429667 prefixEnd_1429667 := by exact prefixLift 1429667
  have htrace : WordTrace (prefixWord ++ tailWord_1429667) baseStart_1429667 baseEnd_1429667 := by
    simpa [prefixWord, tailWord_1429667, baseEnd_1429667] using wordTrace_append hprefix tailTrace_1429667
  have hstable : (prefixWord ++ tailWord_1429667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429667).length < 2 ^ (prefixWord ++ tailWord_1429667).sum := by decide
  have hdescent : baseEnd_1429667 < baseStart_1429667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429735 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1429735 : Nat := 118140960795 + 1429735 * 2 ^ 59
def prefixEnd_1429735 : Nat := 4983230072969 + 3 ^ 40 * 1429735 * 2
def baseEnd_1429735 : Nat := 734141263556068888937275

theorem tailTrace_1429735 : CollatzResearch.WordTrace tailWord_1429735 prefixEnd_1429735 734141263556068888937275 := by
  unfold tailWord_1429735
  simp only [CollatzResearch.WordTrace]
  refine ⟨52146719475321749143002659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34764479650214499428668439 52146719475321749143002659)
  ·
    refine ⟨78220079212982623714503989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52146719475321749143002659 78220079212982623714503989)
    ·
      refine ⟨7333132426217120973234749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78220079212982623714503989 7333132426217120973234749)
      ·
        refine ⟨2749924659831420364963031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7333132426217120973234749 2749924659831420364963031)
        ·
          refine ⟨4124886989747130547444547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749924659831420364963031 4124886989747130547444547)
          ·
            refine ⟨6187330484620695821166821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124886989747130547444547 6187330484620695821166821)
            ·
              refine ⟨1160124465866380466468779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6187330484620695821166821 1160124465866380466468779)
              ·
                refine ⟨1740186698799570699703169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160124465866380466468779 1740186698799570699703169)
                ·
                  refine ⟨1305140024099678024777377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1740186698799570699703169 1305140024099678024777377)
                  ·
                    refine ⟨978855018074758518583033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1305140024099678024777377 978855018074758518583033)
                    ·
                      refine ⟨734141263556068888937275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978855018074758518583033 734141263556068888937275)
                      ·
                        rfl

theorem cell23_1429735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1429735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429735 prefixEnd_1429735 := by exact prefixLift 1429735
  have htrace : WordTrace (prefixWord ++ tailWord_1429735) baseStart_1429735 baseEnd_1429735 := by
    simpa [prefixWord, tailWord_1429735, baseEnd_1429735] using wordTrace_append hprefix tailTrace_1429735
  have hstable : (prefixWord ++ tailWord_1429735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429735).length < 2 ^ (prefixWord ++ tailWord_1429735).sum := by decide
  have hdescent : baseEnd_1429735 < baseStart_1429735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429754 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_1429754 : Nat := 118140960795 + 1429754 * 2 ^ 59
def prefixEnd_1429754 : Nat := 4983230072969 + 3 ^ 40 * 1429754 * 2
def baseEnd_1429754 : Nat := 244717006562834771533229

theorem tailTrace_1429754 : CollatzResearch.WordTrace tailWord_1429754 prefixEnd_1429754 244717006562834771533229 := by
  unfold tailWord_1429754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13036853115563228846986079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34764941641501943591962877 13036853115563228846986079)
  ·
    refine ⟨19555279673344843270479119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13036853115563228846986079 19555279673344843270479119)
    ·
      refine ⟨29332919510017264905718679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19555279673344843270479119 29332919510017264905718679)
      ·
        refine ⟨43999379265025897358578019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29332919510017264905718679 43999379265025897358578019)
        ·
          refine ⟨65999068897538846037867029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43999379265025897358578019 65999068897538846037867029)
          ·
            refine ⟨3093706354572133408025017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65999068897538846037867029 3093706354572133408025017)
            ·
              refine ⟨2320279765929100056018763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3093706354572133408025017 2320279765929100056018763)
              ·
                refine ⟨3480419648893650084028145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320279765929100056018763 3480419648893650084028145)
                ·
                  refine ⟨2610314736670237563021109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3480419648893650084028145 2610314736670237563021109)
                  ·
                    refine ⟨244717006562834771533229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2610314736670237563021109 244717006562834771533229)
                    ·
                      rfl

theorem cell23_1429754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_1429754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429754 prefixEnd_1429754 := by exact prefixLift 1429754
  have htrace : WordTrace (prefixWord ++ tailWord_1429754) baseStart_1429754 baseEnd_1429754 := by
    simpa [prefixWord, tailWord_1429754, baseEnd_1429754] using wordTrace_append hprefix tailTrace_1429754
  have hstable : (prefixWord ++ tailWord_1429754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429754).length < 2 ^ (prefixWord ++ tailWord_1429754).sum := by decide
  have hdescent : baseEnd_1429754 < baseStart_1429754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429757 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1429757 : Nat := 118140960795 + 1429757 * 2 ^ 59
def prefixEnd_1429757 : Nat := 4983230072969 + 3 ^ 40 * 1429757 * 2
def baseEnd_1429757 : Nat := 734152560130467802862173

theorem tailTrace_1429757 : CollatzResearch.WordTrace tailWord_1429757 prefixEnd_1429757 734152560130467802862173 := by
  unfold tailWord_1429757
  simp only [CollatzResearch.WordTrace]
  refine ⟨52147521881242046900303525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34765014587494697933535683 52147521881242046900303525)
  ·
    refine ⟨9777660352732883793806911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52147521881242046900303525 9777660352732883793806911)
    ·
      refine ⟨14666490529099325690710367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9777660352732883793806911 14666490529099325690710367)
      ·
        refine ⟨21999735793648988536065551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14666490529099325690710367 21999735793648988536065551)
        ·
          refine ⟨32999603690473482804098327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21999735793648988536065551 32999603690473482804098327)
          ·
            refine ⟨49499405535710224206147491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32999603690473482804098327 49499405535710224206147491)
            ·
              refine ⟨74249108303565336309221237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49499405535710224206147491 74249108303565336309221237)
              ·
                refine ⟨6960853903459250278989491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74249108303565336309221237 6960853903459250278989491)
                ·
                  refine ⟨10441280855188875418484237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6960853903459250278989491 10441280855188875418484237)
                  ·
                    refine ⟨3915480320695828281931589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10441280855188875418484237 3915480320695828281931589)
                    ·
                      refine ⟨734152560130467802862173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3915480320695828281931589 734152560130467802862173)
                      ·
                        rfl

theorem cell23_1429757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1429757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429757 prefixEnd_1429757 := by exact prefixLift 1429757
  have htrace : WordTrace (prefixWord ++ tailWord_1429757) baseStart_1429757 baseEnd_1429757 := by
    simpa [prefixWord, tailWord_1429757, baseEnd_1429757] using wordTrace_append hprefix tailTrace_1429757
  have hstable : (prefixWord ++ tailWord_1429757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429757).length < 2 ^ (prefixWord ++ tailWord_1429757).sum := by decide
  have hdescent : baseEnd_1429757 < baseStart_1429757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429774 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1429774 : Nat := 118140960795 + 1429774 * 2 ^ 59
def prefixEnd_1429774 : Nat := 4983230072969 + 3 ^ 40 * 1429774 * 2
def baseEnd_1429774 : Nat := 734161289301594236349595

theorem tailTrace_1429774 : CollatzResearch.WordTrace tailWord_1429774 prefixEnd_1429774 734161289301594236349595 := by
  unfold tailWord_1429774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6518517740272557350459047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34765427948120305869114917 6518517740272557350459047)
  ·
    refine ⟨9777776610408836025688571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6518517740272557350459047 9777776610408836025688571)
    ·
      refine ⟨14666664915613254038532857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9777776610408836025688571 14666664915613254038532857)
      ·
        refine ⟨10999998686709940528899643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14666664915613254038532857 10999998686709940528899643)
        ·
          refine ⟨16499998030064910793349465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10999998686709940528899643 16499998030064910793349465)
          ·
            refine ⟨12374998522548683095012099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16499998030064910793349465 12374998522548683095012099)
            ·
              refine ⟨18562497783823024642518149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12374998522548683095012099 18562497783823024642518149)
              ·
                refine ⟨3480468334466817120472153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18562497783823024642518149 3480468334466817120472153)
                ·
                  refine ⟨2610351250850112840354115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3480468334466817120472153 2610351250850112840354115)
                  ·
                    refine ⟨3915526876275169260531173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2610351250850112840354115 3915526876275169260531173)
                    ·
                      refine ⟨734161289301594236349595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3915526876275169260531173 734161289301594236349595)
                      ·
                        rfl

theorem cell23_1429774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1429774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429774 prefixEnd_1429774 := by exact prefixLift 1429774
  have htrace : WordTrace (prefixWord ++ tailWord_1429774) baseStart_1429774 baseEnd_1429774 := by
    simpa [prefixWord, tailWord_1429774, baseEnd_1429774] using wordTrace_append hprefix tailTrace_1429774
  have hstable : (prefixWord ++ tailWord_1429774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429774).length < 2 ^ (prefixWord ++ tailWord_1429774).sum := by decide
  have hdescent : baseEnd_1429774 < baseStart_1429774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429784 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 3, 4]
def baseStart_1429784 : Nat := 118140960795 + 1429784 * 2 ^ 59
def prefixEnd_1429784 : Nat := 4983230072969 + 3 ^ 40 * 1429784 * 2
def baseEnd_1429784 : Nat := 244722141369379732408183

theorem tailTrace_1429784 : CollatzResearch.WordTrace tailWord_1429784 prefixEnd_1429784 244722141369379732408183 := by
  unfold tailWord_1429784
  simp only [CollatzResearch.WordTrace]
  refine ⟨26074253326072115255768203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34765671101429487007690937 26074253326072115255768203)
  ·
    refine ⟨39111379989108172883652305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26074253326072115255768203 39111379989108172883652305)
    ·
      refine ⟨29333534991831129662739229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39111379989108172883652305 29333534991831129662739229)
      ·
        refine ⟨11000075621936673623527211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29333534991831129662739229 11000075621936673623527211)
        ·
          refine ⟨16500113432905010435290817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11000075621936673623527211 16500113432905010435290817)
          ·
            refine ⟨12375085074678757826468113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16500113432905010435290817 12375085074678757826468113)
            ·
              refine ⟨9281313806009068369851085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12375085074678757826468113 9281313806009068369851085)
              ·
                refine ⟨3480492677253400638694157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9281313806009068369851085 3480492677253400638694157)
                ·
                  refine ⟨1305184753970025239510309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3480492677253400638694157 1305184753970025239510309)
                  ·
                    refine ⟨244722141369379732408183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1305184753970025239510309 244722141369379732408183)
                    ·
                      rfl

theorem cell23_1429784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_1429784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429784 prefixEnd_1429784 := by exact prefixLift 1429784
  have htrace : WordTrace (prefixWord ++ tailWord_1429784) baseStart_1429784 baseEnd_1429784 := by
    simpa [prefixWord, tailWord_1429784, baseEnd_1429784] using wordTrace_append hprefix tailTrace_1429784
  have hstable : (prefixWord ++ tailWord_1429784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429784).length < 2 ^ (prefixWord ++ tailWord_1429784).sum := by decide
  have hdescent : baseEnd_1429784 < baseStart_1429784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429791 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 2, 4, 2]
def baseStart_1429791 : Nat := 118140960795 + 1429791 * 2 ^ 59
def prefixEnd_1429791 : Nat := 4983230072969 + 3 ^ 40 * 1429791 * 2
def baseEnd_1429791 : Nat := 734170018472720669837017

theorem tailTrace_1429791 : CollatzResearch.WordTrace tailWord_1429791 prefixEnd_1429791 734170018472720669837017 := by
  unfold tailWord_1429791
  simp only [CollatzResearch.WordTrace]
  refine ⟨52148761963118870707041227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34765841308745913804694151 52148761963118870707041227)
  ·
    refine ⟨78223142944678306060561841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52148761963118870707041227 78223142944678306060561841)
    ·
      refine ⟨58667357208508729545421381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78223142944678306060561841 58667357208508729545421381)
      ·
        refine ⟨11000129476595386789766509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58667357208508729545421381 11000129476595386789766509)
        ·
          refine ⟨4125048553723270046162441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11000129476595386789766509 4125048553723270046162441)
          ·
            refine ⟨3093786415292452534621831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4125048553723270046162441 3093786415292452534621831)
            ·
              refine ⟨4640679622938678801932747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093786415292452534621831 4640679622938678801932747)
              ·
                refine ⟨6961019434408018202899121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640679622938678801932747 6961019434408018202899121)
                ·
                  refine ⟨5220764575806013652174341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6961019434408018202899121 5220764575806013652174341)
                  ·
                    refine ⟨978893357963627559782689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5220764575806013652174341 978893357963627559782689)
                    ·
                      refine ⟨734170018472720669837017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 978893357963627559782689 734170018472720669837017)
                      ·
                        rfl

theorem cell23_1429791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_1429791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429791 prefixEnd_1429791 := by exact prefixLift 1429791
  have htrace : WordTrace (prefixWord ++ tailWord_1429791) baseStart_1429791 baseEnd_1429791 := by
    simpa [prefixWord, tailWord_1429791, baseEnd_1429791] using wordTrace_append hprefix tailTrace_1429791
  have hstable : (prefixWord ++ tailWord_1429791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429791).length < 2 ^ (prefixWord ++ tailWord_1429791).sum := by decide
  have hdescent : baseEnd_1429791 < baseStart_1429791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429805 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1429805 : Nat := 118140960795 + 1429805 * 2 ^ 59
def prefixEnd_1429805 : Nat := 4983230072969 + 3 ^ 40 * 1429805 * 2
def baseEnd_1429805 : Nat := 244725735733961205020651

theorem tailTrace_1429805 : CollatzResearch.WordTrace tailWord_1429805 prefixEnd_1429805 244725735733961205020651 := by
  unfold tailWord_1429805
  simp only [CollatzResearch.WordTrace]
  refine ⟨52149272585068151098050869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34766181723378767398700579 52149272585068151098050869)
  ·
    refine ⟨4888994304850139165442269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52149272585068151098050869 4888994304850139165442269)
    ·
      refine ⟨1833372864318802187040851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4888994304850139165442269 1833372864318802187040851)
      ·
        refine ⟨2750059296478203280561277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833372864318802187040851 2750059296478203280561277)
        ·
          refine ⟨1031272236179326230210479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2750059296478203280561277 1031272236179326230210479)
          ·
            refine ⟨1546908354268989345315719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031272236179326230210479 1546908354268989345315719)
            ·
              refine ⟨2320362531403484017973579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546908354268989345315719 2320362531403484017973579)
              ·
                refine ⟨3480543797105226026960369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320362531403484017973579 3480543797105226026960369)
                ·
                  refine ⟨2610407847828919520220277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3480543797105226026960369 2610407847828919520220277)
                  ·
                    refine ⟨244725735733961205020651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2610407847828919520220277 244725735733961205020651)
                    ·
                      rfl

theorem cell23_1429805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1429805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429805 prefixEnd_1429805 := by exact prefixLift 1429805
  have htrace : WordTrace (prefixWord ++ tailWord_1429805) baseStart_1429805 baseEnd_1429805 := by
    simpa [prefixWord, tailWord_1429805, baseEnd_1429805] using wordTrace_append hprefix tailTrace_1429805
  have hstable : (prefixWord ++ tailWord_1429805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429805).length < 2 ^ (prefixWord ++ tailWord_1429805).sum := by decide
  have hdescent : baseEnd_1429805 < baseStart_1429805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429818 : List Nat := [3, 1, 1, 1, 4, 3, 2, 3, 1, 4]
def baseStart_1429818 : Nat := 118140960795 + 1429818 * 2 ^ 59
def prefixEnd_1429818 : Nat := 4983230072969 + 3 ^ 40 * 1429818 * 2
def baseEnd_1429818 : Nat := 244727960816797354733131

theorem tailTrace_1429818 : CollatzResearch.WordTrace tailWord_1429818 prefixEnd_1429818 244727960816797354733131 := by
  unfold tailWord_1429818
  simp only [CollatzResearch.WordTrace]
  refine ⟨13037436683505263579568527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34766497822680702878849405 13037436683505263579568527)
  ·
    refine ⟨19556155025257895369352791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13037436683505263579568527 19556155025257895369352791)
    ·
      refine ⟨29334232537886843054029187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19556155025257895369352791 29334232537886843054029187)
      ·
        refine ⟨44001348806830264581043781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29334232537886843054029187 44001348806830264581043781)
        ·
          refine ⟨8250252901280674608945709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44001348806830264581043781 8250252901280674608945709)
          ·
            refine ⟨3093844837980252978354641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8250252901280674608945709 3093844837980252978354641)
            ·
              refine ⟨2320383628485189733765981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3093844837980252978354641 2320383628485189733765981)
              ·
                refine ⟨870143860681946150162243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2320383628485189733765981 870143860681946150162243)
                ·
                  refine ⟨1305215791022919225243365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870143860681946150162243 1305215791022919225243365)
                  ·
                    refine ⟨244727960816797354733131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1305215791022919225243365 244727960816797354733131)
                    ·
                      rfl

theorem cell23_1429818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_1429818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429818 prefixEnd_1429818 := by exact prefixLift 1429818
  have htrace : WordTrace (prefixWord ++ tailWord_1429818) baseStart_1429818 baseEnd_1429818 := by
    simpa [prefixWord, tailWord_1429818, baseEnd_1429818] using wordTrace_append hprefix tailTrace_1429818
  have hstable : (prefixWord ++ tailWord_1429818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429818).length < 2 ^ (prefixWord ++ tailWord_1429818).sum := by decide
  have hdescent : baseEnd_1429818 < baseStart_1429818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429841 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 3, 1, 3]
def baseStart_1429841 : Nat := 118140960795 + 1429841 * 2 ^ 59
def prefixEnd_1429841 : Nat := 4983230072969 + 3 ^ 40 * 1429841 * 2
def baseEnd_1429841 : Nat := 734195692505445474211787

theorem tailTrace_1429841 : CollatzResearch.WordTrace tailWord_1429841 prefixEnd_1429841 734195692505445474211787 := by
  unfold tailWord_1429841
  simp only [CollatzResearch.WordTrace]
  refine ⟨52150585612937729246361377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34767057075291819497574251 52150585612937729246361377)
  ·
    refine ⟨39112939209703296934771033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52150585612937729246361377 39112939209703296934771033)
    ·
      refine ⟨29334704407277472701078275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39112939209703296934771033 29334704407277472701078275)
      ·
        refine ⟨44002056610916209051617413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29334704407277472701078275 44002056610916209051617413)
        ·
          refine ⟨8250385614546789197178265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44002056610916209051617413 8250385614546789197178265)
          ·
            refine ⟨6187789210910091897883699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8250385614546789197178265 6187789210910091897883699)
            ·
              refine ⟨9281683816365137846825549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6187789210910091897883699 9281683816365137846825549)
              ·
                refine ⟨3480631431136926692559581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9281683816365137846825549 3480631431136926692559581)
                ·
                  refine ⟨1305236786676347509709843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3480631431136926692559581 1305236786676347509709843)
                  ·
                    refine ⟨1957855180014521264564765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1305236786676347509709843 1957855180014521264564765)
                    ·
                      refine ⟨734195692505445474211787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1957855180014521264564765 734195692505445474211787)
                      ·
                        rfl

theorem cell23_1429841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_1429841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429841 prefixEnd_1429841 := by exact prefixLift 1429841
  have htrace : WordTrace (prefixWord ++ tailWord_1429841) baseStart_1429841 baseEnd_1429841 := by
    simpa [prefixWord, tailWord_1429841, baseEnd_1429841] using wordTrace_append hprefix tailTrace_1429841
  have hstable : (prefixWord ++ tailWord_1429841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429841).length < 2 ^ (prefixWord ++ tailWord_1429841).sum := by decide
  have hdescent : baseEnd_1429841 < baseStart_1429841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429858 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1429858 : Nat := 118140960795 + 1429858 * 2 ^ 59
def prefixEnd_1429858 : Nat := 4983230072969 + 3 ^ 40 * 1429858 * 2
def baseEnd_1429858 : Nat := 734204421676571907699209

theorem tailTrace_1429858 : CollatzResearch.WordTrace tailWord_1429858 prefixEnd_1429858 734204421676571907699209 := by
  unfold tailWord_1429858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13037801413469035287432557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34767470435917427433153485 13037801413469035287432557)
  ·
    refine ⟨4889175530050888232787209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13037801413469035287432557 4889175530050888232787209)
    ·
      refine ⟨3666881647538166174590407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4889175530050888232787209 3666881647538166174590407)
      ·
        refine ⟨5500322471307249261885611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3666881647538166174590407 5500322471307249261885611)
        ·
          refine ⟨8250483706960873892828417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5500322471307249261885611 8250483706960873892828417)
          ·
            refine ⟨6187862780220655419621313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8250483706960873892828417 6187862780220655419621313)
            ·
              refine ⟨4640897085165491564715985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6187862780220655419621313 4640897085165491564715985)
              ·
                refine ⟨3480672813874118673536989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4640897085165491564715985 3480672813874118673536989)
                ·
                  refine ⟨1305252305202794502576371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3480672813874118673536989 1305252305202794502576371)
                  ·
                    refine ⟨1957878457804191753864557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1305252305202794502576371 1957878457804191753864557)
                    ·
                      refine ⟨734204421676571907699209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1957878457804191753864557 734204421676571907699209)
                      ·
                        rfl

theorem cell23_1429858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1429858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429858 prefixEnd_1429858 := by exact prefixLift 1429858
  have htrace : WordTrace (prefixWord ++ tailWord_1429858) baseStart_1429858 baseEnd_1429858 := by
    simpa [prefixWord, tailWord_1429858, baseEnd_1429858] using wordTrace_append hprefix tailTrace_1429858
  have hstable : (prefixWord ++ tailWord_1429858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429858).length < 2 ^ (prefixWord ++ tailWord_1429858).sum := by decide
  have hdescent : baseEnd_1429858 < baseStart_1429858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429861 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_1429861 : Nat := 118140960795 + 1429861 * 2 ^ 59
def prefixEnd_1429861 : Nat := 4983230072969 + 3 ^ 40 * 1429861 * 2
def baseEnd_1429861 : Nat := 244735320706178465320565

theorem tailTrace_1429861 : CollatzResearch.WordTrace tailWord_1429861 prefixEnd_1429861 244735320706178465320565 := by
  unfold tailWord_1429861
  simp only [CollatzResearch.WordTrace]
  refine ⟨52151315072865272662089437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34767543381910181774726291 52151315072865272662089437)
  ·
    refine ⟨19556743152324477248283539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52151315072865272662089437 19556743152324477248283539)
    ·
      refine ⟨29335114728486715872425309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19556743152324477248283539 29335114728486715872425309)
      ·
        refine ⟨11000668023182518452159491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29335114728486715872425309 11000668023182518452159491)
        ·
          refine ⟨16501002034773777678239237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11000668023182518452159491 16501002034773777678239237)
          ·
            refine ⟨3093937881520083314669857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16501002034773777678239237 3093937881520083314669857)
            ·
              refine ⟨2320453411140062486002393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3093937881520083314669857 2320453411140062486002393)
              ·
                refine ⟨1740340058355046864501795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2320453411140062486002393 1740340058355046864501795)
                ·
                  refine ⟨2610510087532570296752693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740340058355046864501795 2610510087532570296752693)
                  ·
                    refine ⟨244735320706178465320565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2610510087532570296752693 244735320706178465320565)
                    ·
                      rfl

theorem cell23_1429861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_1429861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429861 prefixEnd_1429861 := by exact prefixLift 1429861
  have htrace : WordTrace (prefixWord ++ tailWord_1429861) baseStart_1429861 baseEnd_1429861 := by
    simpa [prefixWord, tailWord_1429861, baseEnd_1429861] using wordTrace_append hprefix tailTrace_1429861
  have hstable : (prefixWord ++ tailWord_1429861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429861).length < 2 ^ (prefixWord ++ tailWord_1429861).sum := by decide
  have hdescent : baseEnd_1429861 < baseStart_1429861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429928 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1429928 : Nat := 118140960795 + 1429928 * 2 ^ 59
def prefixEnd_1429928 : Nat := 4983230072969 + 3 ^ 40 * 1429928 * 2
def baseEnd_1429928 : Nat := 734240365322386633823887

theorem tailTrace_1429928 : CollatzResearch.WordTrace tailWord_1429928 prefixEnd_1429928 734240365322386633823887 := by
  unfold tailWord_1429928
  simp only [CollatzResearch.WordTrace]
  refine ⟨26076879381811271552389219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34769172509081695403185625 26076879381811271552389219)
  ·
    refine ⟨39115319072716907328583829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26076879381811271552389219 39115319072716907328583829)
    ·
      refine ⟨1833530581533605031027367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39115319072716907328583829 1833530581533605031027367)
      ·
        refine ⟨2750295872300407546541051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833530581533605031027367 2750295872300407546541051)
        ·
          refine ⟨4125443808450611319811577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750295872300407546541051 4125443808450611319811577)
          ·
            refine ⟨3094082856337958489858683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4125443808450611319811577 3094082856337958489858683)
            ·
              refine ⟨4641124284506937734788025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094082856337958489858683 4641124284506937734788025)
              ·
                refine ⟨3480843213380203301091019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4641124284506937734788025 3480843213380203301091019)
                ·
                  refine ⟨5221264820070304951636529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480843213380203301091019 5221264820070304951636529)
                  ·
                    refine ⟨3915948615052728713727397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5221264820070304951636529 3915948615052728713727397)
                    ·
                      refine ⟨734240365322386633823887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3915948615052728713727397 734240365322386633823887)
                      ·
                        rfl

theorem cell23_1429928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1429928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429928 prefixEnd_1429928 := by exact prefixLift 1429928
  have htrace : WordTrace (prefixWord ++ tailWord_1429928) baseStart_1429928 baseEnd_1429928 := by
    simpa [prefixWord, tailWord_1429928, baseEnd_1429928] using wordTrace_append hprefix tailTrace_1429928
  have hstable : (prefixWord ++ tailWord_1429928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429928).length < 2 ^ (prefixWord ++ tailWord_1429928).sum := by decide
  have hdescent : baseEnd_1429928 < baseStart_1429928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429949 : List Nat := [1, 4, 1, 2, 2, 4, 2, 2, 1, 2, 2]
def baseStart_1429949 : Nat := 118140960795 + 1429949 * 2 ^ 59
def prefixEnd_1429949 : Nat := 4983230072969 + 3 ^ 40 * 1429949 * 2
def baseEnd_1429949 : Nat := 734251148416131051661291

theorem tailTrace_1429949 : CollatzResearch.WordTrace tailWord_1429949 prefixEnd_1429949 734251148416131051661291 := by
  unfold tailWord_1429949
  simp only [CollatzResearch.WordTrace]
  refine ⟨52154524696546463691292901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34769683131030975794195267 52154524696546463691292901)
  ·
    refine ⟨9778973380602461942117419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52154524696546463691292901 9778973380602461942117419)
    ·
      refine ⟨14668460070903692913176129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9778973380602461942117419 14668460070903692913176129)
      ·
        refine ⟨11001345053177769684882097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14668460070903692913176129 11001345053177769684882097)
        ·
          refine ⟨8251008789883327263661573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11001345053177769684882097 8251008789883327263661573)
          ·
            refine ⟨1547064148103123861936545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8251008789883327263661573 1547064148103123861936545)
            ·
              refine ⟨1160298111077342896452409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547064148103123861936545 1160298111077342896452409)
              ·
                refine ⟨870223583308007172339307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1160298111077342896452409 870223583308007172339307)
                ·
                  refine ⟨1305335374962010758508961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870223583308007172339307 1305335374962010758508961)
                  ·
                    refine ⟨979001531221508068881721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1305335374962010758508961 979001531221508068881721)
                    ·
                      refine ⟨734251148416131051661291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979001531221508068881721 734251148416131051661291)
                      ·
                        rfl

theorem cell23_1429949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_1429949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429949 prefixEnd_1429949 := by exact prefixLift 1429949
  have htrace : WordTrace (prefixWord ++ tailWord_1429949) baseStart_1429949 baseEnd_1429949 := by
    simpa [prefixWord, tailWord_1429949, baseEnd_1429949] using wordTrace_append hprefix tailTrace_1429949
  have hstable : (prefixWord ++ tailWord_1429949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429949).length < 2 ^ (prefixWord ++ tailWord_1429949).sum := by decide
  have hdescent : baseEnd_1429949 < baseStart_1429949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429984 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_1429984 : Nat := 118140960795 + 1429984 * 2 ^ 59
def prefixEnd_1429984 : Nat := 4983230072969 + 3 ^ 40 * 1429984 * 2
def baseEnd_1429984 : Nat := 734269120239038414723629

theorem tailTrace_1429984 : CollatzResearch.WordTrace tailWord_1429984 prefixEnd_1429984 734269120239038414723629 := by
  unfold tailWord_1429984
  simp only [CollatzResearch.WordTrace]
  refine ⟨26077900625709832334408503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34770534167613109779211337 26077900625709832334408503)
  ·
    refine ⟨39116850938564748501612755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26077900625709832334408503 39116850938564748501612755)
    ·
      refine ⟨58675276407847122752419133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39116850938564748501612755 58675276407847122752419133)
      ·
        refine ⟨22003228652942671032157175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58675276407847122752419133 22003228652942671032157175)
        ·
          refine ⟨33004842979414006548235763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22003228652942671032157175 33004842979414006548235763)
          ·
            refine ⟨49507264469121009822353645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33004842979414006548235763 49507264469121009822353645)
            ·
              refine ⟨18565224175920378683382617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49507264469121009822353645 18565224175920378683382617)
              ·
                refine ⟨13923918131940284012536963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18565224175920378683382617 13923918131940284012536963)
                ·
                  refine ⟨20885877197910426018805445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13923918131940284012536963 20885877197910426018805445)
                  ·
                    refine ⟨3916101974608204878526021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20885877197910426018805445 3916101974608204878526021)
                    ·
                      refine ⟨734269120239038414723629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3916101974608204878526021 734269120239038414723629)
                      ·
                        rfl

theorem cell23_1429984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_1429984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429984 prefixEnd_1429984 := by exact prefixLift 1429984
  have htrace : WordTrace (prefixWord ++ tailWord_1429984) baseStart_1429984 baseEnd_1429984 := by
    simpa [prefixWord, tailWord_1429984, baseEnd_1429984] using wordTrace_append hprefix tailTrace_1429984
  have hstable : (prefixWord ++ tailWord_1429984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429984).length < 2 ^ (prefixWord ++ tailWord_1429984).sum := by decide
  have hdescent : baseEnd_1429984 < baseStart_1429984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429986 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1429986 : Nat := 118140960795 + 1429986 * 2 ^ 59
def prefixEnd_1429986 : Nat := 4983230072969 + 3 ^ 40 * 1429986 * 2
def baseEnd_1429986 : Nat := 734270147200347406898621

theorem tailTrace_1429986 : CollatzResearch.WordTrace tailWord_1429986 prefixEnd_1429986 734270147200347406898621 := by
  unfold tailWord_1429986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13038968549353104752597453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34770582798274946006926541 13038968549353104752597453)
  ·
    refine ⟨4889613206007414282224045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13038968549353104752597453 4889613206007414282224045)
    ·
      refine ⟨1833604952252780355834017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4889613206007414282224045 1833604952252780355834017)
      ·
        refine ⟨1375203714189585266875513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1833604952252780355834017 1375203714189585266875513)
        ·
          refine ⟨1031402785642188950156635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1375203714189585266875513 1031402785642188950156635)
          ·
            refine ⟨1547104178463283425234953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031402785642188950156635 1547104178463283425234953)
            ·
              refine ⟨1160328133847462568926215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547104178463283425234953 1160328133847462568926215)
              ·
                refine ⟨1740492200771193853389323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160328133847462568926215 1740492200771193853389323)
                ·
                  refine ⟨2610738301156790780083985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740492200771193853389323 2610738301156790780083985)
                  ·
                    refine ⟨1958053725867593085062989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2610738301156790780083985 1958053725867593085062989)
                    ·
                      refine ⟨734270147200347406898621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1958053725867593085062989 734270147200347406898621)
                      ·
                        rfl

theorem cell23_1429986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1429986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429986 prefixEnd_1429986 := by exact prefixLift 1429986
  have htrace : WordTrace (prefixWord ++ tailWord_1429986) baseStart_1429986 baseEnd_1429986 := by
    simpa [prefixWord, tailWord_1429986, baseEnd_1429986] using wordTrace_append hprefix tailTrace_1429986
  have hstable : (prefixWord ++ tailWord_1429986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429986).length < 2 ^ (prefixWord ++ tailWord_1429986).sum := by decide
  have hdescent : baseEnd_1429986 < baseStart_1429986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429992 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_1429992 : Nat := 118140960795 + 1429992 * 2 ^ 59
def prefixEnd_1429992 : Nat := 4983230072969 + 3 ^ 40 * 1429992 * 2
def baseEnd_1429992 : Nat := 734273228084274383423593

theorem tailTrace_1429992 : CollatzResearch.WordTrace tailWord_1429992 prefixEnd_1429992 734273228084274383423593 := by
  unfold tailWord_1429992
  simp only [CollatzResearch.WordTrace]
  refine ⟨26078046517695341017554115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34770728690260454690072153 26078046517695341017554115)
  ·
    refine ⟨39117069776543011526331173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26078046517695341017554115 39117069776543011526331173)
    ·
      refine ⟨7334450583101814661187095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39117069776543011526331173 7334450583101814661187095)
      ·
        refine ⟨11001675874652721991780643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7334450583101814661187095 11001675874652721991780643)
        ·
          refine ⟨16502513811979082987670965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11001675874652721991780643 16502513811979082987670965)
          ·
            refine ⟨1547110669873039030094153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16502513811979082987670965 1547110669873039030094153)
            ·
              refine ⟨1160333002404779272570615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547110669873039030094153 1160333002404779272570615)
              ·
                refine ⟨1740499503607168908855923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160333002404779272570615 1740499503607168908855923)
                ·
                  refine ⟨2610749255410753363283885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740499503607168908855923 2610749255410753363283885)
                  ·
                    refine ⟨979030970779032511231457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2610749255410753363283885 979030970779032511231457)
                    ·
                      refine ⟨734273228084274383423593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979030970779032511231457 734273228084274383423593)
                      ·
                        rfl

theorem cell23_1429992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_1429992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1429992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1429992 prefixEnd_1429992 := by exact prefixLift 1429992
  have htrace : WordTrace (prefixWord ++ tailWord_1429992) baseStart_1429992 baseEnd_1429992 := by
    simpa [prefixWord, tailWord_1429992, baseEnd_1429992] using wordTrace_append hprefix tailTrace_1429992
  have hstable : (prefixWord ++ tailWord_1429992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429992).length < 2 ^ (prefixWord ++ tailWord_1429992).sum := by decide
  have hdescent : baseEnd_1429992 < baseStart_1429992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430021 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 2, 3, 3]
def baseStart_1430021 : Nat := 118140960795 + 1430021 * 2 ^ 59
def prefixEnd_1430021 : Nat := 4983230072969 + 3 ^ 40 * 1430021 * 2
def baseEnd_1430021 : Nat := 734288119023254769960959

theorem tailTrace_1430021 : CollatzResearch.WordTrace tailWord_1430021 prefixEnd_1430021 734288119023254769960959 := by
  unfold tailWord_1430021
  simp only [CollatzResearch.WordTrace]
  refine ⟨52157150752285619987913917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34771433834857079991942611 52157150752285619987913917)
  ·
    refine ⟨19558931532107107495467719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52157150752285619987913917 19558931532107107495467719)
    ·
      refine ⟨29338397298160661243201579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19558931532107107495467719 29338397298160661243201579)
      ·
        refine ⟨44007595947240991864802369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29338397298160661243201579 44007595947240991864802369)
        ·
          refine ⟨33005696960430743898601777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44007595947240991864802369 33005696960430743898601777)
          ·
            refine ⟨24754272720323057923951333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33005696960430743898601777 24754272720323057923951333)
            ·
              refine ⟨4641426135060573360740875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24754272720323057923951333 4641426135060573360740875)
              ·
                refine ⟨6962139202590860041111313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641426135060573360740875 6962139202590860041111313)
                ·
                  refine ⟨5221604401943145030833485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6962139202590860041111313 5221604401943145030833485)
                  ·
                    refine ⟨1958101650728679386562557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5221604401943145030833485 1958101650728679386562557)
                    ·
                      refine ⟨734288119023254769960959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1958101650728679386562557 734288119023254769960959)
                      ·
                        rfl

theorem cell23_1430021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_1430021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430021 prefixEnd_1430021 := by exact prefixLift 1430021
  have htrace : WordTrace (prefixWord ++ tailWord_1430021) baseStart_1430021 baseEnd_1430021 := by
    simpa [prefixWord, tailWord_1430021, baseEnd_1430021] using wordTrace_append hprefix tailTrace_1430021
  have hstable : (prefixWord ++ tailWord_1430021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430021).length < 2 ^ (prefixWord ++ tailWord_1430021).sum := by decide
  have hdescent : baseEnd_1430021 < baseStart_1430021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430031 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 4, 5, 2]
def baseStart_1430031 : Nat := 118140960795 + 1430031 * 2 ^ 59
def prefixEnd_1430031 : Nat := 4983230072969 + 3 ^ 40 * 1430031 * 2
def baseEnd_1430031 : Nat := 734293253829799730835913

theorem tailTrace_1430031 : CollatzResearch.WordTrace tailWord_1430031 prefixEnd_1430031 734293253829799730835913 := by
  unfold tailWord_1430031
  simp only [CollatzResearch.WordTrace]
  refine ⟨52157515482249391695777947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34771676988166261130518631 52157515482249391695777947)
  ·
    refine ⟨78236273223374087543666921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52157515482249391695777947 78236273223374087543666921)
    ·
      refine ⟨58677204917530565657750191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78236273223374087543666921 58677204917530565657750191)
      ·
        refine ⟨88015807376295848486625287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58677204917530565657750191 88015807376295848486625287)
        ·
          refine ⟨132023711064443772729937931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88015807376295848486625287 132023711064443772729937931)
          ·
            refine ⟨198035566596665659094906897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132023711064443772729937931 198035566596665659094906897)
            ·
              refine ⟨148526674947499244321180173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198035566596665659094906897 148526674947499244321180173)
              ·
                refine ⟨55697503105312216620442565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148526674947499244321180173 55697503105312216620442565)
                ·
                  refine ⟨10443281832246040616332981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55697503105312216620442565 10443281832246040616332981)
                  ·
                    refine ⟨979057671773066307781217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10443281832246040616332981 979057671773066307781217)
                    ·
                      refine ⟨734293253829799730835913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979057671773066307781217 734293253829799730835913)
                      ·
                        rfl

theorem cell23_1430031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 5, 2].length) (baseStart_1430031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430031 prefixEnd_1430031 := by exact prefixLift 1430031
  have htrace : WordTrace (prefixWord ++ tailWord_1430031) baseStart_1430031 baseEnd_1430031 := by
    simpa [prefixWord, tailWord_1430031, baseEnd_1430031] using wordTrace_append hprefix tailTrace_1430031
  have hstable : (prefixWord ++ tailWord_1430031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430031).length < 2 ^ (prefixWord ++ tailWord_1430031).sum := by decide
  have hdescent : baseEnd_1430031 < baseStart_1430031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430045 : List Nat := [1, 4, 2, 2, 1, 4, 1, 3, 5]
def baseStart_1430045 : Nat := 118140960795 + 1430045 * 2 ^ 59
def prefixEnd_1430045 : Nat := 4983230072969 + 3 ^ 40 * 1430045 * 2
def baseEnd_1430045 : Nat := 81588938062106964006761

theorem tailTrace_1430045 : CollatzResearch.WordTrace tailWord_1430045 prefixEnd_1430045 81588938062106964006761 := by
  unfold tailWord_1430045
  simp only [CollatzResearch.WordTrace]
  refine ⟨52158026104198672086787589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34772017402799114724525059 52158026104198672086787589)
  ·
    refine ⟨9779629894537251016272673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52158026104198672086787589 9779629894537251016272673)
    ·
      refine ⟨7334722420902938262204505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9779629894537251016272673 7334722420902938262204505)
      ·
        refine ⟨5501041815677203696653379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7334722420902938262204505 5501041815677203696653379)
        ·
          refine ⟨8251562723515805544980069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501041815677203696653379 8251562723515805544980069)
          ·
            refine ⟨1547168010659213539683763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8251562723515805544980069 1547168010659213539683763)
            ·
              refine ⟨2320752015988820309525645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547168010659213539683763 2320752015988820309525645)
              ·
                refine ⟨870282005995807616072117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2320752015988820309525645 870282005995807616072117)
                ·
                  refine ⟨81588938062106964006761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 870282005995807616072117 81588938062106964006761)
                  ·
                    rfl

theorem cell23_1430045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_1430045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430045 prefixEnd_1430045 := by exact prefixLift 1430045
  have htrace : WordTrace (prefixWord ++ tailWord_1430045) baseStart_1430045 baseEnd_1430045 := by
    simpa [prefixWord, tailWord_1430045, baseEnd_1430045] using wordTrace_append hprefix tailTrace_1430045
  have hstable : (prefixWord ++ tailWord_1430045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430045).length < 2 ^ (prefixWord ++ tailWord_1430045).sum := by decide
  have hdescent : baseEnd_1430045 < baseStart_1430045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430058 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1430058 : Nat := 118140960795 + 1430058 * 2 ^ 59
def prefixEnd_1430058 : Nat := 4983230072969 + 3 ^ 40 * 1430058 * 2
def baseEnd_1430058 : Nat := 244769039269157041732763

theorem tailTrace_1430058 : CollatzResearch.WordTrace tailWord_1430058 prefixEnd_1430058 244769039269157041732763 := by
  unfold tailWord_1430058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13039625063287893826752707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34772333502101050204673885 13039625063287893826752707)
  ·
    refine ⟨19559437594931840740129061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13039625063287893826752707 19559437594931840740129061)
    ·
      refine ⟨3667394549049720138774199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19559437594931840740129061 3667394549049720138774199)
      ·
        refine ⟨5501091823574580208161299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3667394549049720138774199 5501091823574580208161299)
        ·
          refine ⟨8251637735361870312241949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501091823574580208161299 8251637735361870312241949)
          ·
            refine ⟨3094364150760701367090731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8251637735361870312241949 3094364150760701367090731)
            ·
              refine ⟨4641546226141052050636097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094364150760701367090731 4641546226141052050636097)
              ·
                refine ⟨3481159669605789037977073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4641546226141052050636097 3481159669605789037977073)
                ·
                  refine ⟨2610869752204341778482805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3481159669605789037977073 2610869752204341778482805)
                  ·
                    refine ⟨244769039269157041732763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2610869752204341778482805 244769039269157041732763)
                    ·
                      rfl

theorem cell23_1430058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1430058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430058 prefixEnd_1430058 := by exact prefixLift 1430058
  have htrace : WordTrace (prefixWord ++ tailWord_1430058) baseStart_1430058 baseEnd_1430058 := by
    simpa [prefixWord, tailWord_1430058, baseEnd_1430058] using wordTrace_append hprefix tailTrace_1430058
  have hstable : (prefixWord ++ tailWord_1430058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430058).length < 2 ^ (prefixWord ++ tailWord_1430058).sum := by decide
  have hdescent : baseEnd_1430058 < baseStart_1430058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430062 : List Nat := [4, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_1430062 : Nat := 118140960795 + 1430062 * 2 ^ 59
def prefixEnd_1430062 : Nat := 4983230072969 + 3 ^ 40 * 1430062 * 2
def baseEnd_1430062 : Nat := 81589907970009901060919

theorem tailTrace_1430062 : CollatzResearch.WordTrace tailWord_1430062 prefixEnd_1430062 81589907970009901060919 := by
  unfold tailWord_1430062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519830768142135498769555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34772430763424722660104293 6519830768142135498769555)
  ·
    refine ⟨9779746152213203248154333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6519830768142135498769555 9779746152213203248154333)
    ·
      refine ⟨3667404807079951218057875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9779746152213203248154333 3667404807079951218057875)
      ·
        refine ⟨5501107210619926827086813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3667404807079951218057875 5501107210619926827086813)
        ·
          refine ⟨2062915203982472560157555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5501107210619926827086813 2062915203982472560157555)
          ·
            refine ⟨3094372805973708840236333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062915203982472560157555 3094372805973708840236333)
            ·
              refine ⟨1160389802240140815088625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3094372805973708840236333 1160389802240140815088625)
              ·
                refine ⟨870292351680105611316469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1160389802240140815088625 870292351680105611316469)
                ·
                  refine ⟨81589907970009901060919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 870292351680105611316469 81589907970009901060919)
                  ·
                    rfl

theorem cell23_1430062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_1430062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430062 prefixEnd_1430062 := by exact prefixLift 1430062
  have htrace : WordTrace (prefixWord ++ tailWord_1430062) baseStart_1430062 baseEnd_1430062 := by
    simpa [prefixWord, tailWord_1430062, baseEnd_1430062] using wordTrace_append hprefix tailTrace_1430062
  have hstable : (prefixWord ++ tailWord_1430062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430062).length < 2 ^ (prefixWord ++ tailWord_1430062).sum := by decide
  have hdescent : baseEnd_1430062 < baseStart_1430062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430145 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1430145 : Nat := 118140960795 + 1430145 * 2 ^ 59
def prefixEnd_1430145 : Nat := 4983230072969 + 3 ^ 40 * 1430145 * 2
def baseEnd_1430145 : Nat := 734351790624412284810389

theorem tailTrace_1430145 : CollatzResearch.WordTrace tailWord_1430145 prefixEnd_1430145 734351790624412284810389 := by
  unfold tailWord_1430145
  simp only [CollatzResearch.WordTrace]
  refine ⟨52161673403836389165427889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34774448935890926110285259 52161673403836389165427889)
  ·
    refine ⟨39121255052877291874070917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52161673403836389165427889 39121255052877291874070917)
    ·
      refine ⟨7335235322414492226388297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39121255052877291874070917 7335235322414492226388297)
      ·
        refine ⟨5501426491810869169791223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7335235322414492226388297 5501426491810869169791223)
        ·
          refine ⟨8252139737716303754686835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501426491810869169791223 8252139737716303754686835)
          ·
            refine ⟨12378209606574455632030253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8252139737716303754686835 12378209606574455632030253)
            ·
              refine ⟨4641828602465420862011345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12378209606574455632030253 4641828602465420862011345)
              ·
                refine ⟨3481371451849065646508509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4641828602465420862011345 3481371451849065646508509)
                ·
                  refine ⟨1305514294443399617440691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3481371451849065646508509 1305514294443399617440691)
                  ·
                    refine ⟨1958271441665099426161037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1305514294443399617440691 1958271441665099426161037)
                    ·
                      refine ⟨734351790624412284810389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1958271441665099426161037 734351790624412284810389)
                      ·
                        rfl

theorem cell23_1430145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1430145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430145 prefixEnd_1430145 := by exact prefixLift 1430145
  have htrace : WordTrace (prefixWord ++ tailWord_1430145) baseStart_1430145 baseEnd_1430145 := by
    simpa [prefixWord, tailWord_1430145, baseEnd_1430145] using wordTrace_append hprefix tailTrace_1430145
  have hstable : (prefixWord ++ tailWord_1430145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430145).length < 2 ^ (prefixWord ++ tailWord_1430145).sum := by decide
  have hdescent : baseEnd_1430145 < baseStart_1430145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430146 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1430146 : Nat := 118140960795 + 1430146 * 2 ^ 59
def prefixEnd_1430146 : Nat := 4983230072969 + 3 ^ 40 * 1430146 * 2
def baseEnd_1430146 : Nat := 734352304105066780897885

theorem tailTrace_1430146 : CollatzResearch.WordTrace tailWord_1430146 prefixEnd_1430146 734352304105066780897885 := by
  unfold tailWord_1430146
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040427469208191584053573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34774473251221844224142861 13040427469208191584053573)
  ·
    refine ⟨2445080150476535922010045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13040427469208191584053573 2445080150476535922010045)
    ·
      refine ⟨916905056428700970753767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2445080150476535922010045 916905056428700970753767)
      ·
        refine ⟨1375357584643051456130651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916905056428700970753767 1375357584643051456130651)
        ·
          refine ⟨2063036376964577184195977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375357584643051456130651 2063036376964577184195977)
          ·
            refine ⟨1547277282723432888146983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2063036376964577184195977 1547277282723432888146983)
            ·
              refine ⟨2320915924085149332220475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547277282723432888146983 2320915924085149332220475)
              ·
                refine ⟨3481373886127723998330713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320915924085149332220475 3481373886127723998330713)
                ·
                  refine ⟨2611030414595792998748035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3481373886127723998330713 2611030414595792998748035)
                  ·
                    refine ⟨3916545621893689498122053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2611030414595792998748035 3916545621893689498122053)
                    ·
                      refine ⟨734352304105066780897885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3916545621893689498122053 734352304105066780897885)
                      ·
                        rfl

theorem cell23_1430146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1430146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430146 prefixEnd_1430146 := by exact prefixLift 1430146
  have htrace : WordTrace (prefixWord ++ tailWord_1430146) baseStart_1430146 baseEnd_1430146 := by
    simpa [prefixWord, tailWord_1430146, baseEnd_1430146] using wordTrace_append hprefix tailTrace_1430146
  have hstable : (prefixWord ++ tailWord_1430146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430146).length < 2 ^ (prefixWord ++ tailWord_1430146).sum := by decide
  have hdescent : baseEnd_1430146 < baseStart_1430146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430148 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_1430148 : Nat := 118140960795 + 1430148 * 2 ^ 59
def prefixEnd_1430148 : Nat := 4983230072969 + 3 ^ 40 * 1430148 * 2
def baseEnd_1430148 : Nat := 244784443688791924357625

theorem tailTrace_1430148 : CollatzResearch.WordTrace tailWord_1430148 prefixEnd_1430148 244784443688791924357625 := by
  unfold tailWord_1430148
  simp only [CollatzResearch.WordTrace]
  refine ⟨26080891411412760338893549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34774521881883680451858065 26080891411412760338893549)
  ·
    refine ⟨9780334279279785127085081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26080891411412760338893549 9780334279279785127085081)
    ·
      refine ⟨7335250709459838845313811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9780334279279785127085081 7335250709459838845313811)
      ·
        refine ⟨11002876064189758267970717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7335250709459838845313811 11002876064189758267970717)
        ·
          refine ⟨4126078524071159350489019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11002876064189758267970717 4126078524071159350489019)
          ·
            refine ⟨6189117786106739025733529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4126078524071159350489019 6189117786106739025733529)
            ·
              refine ⟨4641838339580054269300147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6189117786106739025733529 4641838339580054269300147)
              ·
                refine ⟨6962757509370081403950221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641838339580054269300147 6962757509370081403950221)
                ·
                  refine ⟨2611034066013780526481333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6962757509370081403950221 2611034066013780526481333)
                  ·
                    refine ⟨244784443688791924357625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2611034066013780526481333 244784443688791924357625)
                    ·
                      rfl

theorem cell23_1430148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_1430148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430148 prefixEnd_1430148 := by exact prefixLift 1430148
  have htrace : WordTrace (prefixWord ++ tailWord_1430148) baseStart_1430148 baseEnd_1430148 := by
    simpa [prefixWord, tailWord_1430148, baseEnd_1430148] using wordTrace_append hprefix tailTrace_1430148
  have hstable : (prefixWord ++ tailWord_1430148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430148).length < 2 ^ (prefixWord ++ tailWord_1430148).sum := by decide
  have hdescent : baseEnd_1430148 < baseStart_1430148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430171 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 3]
def baseStart_1430171 : Nat := 118140960795 + 1430171 * 2 ^ 59
def prefixEnd_1430171 : Nat := 4983230072969 + 3 ^ 40 * 1430171 * 2
def baseEnd_1430171 : Nat := 734365141121429183085269

theorem tailTrace_1430171 : CollatzResearch.WordTrace tailWord_1430171 prefixEnd_1430171 734365141121429183085269 := by
  unfold tailWord_1430171
  simp only [CollatzResearch.WordTrace]
  refine ⟨52162621701742195605874367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34775081134494797070582911 52162621701742195605874367)
  ·
    refine ⟨78243932552613293408811551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52162621701742195605874367 78243932552613293408811551)
    ·
      refine ⟨117365898828919940113217327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78243932552613293408811551 117365898828919940113217327)
      ·
        refine ⟨176048848243379910169825991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117365898828919940113217327 176048848243379910169825991)
        ·
          refine ⟨264073272365069865254738987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176048848243379910169825991 264073272365069865254738987)
          ·
            refine ⟨396109908547604797882108481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264073272365069865254738987 396109908547604797882108481)
            ·
              refine ⟨297082431410703598411581361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396109908547604797882108481 297082431410703598411581361)
              ·
                refine ⟨222811823558027698808686021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297082431410703598411581361 222811823558027698808686021)
                ·
                  refine ⟨41777216917130193526628629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222811823558027698808686021 41777216917130193526628629)
                  ·
                    refine ⟨1958307042990477821560717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41777216917130193526628629 1958307042990477821560717)
                    ·
                      refine ⟨734365141121429183085269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1958307042990477821560717 734365141121429183085269)
                      ·
                        rfl

theorem cell23_1430171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 3].length) (baseStart_1430171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430171 prefixEnd_1430171 := by exact prefixLift 1430171
  have htrace : WordTrace (prefixWord ++ tailWord_1430171) baseStart_1430171 baseEnd_1430171 := by
    simpa [prefixWord, tailWord_1430171, baseEnd_1430171] using wordTrace_append hprefix tailTrace_1430171
  have hstable : (prefixWord ++ tailWord_1430171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430171).length < 2 ^ (prefixWord ++ tailWord_1430171).sum := by decide
  have hdescent : baseEnd_1430171 < baseStart_1430171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430181 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_1430181 : Nat := 118140960795 + 1430181 * 2 ^ 59
def prefixEnd_1430181 : Nat := 4983230072969 + 3 ^ 40 * 1430181 * 2
def baseEnd_1430181 : Nat := 734370275927974143960223

theorem tailTrace_1430181 : CollatzResearch.WordTrace tailWord_1430181 prefixEnd_1430181 734370275927974143960223 := by
  unfold tailWord_1430181
  simp only [CollatzResearch.WordTrace]
  refine ⟨52162986431705967313738397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34775324287803978209158931 52162986431705967313738397)
  ·
    refine ⟨19561119911889737742651899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52162986431705967313738397 19561119911889737742651899)
    ·
      refine ⟨29341679867834606613977849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19561119911889737742651899 29341679867834606613977849)
      ·
        refine ⟨22006259900875954960483387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29341679867834606613977849 22006259900875954960483387)
        ·
          refine ⟨33009389851313932440725081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22006259900875954960483387 33009389851313932440725081)
          ·
            refine ⟨24757042388485449330543811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33009389851313932440725081 24757042388485449330543811)
            ·
              refine ⟨37135563582728173995815717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24757042388485449330543811 37135563582728173995815717)
              ·
                refine ⟨6962918171761532624215447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37135563582728173995815717 6962918171761532624215447)
                ·
                  refine ⟨10444377257642298936323171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6962918171761532624215447 10444377257642298936323171)
                  ·
                    refine ⟨15666565886463448404484757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10444377257642298936323171 15666565886463448404484757)
                    ·
                      refine ⟨734370275927974143960223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15666565886463448404484757 734370275927974143960223)
                      ·
                        rfl

theorem cell23_1430181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_1430181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430181 prefixEnd_1430181 := by exact prefixLift 1430181
  have htrace : WordTrace (prefixWord ++ tailWord_1430181) baseStart_1430181 baseEnd_1430181 := by
    simpa [prefixWord, tailWord_1430181, baseEnd_1430181] using wordTrace_append hprefix tailTrace_1430181
  have hstable : (prefixWord ++ tailWord_1430181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430181).length < 2 ^ (prefixWord ++ tailWord_1430181).sum := by decide
  have hdescent : baseEnd_1430181 < baseStart_1430181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430185 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 3, 2, 2]
def baseStart_1430185 : Nat := 118140960795 + 1430185 * 2 ^ 59
def prefixEnd_1430185 : Nat := 4983230072969 + 3 ^ 40 * 1430185 * 2
def baseEnd_1430185 : Nat := 734372329850592128310205

theorem tailTrace_1430185 : CollatzResearch.WordTrace tailWord_1430185 prefixEnd_1430185 734372329850592128310205 := by
  unfold tailWord_1430185
  simp only [CollatzResearch.WordTrace]
  refine ⟨52163132323691475996884009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34775421549127650664589339 52163132323691475996884009)
  ·
    refine ⟨39122349242768606997663007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52163132323691475996884009 39122349242768606997663007)
    ·
      refine ⟨58683523864152910496494511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39122349242768606997663007 58683523864152910496494511)
      ·
        refine ⟨88025285796229365744741767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58683523864152910496494511 88025285796229365744741767)
        ·
          refine ⟨132037928694344048617112651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88025285796229365744741767 132037928694344048617112651)
          ·
            refine ⟨198056893041516072925668977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132037928694344048617112651 198056893041516072925668977)
            ·
              refine ⟨148542669781137054694251733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198056893041516072925668977 148542669781137054694251733)
              ·
                refine ⟨3481468822995399719396525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 148542669781137054694251733 3481468822995399719396525)
                ·
                  refine ⟨1305550808623274894773697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3481468822995399719396525 1305550808623274894773697)
                  ·
                    refine ⟨979163106467456171080273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1305550808623274894773697 979163106467456171080273)
                    ·
                      refine ⟨734372329850592128310205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979163106467456171080273 734372329850592128310205)
                      ·
                        rfl

theorem cell23_1430185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 2, 2].length) (baseStart_1430185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430185 prefixEnd_1430185 := by exact prefixLift 1430185
  have htrace : WordTrace (prefixWord ++ tailWord_1430185) baseStart_1430185 baseEnd_1430185 := by
    simpa [prefixWord, tailWord_1430185, baseEnd_1430185] using wordTrace_append hprefix tailTrace_1430185
  have hstable : (prefixWord ++ tailWord_1430185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430185).length < 2 ^ (prefixWord ++ tailWord_1430185).sum := by decide
  have hdescent : baseEnd_1430185 < baseStart_1430185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430205 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_1430205 : Nat := 118140960795 + 1430205 * 2 ^ 59
def prefixEnd_1430205 : Nat := 4983230072969 + 3 ^ 40 * 1430205 * 2
def baseEnd_1430205 : Nat := 734382599463682050060113

theorem tailTrace_1430205 : CollatzResearch.WordTrace tailWord_1430205 prefixEnd_1430205 734382599463682050060113 := by
  unfold tailWord_1430205
  simp only [CollatzResearch.WordTrace]
  refine ⟨52163861783619019412612069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34775907855746012941741379 52163861783619019412612069)
  ·
    refine ⟨9780724084428566139864763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52163861783619019412612069 9780724084428566139864763)
    ·
      refine ⟨14671086126642849209797145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9780724084428566139864763 14671086126642849209797145)
      ·
        refine ⟨11003314594982136907347859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14671086126642849209797145 11003314594982136907347859)
        ·
          refine ⟨16504971892473205361021789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11003314594982136907347859 16504971892473205361021789)
          ·
            refine ⟨6189364459677452010383171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16504971892473205361021789 6189364459677452010383171)
            ·
              refine ⟨9284046689516178015574757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6189364459677452010383171 9284046689516178015574757)
              ·
                refine ⟨1740758754284283377920267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9284046689516178015574757 1740758754284283377920267)
                ·
                  refine ⟨2611138131426425066880401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740758754284283377920267 2611138131426425066880401)
                  ·
                    refine ⟨1958353598569818800160301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2611138131426425066880401 1958353598569818800160301)
                    ·
                      refine ⟨734382599463682050060113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1958353598569818800160301 734382599463682050060113)
                      ·
                        rfl

theorem cell23_1430205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_1430205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430205 prefixEnd_1430205 := by exact prefixLift 1430205
  have htrace : WordTrace (prefixWord ++ tailWord_1430205) baseStart_1430205 baseEnd_1430205 := by
    simpa [prefixWord, tailWord_1430205, baseEnd_1430205] using wordTrace_append hprefix tailTrace_1430205
  have hstable : (prefixWord ++ tailWord_1430205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430205).length < 2 ^ (prefixWord ++ tailWord_1430205).sum := by decide
  have hdescent : baseEnd_1430205 < baseStart_1430205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430208 : List Nat := [2, 1, 1, 2, 4, 2, 4, 7]
def baseStart_1430208 : Nat := 118140960795 + 1430208 * 2 ^ 59
def prefixEnd_1430208 : Nat := 4983230072969 + 3 ^ 40 * 1430208 * 2
def baseEnd_1430208 : Nat := 27199412589097982900837

theorem tailTrace_1430208 : CollatzResearch.WordTrace tailWord_1430208 prefixEnd_1430208 27199412589097982900837 := by
  unfold tailWord_1430208
  simp only [CollatzResearch.WordTrace]
  refine ⟨26081985601304075462485639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34775980801738767283314185 26081985601304075462485639)
  ·
    refine ⟨39122978401956113193728459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26081985601304075462485639 39122978401956113193728459)
    ·
      refine ⟨58684467602934169790592689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39122978401956113193728459 58684467602934169790592689)
      ·
        refine ⟨44013350702200627342944517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58684467602934169790592689 44013350702200627342944517)
        ·
          refine ⟨8252503256662617626802097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44013350702200627342944517 8252503256662617626802097)
          ·
            refine ⟨6189377442496963220101573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8252503256662617626802097 6189377442496963220101573)
            ·
              refine ⟨1160508270468180603769045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6189377442496963220101573 1160508270468180603769045)
              ·
                refine ⟨27199412589097982900837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1160508270468180603769045 27199412589097982900837)
                ·
                  rfl

theorem cell23_1430208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 7].length) (baseStart_1430208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430208 prefixEnd_1430208 := by exact prefixLift 1430208
  have htrace : WordTrace (prefixWord ++ tailWord_1430208) baseStart_1430208 baseEnd_1430208 := by
    simpa [prefixWord, tailWord_1430208, baseEnd_1430208] using wordTrace_append hprefix tailTrace_1430208
  have hstable : (prefixWord ++ tailWord_1430208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430208).length < 2 ^ (prefixWord ++ tailWord_1430208).sum := by decide
  have hdescent : baseEnd_1430208 < baseStart_1430208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430236 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1430236 : Nat := 118140960795 + 1430236 * 2 ^ 59
def prefixEnd_1430236 : Nat := 4983230072969 + 3 ^ 40 * 1430236 * 2
def baseEnd_1430236 : Nat := 734398517363971428772471

theorem tailTrace_1430236 : CollatzResearch.WordTrace tailWord_1430236 prefixEnd_1430236 734398517363971428772471 := by
  unfold tailWord_1430236
  simp only [CollatzResearch.WordTrace]
  refine ⟨26082496223253355853495281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34776661631004474471327041 26082496223253355853495281)
  ·
    refine ⟨19561872167440016890121461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26082496223253355853495281 19561872167440016890121461)
    ·
      refine ⟨1833925515697501583448887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19561872167440016890121461 1833925515697501583448887)
      ·
        refine ⟨2750888273546252375173331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833925515697501583448887 2750888273546252375173331)
        ·
          refine ⟨4126332410319378562759997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750888273546252375173331 4126332410319378562759997)
          ·
            refine ⟨1547374653869766961034999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4126332410319378562759997 1547374653869766961034999)
            ·
              refine ⟨2321061980804650441552499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547374653869766961034999 2321061980804650441552499)
              ·
                refine ⟨3481592971206975662328749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321061980804650441552499 3481592971206975662328749)
                ·
                  refine ⟨1305597364202615873373281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3481592971206975662328749 1305597364202615873373281)
                  ·
                    refine ⟨979198023151961905029961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1305597364202615873373281 979198023151961905029961)
                    ·
                      refine ⟨734398517363971428772471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979198023151961905029961 734398517363971428772471)
                      ·
                        rfl

theorem cell23_1430236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1430236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430236 prefixEnd_1430236 := by exact prefixLift 1430236
  have htrace : WordTrace (prefixWord ++ tailWord_1430236) baseStart_1430236 baseEnd_1430236 := by
    simpa [prefixWord, tailWord_1430236, baseEnd_1430236] using wordTrace_append hprefix tailTrace_1430236
  have hstable : (prefixWord ++ tailWord_1430236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430236).length < 2 ^ (prefixWord ++ tailWord_1430236).sum := by decide
  have hdescent : baseEnd_1430236 < baseStart_1430236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430251 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 1, 8]
def baseStart_1430251 : Nat := 118140960795 + 1430251 * 2 ^ 59
def prefixEnd_1430251 : Nat := 4983230072969 + 3 ^ 40 * 1430251 * 2
def baseEnd_1430251 : Nat := 244802073191262956694967

theorem tailTrace_1430251 : CollatzResearch.WordTrace tailWord_1430251 prefixEnd_1430251 244802073191262956694967 := by
  unfold tailWord_1430251
  simp only [CollatzResearch.WordTrace]
  refine ⟨52165539541452369268786607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34777026360968246179191071 52165539541452369268786607)
  ·
    refine ⟨78248309312178553903179911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52165539541452369268786607 78248309312178553903179911)
    ·
      refine ⟨117372463968267830854769867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78248309312178553903179911 117372463968267830854769867)
      ·
        refine ⟨176058695952401746282154801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117372463968267830854769867 176058695952401746282154801)
        ·
          refine ⟨132044021964301309711616101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176058695952401746282154801 132044021964301309711616101)
          ·
            refine ⟨24758254118306495570928019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132044021964301309711616101 24758254118306495570928019)
            ·
              refine ⟨37137381177459743356392029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24758254118306495570928019 37137381177459743356392029)
              ·
                refine ⟨13926517941547403758647011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37137381177459743356392029 13926517941547403758647011)
                ·
                  refine ⟨20889776912321105637970517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13926517941547403758647011 20889776912321105637970517)
                  ·
                    refine ⟨244802073191262956694967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20889776912321105637970517 244802073191262956694967)
                    ·
                      rfl

theorem cell23_1430251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 8].length) (baseStart_1430251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430251 prefixEnd_1430251 := by exact prefixLift 1430251
  have htrace : WordTrace (prefixWord ++ tailWord_1430251) baseStart_1430251 baseEnd_1430251 := by
    simpa [prefixWord, tailWord_1430251, baseEnd_1430251] using wordTrace_append hprefix tailTrace_1430251
  have hstable : (prefixWord ++ tailWord_1430251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430251).length < 2 ^ (prefixWord ++ tailWord_1430251).sum := by decide
  have hdescent : baseEnd_1430251 < baseStart_1430251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430262 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_1430262 : Nat := 118140960795 + 1430262 * 2 ^ 59
def prefixEnd_1430262 : Nat := 4983230072969 + 3 ^ 40 * 1430262 * 2
def baseEnd_1430262 : Nat := 734411867860988327047351

theorem tailTrace_1430262 : CollatzResearch.WordTrace tailWord_1430262 prefixEnd_1430262 734411867860988327047351 := by
  unfold tailWord_1430262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260371296525782384214815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34777293829608345431624693 3260371296525782384214815)
  ·
    refine ⟨4890556944788673576322223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3260371296525782384214815 4890556944788673576322223)
    ·
      refine ⟨7335835417183010364483335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4890556944788673576322223 7335835417183010364483335)
      ·
        refine ⟨11003753125774515546725003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7335835417183010364483335 11003753125774515546725003)
        ·
          refine ⟨16505629688661773320087505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11003753125774515546725003 16505629688661773320087505)
          ·
            refine ⟨12379222266496329990065629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16505629688661773320087505 12379222266496329990065629)
            ·
              refine ⟨4642208349936123746274611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12379222266496329990065629 4642208349936123746274611)
              ·
                refine ⟨6963312524904185619411917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4642208349936123746274611 6963312524904185619411917)
                ·
                  refine ⟨2611242196839069607279469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6963312524904185619411917 2611242196839069607279469)
                  ·
                    refine ⟨979215823814651102729801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611242196839069607279469 979215823814651102729801)
                    ·
                      refine ⟨734411867860988327047351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979215823814651102729801 734411867860988327047351)
                      ·
                        rfl

theorem cell23_1430262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_1430262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430262 prefixEnd_1430262 := by exact prefixLift 1430262
  have htrace : WordTrace (prefixWord ++ tailWord_1430262) baseStart_1430262 baseEnd_1430262 := by
    simpa [prefixWord, tailWord_1430262, baseEnd_1430262] using wordTrace_append hprefix tailTrace_1430262
  have hstable : (prefixWord ++ tailWord_1430262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430262).length < 2 ^ (prefixWord ++ tailWord_1430262).sum := by decide
  have hdescent : baseEnd_1430262 < baseStart_1430262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430298 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 7]
def baseStart_1430298 : Nat := 118140960795 + 1430298 * 2 ^ 59
def prefixEnd_1430298 : Nat := 4983230072969 + 3 ^ 40 * 1430298 * 2
def baseEnd_1430298 : Nat := 81603372573838909577465

theorem tailTrace_1430298 : CollatzResearch.WordTrace tailWord_1430298 prefixEnd_1430298 81603372573838909577465 := by
  unfold tailWord_1430298
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041813443070524073936887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34778169181521397530498365 13041813443070524073936887)
  ·
    refine ⟨19562720164605786110905331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13041813443070524073936887 19562720164605786110905331)
    ·
      refine ⟨29344080246908679166357997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19562720164605786110905331 29344080246908679166357997)
      ·
        refine ⟨11004030092590754687384249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29344080246908679166357997 11004030092590754687384249)
        ·
          refine ⟨8253022569443066015538187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11004030092590754687384249 8253022569443066015538187)
          ·
            refine ⟨12379533854164599023307281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8253022569443066015538187 12379533854164599023307281)
            ·
              refine ⟨9284650390623449267480461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12379533854164599023307281 9284650390623449267480461)
              ·
                refine ⟨3481743896483793475305173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9284650390623449267480461 3481743896483793475305173)
                ·
                  refine ⟨81603372573838909577465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3481743896483793475305173 81603372573838909577465)
                  ·
                    rfl

theorem cell23_1430298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_1430298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430298 prefixEnd_1430298 := by exact prefixLift 1430298
  have htrace : WordTrace (prefixWord ++ tailWord_1430298) baseStart_1430298 baseEnd_1430298 := by
    simpa [prefixWord, tailWord_1430298, baseEnd_1430298] using wordTrace_append hprefix tailTrace_1430298
  have hstable : (prefixWord ++ tailWord_1430298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430298).length < 2 ^ (prefixWord ++ tailWord_1430298).sum := by decide
  have hdescent : baseEnd_1430298 < baseStart_1430298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430328 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 1, 7]
def baseStart_1430328 : Nat := 118140960795 + 1430328 * 2 ^ 59
def prefixEnd_1430328 : Nat := 4983230072969 + 3 ^ 40 * 1430328 * 2
def baseEnd_1430328 : Nat := 244815252528061689607349

theorem tailTrace_1430328 : CollatzResearch.WordTrace tailWord_1430328 prefixEnd_1430328 244815252528061689607349 := by
  unfold tailWord_1430328
  simp only [CollatzResearch.WordTrace]
  refine ⟨26084173981086705709669819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34778898641448940946226425 26084173981086705709669819)
  ·
    refine ⟨39126260971630058564504729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26084173981086705709669819 39126260971630058564504729)
    ·
      refine ⟨29344695728722543923378547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39126260971630058564504729 29344695728722543923378547)
      ·
        refine ⟨44017043593083815885067821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29344695728722543923378547 44017043593083815885067821)
        ·
          refine ⟨16506391347406430956900433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44017043593083815885067821 16506391347406430956900433)
          ·
            refine ⟨12379793510554823217675325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16506391347406430956900433 12379793510554823217675325)
            ·
              refine ⟨4642422566458058706628247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12379793510554823217675325 4642422566458058706628247)
              ·
                refine ⟨6963633849687088059942371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4642422566458058706628247 6963633849687088059942371)
                ·
                  refine ⟨10445450774530632089913557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6963633849687088059942371 10445450774530632089913557)
                  ·
                    refine ⟨244815252528061689607349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10445450774530632089913557 244815252528061689607349)
                    ·
                      rfl

theorem cell23_1430328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_1430328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430328 prefixEnd_1430328 := by exact prefixLift 1430328
  have htrace : WordTrace (prefixWord ++ tailWord_1430328) baseStart_1430328 baseEnd_1430328 := by
    simpa [prefixWord, tailWord_1430328, baseEnd_1430328] using wordTrace_append hprefix tailTrace_1430328
  have hstable : (prefixWord ++ tailWord_1430328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430328).length < 2 ^ (prefixWord ++ tailWord_1430328).sum := by decide
  have hdescent : baseEnd_1430328 < baseStart_1430328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430385 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 1, 4, 3]
def baseStart_1430385 : Nat := 118140960795 + 1430385 * 2 ^ 59
def prefixEnd_1430385 : Nat := 4983230072969 + 3 ^ 40 * 1430385 * 2
def baseEnd_1430385 : Nat := 734475025981491345809285

theorem tailTrace_1430385 : CollatzResearch.WordTrace tailWord_1430385 prefixEnd_1430385 734475025981491345809285 := by
  unfold tailWord_1430385
  simp only [CollatzResearch.WordTrace]
  refine ⟨52170426922966910154164609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34780284615311273436109739 52170426922966910154164609)
  ·
    refine ⟨39127820192225182615623457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52170426922966910154164609 39127820192225182615623457)
    ·
      refine ⟨29345865144168886961717593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39127820192225182615623457 29345865144168886961717593)
      ·
        refine ⟨22009398858126665221288195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29345865144168886961717593 22009398858126665221288195)
        ·
          refine ⟨33014098287189997831932293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22009398858126665221288195 33014098287189997831932293)
          ·
            refine ⟨6190143428848124593487305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33014098287189997831932293 6190143428848124593487305)
            ·
              refine ⟨4642607571636093445115479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6190143428848124593487305 4642607571636093445115479)
              ·
                refine ⟨6963911357454140167673219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4642607571636093445115479 6963911357454140167673219)
                ·
                  refine ⟨10445867036181210251509829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6963911357454140167673219 10445867036181210251509829)
                  ·
                    refine ⟨1958600069283976922158093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10445867036181210251509829 1958600069283976922158093)
                    ·
                      refine ⟨734475025981491345809285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1958600069283976922158093 734475025981491345809285)
                      ·
                        rfl

theorem cell23_1430385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_1430385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430385 prefixEnd_1430385 := by exact prefixLift 1430385
  have htrace : WordTrace (prefixWord ++ tailWord_1430385) baseStart_1430385 baseEnd_1430385 := by
    simpa [prefixWord, tailWord_1430385, baseEnd_1430385] using wordTrace_append hprefix tailTrace_1430385
  have hstable : (prefixWord ++ tailWord_1430385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430385).length < 2 ^ (prefixWord ++ tailWord_1430385).sum := by decide
  have hdescent : baseEnd_1430385 < baseStart_1430385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430392 : List Nat := [2, 1, 2, 1, 1, 1, 1, 9, 1, 4]
def baseStart_1430392 : Nat := 118140960795 + 1430392 * 2 ^ 59
def prefixEnd_1430392 : Nat := 4983230072969 + 3 ^ 40 * 1430392 * 2
def baseEnd_1430392 : Nat := 244826206782024272807251

theorem tailTrace_1430392 : CollatzResearch.WordTrace tailWord_1430392 prefixEnd_1430392 244826206782024272807251 := by
  unfold tailWord_1430392
  simp only [CollatzResearch.WordTrace]
  refine ⟨26085341116970775174834715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34780454822627700233112953 26085341116970775174834715)
  ·
    refine ⟨39128011675456162762252073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26085341116970775174834715 39128011675456162762252073)
    ·
      refine ⟨29346008756592122071689055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39128011675456162762252073 29346008756592122071689055)
      ·
        refine ⟨44019013134888183107533583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29346008756592122071689055 44019013134888183107533583)
        ·
          refine ⟨66028519702332274661300375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44019013134888183107533583 66028519702332274661300375)
          ·
            refine ⟨99042779553498411991950563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66028519702332274661300375 99042779553498411991950563)
            ·
              refine ⟨148564169330247617987925845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99042779553498411991950563 148564169330247617987925845)
              ·
                refine ⟨870493179669419636648003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 148564169330247617987925845 870493179669419636648003)
                ·
                  refine ⟨1305739769504129454972005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870493179669419636648003 1305739769504129454972005)
                  ·
                    refine ⟨244826206782024272807251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1305739769504129454972005 244826206782024272807251)
                    ·
                      rfl

theorem cell23_1430392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_1430392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430392 prefixEnd_1430392 := by exact prefixLift 1430392
  have htrace : WordTrace (prefixWord ++ tailWord_1430392) baseStart_1430392 baseEnd_1430392 := by
    simpa [prefixWord, tailWord_1430392, baseEnd_1430392] using wordTrace_append hprefix tailTrace_1430392
  have hstable : (prefixWord ++ tailWord_1430392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430392).length < 2 ^ (prefixWord ++ tailWord_1430392).sum := by decide
  have hdescent : baseEnd_1430392 < baseStart_1430392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430432 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 3, 1, 3]
def baseStart_1430432 : Nat := 118140960795 + 1430432 * 2 ^ 59
def prefixEnd_1430432 : Nat := 4983230072969 + 3 ^ 40 * 1430432 * 2
def baseEnd_1430432 : Nat := 734499159572252661921569

theorem tailTrace_1430432 : CollatzResearch.WordTrace tailWord_1430432 prefixEnd_1430432 734499159572252661921569 := by
  unfold tailWord_1430432
  simp only [CollatzResearch.WordTrace]
  refine ⟨26086070576898318590562775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34781427435864424787417033 26086070576898318590562775)
  ·
    refine ⟨39129105865347477885844163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26086070576898318590562775 39129105865347477885844163)
    ·
      refine ⟨58693658798021216828766245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39129105865347477885844163 58693658798021216828766245)
      ·
        refine ⟨11005061024628978155393671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58693658798021216828766245 11005061024628978155393671)
        ·
          refine ⟨16507591536943467233090507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11005061024628978155393671 16507591536943467233090507)
          ·
            refine ⟨24761387305415200849635761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16507591536943467233090507 24761387305415200849635761)
            ·
              refine ⟨18571040479061400637226821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24761387305415200849635761 18571040479061400637226821)
              ·
                refine ⟨3482070089824012619480029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18571040479061400637226821 3482070089824012619480029)
                ·
                  refine ⟨1305776283684004732305011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3482070089824012619480029 1305776283684004732305011)
                  ·
                    refine ⟨1958664425526007098457517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1305776283684004732305011 1958664425526007098457517)
                    ·
                      refine ⟨734499159572252661921569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1958664425526007098457517 734499159572252661921569)
                      ·
                        rfl

theorem cell23_1430432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_1430432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430432 prefixEnd_1430432 := by exact prefixLift 1430432
  have htrace : WordTrace (prefixWord ++ tailWord_1430432) baseStart_1430432 baseEnd_1430432 := by
    simpa [prefixWord, tailWord_1430432, baseEnd_1430432] using wordTrace_append hprefix tailTrace_1430432
  have hstable : (prefixWord ++ tailWord_1430432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430432).length < 2 ^ (prefixWord ++ tailWord_1430432).sum := by decide
  have hdescent : baseEnd_1430432 < baseStart_1430432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430482 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1430482 : Nat := 118140960795 + 1430482 * 2 ^ 59
def prefixEnd_1430482 : Nat := 4983230072969 + 3 ^ 40 * 1430482 * 2
def baseEnd_1430482 : Nat := 244841611201659155432113

theorem tailTrace_1430482 : CollatzResearch.WordTrace tailWord_1430482 prefixEnd_1430482 244841611201659155432113 := by
  unfold tailWord_1430482
  simp only [CollatzResearch.WordTrace]
  refine ⟨13043491200903873930111425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34782643202410330480297133 13043491200903873930111425)
  ·
    refine ⟨9782618400677905447583569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13043491200903873930111425 9782618400677905447583569)
    ·
      refine ⟨7336963800508429085687677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9782618400677905447583569 7336963800508429085687677)
      ·
        refine ⟨2751361425190660907132879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7336963800508429085687677 2751361425190660907132879)
        ·
          refine ⟨4127042137785991360699319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751361425190660907132879 4127042137785991360699319)
          ·
            refine ⟨6190563206678987041048979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127042137785991360699319 6190563206678987041048979)
            ·
              refine ⟨9285844810018480561573469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6190563206678987041048979 9285844810018480561573469)
              ·
                refine ⟨3482191803756930210590051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9285844810018480561573469 3482191803756930210590051)
                ·
                  refine ⟨5223287705635395315885077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482191803756930210590051 5223287705635395315885077)
                  ·
                    refine ⟨244841611201659155432113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5223287705635395315885077 244841611201659155432113)
                    ·
                      rfl

theorem cell23_1430482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1430482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430482 prefixEnd_1430482 := by exact prefixLift 1430482
  have htrace : WordTrace (prefixWord ++ tailWord_1430482) baseStart_1430482 baseEnd_1430482 := by
    simpa [prefixWord, tailWord_1430482, baseEnd_1430482] using wordTrace_append hprefix tailTrace_1430482
  have hstable : (prefixWord ++ tailWord_1430482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430482).length < 2 ^ (prefixWord ++ tailWord_1430482).sum := by decide
  have hdescent : baseEnd_1430482 < baseStart_1430482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430489 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 5, 2, 2]
def baseStart_1430489 : Nat := 118140960795 + 1430489 * 2 ^ 59
def prefixEnd_1430489 : Nat := 4983230072969 + 3 ^ 40 * 1430489 * 2
def baseEnd_1430489 : Nat := 734528427969558938908807

theorem tailTrace_1430489 : CollatzResearch.WordTrace tailWord_1430489 prefixEnd_1430489 734528427969558938908807 := by
  unfold tailWord_1430489
  simp only [CollatzResearch.WordTrace]
  refine ⟨52174220114590135915950521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34782813409726757277300347 52174220114590135915950521)
  ·
    refine ⟨39130665085942601936962891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52174220114590135915950521 39130665085942601936962891)
    ·
      refine ⟨58695997628913902905444337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39130665085942601936962891 58695997628913902905444337)
      ·
        refine ⟨44021998221685427179083253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58695997628913902905444337 44021998221685427179083253)
        ·
          refine ⟨4127062333283008798039055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44021998221685427179083253 4127062333283008798039055)
          ·
            refine ⟨6190593499924513197058583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127062333283008798039055 6190593499924513197058583)
            ·
              refine ⟨9285890249886769795587875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6190593499924513197058583 9285890249886769795587875)
              ·
                refine ⟨13928835374830154693381813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9285890249886769795587875 13928835374830154693381813)
                ·
                  refine ⟨1305828316390327002504545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13928835374830154693381813 1305828316390327002504545)
                  ·
                    refine ⟨979371237292745251878409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1305828316390327002504545 979371237292745251878409)
                    ·
                      refine ⟨734528427969558938908807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979371237292745251878409 734528427969558938908807)
                      ·
                        rfl

theorem cell23_1430489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_1430489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430489 prefixEnd_1430489 := by exact prefixLift 1430489
  have htrace : WordTrace (prefixWord ++ tailWord_1430489) baseStart_1430489 baseEnd_1430489 := by
    simpa [prefixWord, tailWord_1430489, baseEnd_1430489] using wordTrace_append hprefix tailTrace_1430489
  have hstable : (prefixWord ++ tailWord_1430489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430489).length < 2 ^ (prefixWord ++ tailWord_1430489).sum := by decide
  have hdescent : baseEnd_1430489 < baseStart_1430489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430506 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_1430506 : Nat := 118140960795 + 1430506 * 2 ^ 59
def prefixEnd_1430506 : Nat := 4983230072969 + 3 ^ 40 * 1430506 * 2
def baseEnd_1430506 : Nat := 734537157140685372396229

theorem tailTrace_1430506 : CollatzResearch.WordTrace tailWord_1430506 prefixEnd_1430506 734537157140685372396229 := by
  unfold tailWord_1430506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13043710038882136954829843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34783226770352365212879581 13043710038882136954829843)
  ·
    refine ⟨19565565058323205432244765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13043710038882136954829843 19565565058323205432244765)
    ·
      refine ⟨7337086896871202037091787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19565565058323205432244765 7337086896871202037091787)
      ·
        refine ⟨11005630345306803055637681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7337086896871202037091787 11005630345306803055637681)
        ·
          refine ⟨8254222758980102291728261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11005630345306803055637681 8254222758980102291728261)
          ·
            refine ⟨1547666767308769179699049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8254222758980102291728261 1547666767308769179699049)
            ·
              refine ⟨1160750075481576884774287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547666767308769179699049 1160750075481576884774287)
              ·
                refine ⟨1741125113222365327161431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160750075481576884774287 1741125113222365327161431)
                ·
                  refine ⟨2611687669833547990742147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741125113222365327161431 2611687669833547990742147)
                  ·
                    refine ⟨3917531504750321986113221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2611687669833547990742147 3917531504750321986113221)
                    ·
                      refine ⟨734537157140685372396229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3917531504750321986113221 734537157140685372396229)
                      ·
                        rfl

theorem cell23_1430506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_1430506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430506 prefixEnd_1430506 := by exact prefixLift 1430506
  have htrace : WordTrace (prefixWord ++ tailWord_1430506) baseStart_1430506 baseEnd_1430506 := by
    simpa [prefixWord, tailWord_1430506, baseEnd_1430506] using wordTrace_append hprefix tailTrace_1430506
  have hstable : (prefixWord ++ tailWord_1430506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430506).length < 2 ^ (prefixWord ++ tailWord_1430506).sum := by decide
  have hdescent : baseEnd_1430506 < baseStart_1430506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430539 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 1, 3, 3]
def baseStart_1430539 : Nat := 118140960795 + 1430539 * 2 ^ 59
def prefixEnd_1430539 : Nat := 4983230072969 + 3 ^ 40 * 1430539 * 2
def baseEnd_1430539 : Nat := 734554102002283743283577

theorem tailTrace_1430539 : CollatzResearch.WordTrace tailWord_1430539 prefixEnd_1430539 734554102002283743283577 := by
  unfold tailWord_1430539
  simp only [CollatzResearch.WordTrace]
  refine ⟨52176043764408994455270671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34784029176272662970180447 52176043764408994455270671)
  ·
    refine ⟨78264065646613491682906007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52176043764408994455270671 78264065646613491682906007)
    ·
      refine ⟨117396098469920237524359011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78264065646613491682906007 117396098469920237524359011)
      ·
        refine ⟨176094147704880356286538517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117396098469920237524359011 176094147704880356286538517)
        ·
          refine ⟨8254413173666266700931493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176094147704880356286538517 8254413173666266700931493)
          ·
            refine ⟨1547702470062425006424655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8254413173666266700931493 1547702470062425006424655)
            ·
              refine ⟨2321553705093637509636983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547702470062425006424655 2321553705093637509636983)
              ·
                refine ⟨3482330557640456264455475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321553705093637509636983 3482330557640456264455475)
                ·
                  refine ⟨5223495836460684396683213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482330557640456264455475 5223495836460684396683213)
                  ·
                    refine ⟨1958810938672756648756205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5223495836460684396683213 1958810938672756648756205)
                    ·
                      refine ⟨734554102002283743283577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1958810938672756648756205 734554102002283743283577)
                      ·
                        rfl

theorem cell23_1430539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 3, 3].length) (baseStart_1430539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430539 prefixEnd_1430539 := by exact prefixLift 1430539
  have htrace : WordTrace (prefixWord ++ tailWord_1430539) baseStart_1430539 baseEnd_1430539 := by
    simpa [prefixWord, tailWord_1430539, baseEnd_1430539] using wordTrace_append hprefix tailTrace_1430539
  have hstable : (prefixWord ++ tailWord_1430539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430539).length < 2 ^ (prefixWord ++ tailWord_1430539).sum := by decide
  have hdescent : baseEnd_1430539 < baseStart_1430539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430545 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_1430545 : Nat := 118140960795 + 1430545 * 2 ^ 59
def prefixEnd_1430545 : Nat := 4983230072969 + 3 ^ 40 * 1430545 * 2
def baseEnd_1430545 : Nat := 734557182886210719808549

theorem tailTrace_1430545 : CollatzResearch.WordTrace tailWord_1430545 prefixEnd_1430545 734557182886210719808549 := by
  unfold tailWord_1430545
  simp only [CollatzResearch.WordTrace]
  refine ⟨52176262602387257479989089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34784175068258171653326059 52176262602387257479989089)
  ·
    refine ⟨39132196951790443109991817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52176262602387257479989089 39132196951790443109991817)
    ·
      refine ⟨29349147713842832332493863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39132196951790443109991817 29349147713842832332493863)
      ·
        refine ⟨44023721570764248498740795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29349147713842832332493863 44023721570764248498740795)
        ·
          refine ⟨66035582356146372748111193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44023721570764248498740795 66035582356146372748111193)
          ·
            refine ⟨49526686767109779561083395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66035582356146372748111193 49526686767109779561083395)
            ·
              refine ⟨74290030150664669341625093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49526686767109779561083395 74290030150664669341625093)
              ·
                refine ⟨13929380653249625501554705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74290030150664669341625093 13929380653249625501554705)
                ·
                  refine ⟨10447035489937219126166029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13929380653249625501554705 10447035489937219126166029)
                  ·
                    refine ⟨3917638308726457172312261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10447035489937219126166029 3917638308726457172312261)
                    ·
                      refine ⟨734557182886210719808549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3917638308726457172312261 734557182886210719808549)
                      ·
                        rfl

theorem cell23_1430545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_1430545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430545 prefixEnd_1430545 := by exact prefixLift 1430545
  have htrace : WordTrace (prefixWord ++ tailWord_1430545) baseStart_1430545 baseEnd_1430545 := by
    simpa [prefixWord, tailWord_1430545, baseEnd_1430545] using wordTrace_append hprefix tailTrace_1430545
  have hstable : (prefixWord ++ tailWord_1430545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430545).length < 2 ^ (prefixWord ++ tailWord_1430545).sum := by decide
  have hdescent : baseEnd_1430545 < baseStart_1430545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430546 : List Nat := [3, 2, 5, 1, 1, 1, 1, 9]
def baseStart_1430546 : Nat := 118140960795 + 1430546 * 2 ^ 59
def prefixEnd_1430546 : Nat := 4983230072969 + 3 ^ 40 * 1430546 * 2
def baseEnd_1430546 : Nat := 27205840606180193181335

theorem tailTrace_1430546 : CollatzResearch.WordTrace tailWord_1430546 prefixEnd_1430546 27205840606180193181335 := by
  unfold tailWord_1430546
  simp only [CollatzResearch.WordTrace]
  refine ⟨13044074768845908662693873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34784199383589089767183661 13044074768845908662693873)
  ·
    refine ⟨9783056076634431497020405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13044074768845908662693873 9783056076634431497020405)
    ·
      refine ⟨917161507184477952845663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9783056076634431497020405 917161507184477952845663)
      ·
        refine ⟨1375742260776716929268495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917161507184477952845663 1375742260776716929268495)
        ·
          refine ⟨2063613391165075393902743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375742260776716929268495 2063613391165075393902743)
          ·
            refine ⟨3095420086747613090854115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2063613391165075393902743 3095420086747613090854115)
            ·
              refine ⟨4643130130121419636281173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3095420086747613090854115 4643130130121419636281173)
              ·
                refine ⟨27205840606180193181335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4643130130121419636281173 27205840606180193181335)
                ·
                  rfl

theorem cell23_1430546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 9].length) (baseStart_1430546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430546 prefixEnd_1430546 := by exact prefixLift 1430546
  have htrace : WordTrace (prefixWord ++ tailWord_1430546) baseStart_1430546 baseEnd_1430546 := by
    simpa [prefixWord, tailWord_1430546, baseEnd_1430546] using wordTrace_append hprefix tailTrace_1430546
  have hstable : (prefixWord ++ tailWord_1430546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430546).length < 2 ^ (prefixWord ++ tailWord_1430546).sum := by decide
  have hdescent : baseEnd_1430546 < baseStart_1430546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430557 : List Nat := [1, 4, 2, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_1430557 : Nat := 118140960795 + 1430557 * 2 ^ 59
def prefixEnd_1430557 : Nat := 4983230072969 + 3 ^ 40 * 1430557 * 2
def baseEnd_1430557 : Nat := 734563344654064672858495

theorem tailTrace_1430557 : CollatzResearch.WordTrace tailWord_1430557 prefixEnd_1430557 734563344654064672858495 := by
  unfold tailWord_1430557
  simp only [CollatzResearch.WordTrace]
  refine ⟨52176700278343783529425925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34784466852229189019617283 52176700278343783529425925)
  ·
    refine ⟨9783131302189459411767361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52176700278343783529425925 9783131302189459411767361)
    ·
      refine ⟨7337348476642094558825521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9783131302189459411767361 7337348476642094558825521)
      ·
        refine ⟨5503011357481570919119141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7337348476642094558825521 5503011357481570919119141)
        ·
          refine ⟨1031814629527794547334839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5503011357481570919119141 1031814629527794547334839)
          ·
            refine ⟨1547721944291691821002259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031814629527794547334839 1547721944291691821002259)
            ·
              refine ⟨2321582916437537731503389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547721944291691821002259 2321582916437537731503389)
              ·
                refine ⟨870593593664076649313771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2321582916437537731503389 870593593664076649313771)
                ·
                  refine ⟨1305890390496114973970657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870593593664076649313771 1305890390496114973970657)
                  ·
                    refine ⟨979417792872086230477993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1305890390496114973970657 979417792872086230477993)
                    ·
                      refine ⟨734563344654064672858495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979417792872086230477993 734563344654064672858495)
                      ·
                        rfl

theorem cell23_1430557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_1430557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430557 prefixEnd_1430557 := by exact prefixLift 1430557
  have htrace : WordTrace (prefixWord ++ tailWord_1430557) baseStart_1430557 baseEnd_1430557 := by
    simpa [prefixWord, tailWord_1430557, baseEnd_1430557] using wordTrace_append hprefix tailTrace_1430557
  have hstable : (prefixWord ++ tailWord_1430557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430557).length < 2 ^ (prefixWord ++ tailWord_1430557).sum := by decide
  have hdescent : baseEnd_1430557 < baseStart_1430557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430590 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_1430590 : Nat := 118140960795 + 1430590 * 2 ^ 59
def prefixEnd_1430590 : Nat := 4983230072969 + 3 ^ 40 * 1430590 * 2
def baseEnd_1430590 : Nat := 734580289515663043745843

theorem tailTrace_1430590 : CollatzResearch.WordTrace tailWord_1430590 prefixEnd_1430590 734580289515663043745843 := by
  unfold tailWord_1430590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6522237985903028770672153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34785269258149486776918149 6522237985903028770672153)
  ·
    refine ⟨4891678489427271578004115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6522237985903028770672153 4891678489427271578004115)
    ·
      refine ⟨7337517734140907367006173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4891678489427271578004115 7337517734140907367006173)
      ·
        refine ⟨2751569150302840262627315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7337517734140907367006173 2751569150302840262627315)
        ·
          refine ⟨4127353725454260393940973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751569150302840262627315 4127353725454260393940973)
          ·
            refine ⟨1547757647045347647727865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4127353725454260393940973 1547757647045347647727865)
            ·
              refine ⟨1160818235284010735795899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547757647045347647727865 1160818235284010735795899)
              ·
                refine ⟨1741227352926016103693849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160818235284010735795899 1741227352926016103693849)
                ·
                  refine ⟨1305920514694512077770387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1741227352926016103693849 1305920514694512077770387)
                  ·
                    refine ⟨1958880772041768116655581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1305920514694512077770387 1958880772041768116655581)
                    ·
                      refine ⟨734580289515663043745843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1958880772041768116655581 734580289515663043745843)
                      ·
                        rfl

theorem cell23_1430590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_1430590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430590 prefixEnd_1430590 := by exact prefixLift 1430590
  have htrace : WordTrace (prefixWord ++ tailWord_1430590) baseStart_1430590 baseEnd_1430590 := by
    simpa [prefixWord, tailWord_1430590, baseEnd_1430590] using wordTrace_append hprefix tailTrace_1430590
  have hstable : (prefixWord ++ tailWord_1430590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430590).length < 2 ^ (prefixWord ++ tailWord_1430590).sum := by decide
  have hdescent : baseEnd_1430590 < baseStart_1430590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430642 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1430642 : Nat := 118140960795 + 1430642 * 2 ^ 59
def prefixEnd_1430642 : Nat := 4983230072969 + 3 ^ 40 * 1430642 * 2
def baseEnd_1430642 : Nat := 734606990509696840295603

theorem tailTrace_1430642 : CollatzResearch.WordTrace tailWord_1430642 prefixEnd_1430642 734606990509696840295603 := by
  unfold tailWord_1430642
  simp only [CollatzResearch.WordTrace]
  refine ⟨13044950120758960761567545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34786533655357228697513453 13044950120758960761567545)
  ·
    refine ⟨9783712590569220571175659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13044950120758960761567545 9783712590569220571175659)
    ·
      refine ⟨14675568885853830856763489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9783712590569220571175659 14675568885853830856763489)
      ·
        refine ⟨11006676664390373142572617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14675568885853830856763489 11006676664390373142572617)
        ·
          refine ⟨8255007498292779856929463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11006676664390373142572617 8255007498292779856929463)
          ·
            refine ⟨12382511247439169785394195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8255007498292779856929463 12382511247439169785394195)
            ·
              refine ⟨18573766871158754678091293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12382511247439169785394195 18573766871158754678091293)
              ·
                refine ⟨6965162576684533004284235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18573766871158754678091293 6965162576684533004284235)
                ·
                  refine ⟨10447743865026799506426353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6965162576684533004284235 10447743865026799506426353)
                  ·
                    refine ⟨7835807898770099629819765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10447743865026799506426353 7835807898770099629819765)
                    ·
                      refine ⟨734606990509696840295603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7835807898770099629819765 734606990509696840295603)
                      ·
                        rfl

theorem cell23_1430642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1430642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430642 prefixEnd_1430642 := by exact prefixLift 1430642
  have htrace : WordTrace (prefixWord ++ tailWord_1430642) baseStart_1430642 baseEnd_1430642 := by
    simpa [prefixWord, tailWord_1430642, baseEnd_1430642] using wordTrace_append hprefix tailTrace_1430642
  have hstable : (prefixWord ++ tailWord_1430642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430642).length < 2 ^ (prefixWord ++ tailWord_1430642).sum := by decide
  have hdescent : baseEnd_1430642 < baseStart_1430642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430652 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_1430652 : Nat := 118140960795 + 1430652 * 2 ^ 59
def prefixEnd_1430652 : Nat := 4983230072969 + 3 ^ 40 * 1430652 * 2
def baseEnd_1430652 : Nat := 734612125316241801170557

theorem tailTrace_1430652 : CollatzResearch.WordTrace tailWord_1430652 prefixEnd_1430652 734612125316241801170557 := by
  unfold tailWord_1430652
  simp only [CollatzResearch.WordTrace]
  refine ⟨26090082606499807377067105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34786776808666409836089473 26090082606499807377067105)
  ·
    refine ⟨19567561954874855532800329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26090082606499807377067105 19567561954874855532800329)
    ·
      refine ⟨14675671466156141649600247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19567561954874855532800329 14675671466156141649600247)
      ·
        refine ⟨22013507199234212474400371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14675671466156141649600247 22013507199234212474400371)
        ·
          refine ⟨33020260798851318711600557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22013507199234212474400371 33020260798851318711600557)
          ·
            refine ⟨12382597799569244516850209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33020260798851318711600557 12382597799569244516850209)
            ·
              refine ⟨9286948349676933387637657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12382597799569244516850209 9286948349676933387637657)
              ·
                refine ⟨6965211262257700040728243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9286948349676933387637657 6965211262257700040728243)
                ·
                  refine ⟨10447816893386550061092365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6965211262257700040728243 10447816893386550061092365)
                  ·
                    refine ⟨3917931335019956272909637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10447816893386550061092365 3917931335019956272909637)
                    ·
                      refine ⟨734612125316241801170557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3917931335019956272909637 734612125316241801170557)
                      ·
                        rfl

theorem cell23_1430652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_1430652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430652 prefixEnd_1430652 := by exact prefixLift 1430652
  have htrace : WordTrace (prefixWord ++ tailWord_1430652) baseStart_1430652 baseEnd_1430652 := by
    simpa [prefixWord, tailWord_1430652, baseEnd_1430652] using wordTrace_append hprefix tailTrace_1430652
  have hstable : (prefixWord ++ tailWord_1430652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430652).length < 2 ^ (prefixWord ++ tailWord_1430652).sum := by decide
  have hdescent : baseEnd_1430652 < baseStart_1430652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430689 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1430689 : Nat := 118140960795 + 1430689 * 2 ^ 59
def prefixEnd_1430689 : Nat := 4983230072969 + 3 ^ 40 * 1430689 * 2
def baseEnd_1430689 : Nat := 734631124100458156407887

theorem tailTrace_1430689 : CollatzResearch.WordTrace tailWord_1430689 prefixEnd_1430689 734631124100458156407887 := by
  unfold tailWord_1430689
  simp only [CollatzResearch.WordTrace]
  refine ⟨52181514713865570073231121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34787676475910380048820747 52181514713865570073231121)
  ·
    refine ⟨39136136035399177554923341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52181514713865570073231121 39136136035399177554923341)
    ·
      refine ⟨14676051013274691583096253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39136136035399177554923341 14676051013274691583096253)
      ·
        refine ⟨5503519129978009343661095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14676051013274691583096253 5503519129978009343661095)
        ·
          refine ⟨8255278694967014015491643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503519129978009343661095 8255278694967014015491643)
          ·
            refine ⟨12382918042450521023237465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8255278694967014015491643 12382918042450521023237465)
            ·
              refine ⟨9287188531837890767428099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12382918042450521023237465 9287188531837890767428099)
              ·
                refine ⟨13930782797756836151142149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9287188531837890767428099 13930782797756836151142149)
                ·
                  refine ⟨2612021774579406778339153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13930782797756836151142149 2612021774579406778339153)
                  ·
                    refine ⟨1959016330934555083754365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2612021774579406778339153 1959016330934555083754365)
                    ·
                      refine ⟨734631124100458156407887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1959016330934555083754365 734631124100458156407887)
                      ·
                        rfl

theorem cell23_1430689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1430689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430689 prefixEnd_1430689 := by exact prefixLift 1430689
  have htrace : WordTrace (prefixWord ++ tailWord_1430689) baseStart_1430689 baseEnd_1430689 := by
    simpa [prefixWord, tailWord_1430689, baseEnd_1430689] using wordTrace_append hprefix tailTrace_1430689
  have hstable : (prefixWord ++ tailWord_1430689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430689).length < 2 ^ (prefixWord ++ tailWord_1430689).sum := by decide
  have hdescent : baseEnd_1430689 < baseStart_1430689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430753 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_1430753 : Nat := 118140960795 + 1430753 * 2 ^ 59
def prefixEnd_1430753 : Nat := 4983230072969 + 3 ^ 40 * 1430753 * 2
def baseEnd_1430753 : Nat := 734663986862345906007593

theorem tailTrace_1430753 : CollatzResearch.WordTrace tailWord_1430753 prefixEnd_1430753 734663986862345906007593 := by
  unfold tailWord_1430753
  simp only [CollatzResearch.WordTrace]
  refine ⟨52183848985633709003560913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34789232657089139335707275 52183848985633709003560913)
  ·
    refine ⟨39137886739225281752670685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52183848985633709003560913 39137886739225281752670685)
    ·
      refine ⟨14676707527209480657251507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39137886739225281752670685 14676707527209480657251507)
      ·
        refine ⟨22015061290814220985877261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14676707527209480657251507 22015061290814220985877261)
        ·
          refine ⟨8255647984055332869703973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22015061290814220985877261 8255647984055332869703973)
          ·
            refine ⟨1547933997010374913069495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8255647984055332869703973 1547933997010374913069495)
            ·
              refine ⟨2321900995515562369604243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547933997010374913069495 2321900995515562369604243)
              ·
                refine ⟨3482851493273343554406365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321900995515562369604243 3482851493273343554406365)
                ·
                  refine ⟨1306069309977503832902387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3482851493273343554406365 1306069309977503832902387)
                  ·
                    refine ⟨1959103964966255749353581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1306069309977503832902387 1959103964966255749353581)
                    ·
                      refine ⟨734663986862345906007593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1959103964966255749353581 734663986862345906007593)
                      ·
                        rfl

theorem cell23_1430753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_1430753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430753 prefixEnd_1430753 := by exact prefixLift 1430753
  have htrace : WordTrace (prefixWord ++ tailWord_1430753) baseStart_1430753 baseEnd_1430753 := by
    simpa [prefixWord, tailWord_1430753, baseEnd_1430753] using wordTrace_append hprefix tailTrace_1430753
  have hstable : (prefixWord ++ tailWord_1430753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430753).length < 2 ^ (prefixWord ++ tailWord_1430753).sum := by decide
  have hdescent : baseEnd_1430753 < baseStart_1430753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430789 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_1430789 : Nat := 118140960795 + 1430789 * 2 ^ 59
def prefixEnd_1430789 : Nat := 4983230072969 + 3 ^ 40 * 1430789 * 2
def baseEnd_1430789 : Nat := 734682472165907765157427

theorem tailTrace_1430789 : CollatzResearch.WordTrace tailWord_1430789 prefixEnd_1430789 734682472165907765157427 := by
  unfold tailWord_1430789
  simp only [CollatzResearch.WordTrace]
  refine ⟨52185162013503287151871421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34790108009002191434580947 52185162013503287151871421)
  ·
    refine ⟨19569435755063732681951783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52185162013503287151871421 19569435755063732681951783)
    ·
      refine ⟨29354153632595599022927675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19569435755063732681951783 29354153632595599022927675)
      ·
        refine ⟨44031230448893398534391513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29354153632595599022927675 44031230448893398534391513)
        ·
          refine ⟨33023422836670048900793635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44031230448893398534391513 33023422836670048900793635)
          ·
            refine ⟨49535134255005073351190453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33023422836670048900793635 49535134255005073351190453)
            ·
              refine ⟨4643918836406725626674105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49535134255005073351190453 4643918836406725626674105)
              ·
                refine ⟨3482939127305044220005579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4643918836406725626674105 3482939127305044220005579)
                ·
                  refine ⟨5224408690957566330008369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482939127305044220005579 5224408690957566330008369)
                  ·
                    refine ⟨3918306518218174747506277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5224408690957566330008369 3918306518218174747506277)
                    ·
                      refine ⟨734682472165907765157427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3918306518218174747506277 734682472165907765157427)
                      ·
                        rfl

theorem cell23_1430789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_1430789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430789 prefixEnd_1430789 := by exact prefixLift 1430789
  have htrace : WordTrace (prefixWord ++ tailWord_1430789) baseStart_1430789 baseEnd_1430789 := by
    simpa [prefixWord, tailWord_1430789, baseEnd_1430789] using wordTrace_append hprefix tailTrace_1430789
  have hstable : (prefixWord ++ tailWord_1430789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430789).length < 2 ^ (prefixWord ++ tailWord_1430789).sum := by decide
  have hdescent : baseEnd_1430789 < baseStart_1430789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430796 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 1, 1, 5]
def baseStart_1430796 : Nat := 118140960795 + 1430796 * 2 ^ 59
def prefixEnd_1430796 : Nat := 4983230072969 + 3 ^ 40 * 1430796 * 2
def baseEnd_1430796 : Nat := 734686066530489237769895

theorem tailTrace_1430796 : CollatzResearch.WordTrace tailWord_1430796 prefixEnd_1430796 734686066530489237769895 := by
  unfold tailWord_1430796
  simp only [CollatzResearch.WordTrace]
  refine ⟨26092708662238963673688121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34790278216318618231584161 26092708662238963673688121)
  ·
    refine ⟨19569531496679222755266091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26092708662238963673688121 19569531496679222755266091)
    ·
      refine ⟨29354297245018834132899137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19569531496679222755266091 29354297245018834132899137)
      ·
        refine ⟨22015722933764125599674353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29354297245018834132899137 22015722933764125599674353)
        ·
          refine ⟨16511792200323094199755765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22015722933764125599674353 16511792200323094199755765)
          ·
            refine ⟨1547980518780290081227103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16511792200323094199755765 1547980518780290081227103)
            ·
              refine ⟨2321970778170435121840655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547980518780290081227103 2321970778170435121840655)
              ·
                refine ⟨3482956167255652682760983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321970778170435121840655 3482956167255652682760983)
                ·
                  refine ⟨5224434250883479024141475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482956167255652682760983 5224434250883479024141475)
                  ·
                    refine ⟨7836651376325218536212213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5224434250883479024141475 7836651376325218536212213)
                    ·
                      refine ⟨734686066530489237769895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7836651376325218536212213 734686066530489237769895)
                      ·
                        rfl

theorem cell23_1430796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_1430796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430796 prefixEnd_1430796 := by exact prefixLift 1430796
  have htrace : WordTrace (prefixWord ++ tailWord_1430796) baseStart_1430796 baseEnd_1430796 := by
    simpa [prefixWord, tailWord_1430796, baseEnd_1430796] using wordTrace_append hprefix tailTrace_1430796
  have hstable : (prefixWord ++ tailWord_1430796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430796).length < 2 ^ (prefixWord ++ tailWord_1430796).sum := by decide
  have hdescent : baseEnd_1430796 < baseStart_1430796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430816 : List Nat := [2, 1, 1, 5, 3, 2, 1, 8]
def baseStart_1430816 : Nat := 118140960795 + 1430816 * 2 ^ 59
def prefixEnd_1430816 : Nat := 4983230072969 + 3 ^ 40 * 1430816 * 2
def baseEnd_1430816 : Nat := 27210975412725154056289

theorem tailTrace_1430816 : CollatzResearch.WordTrace tailWord_1430816 prefixEnd_1430816 27210975412725154056289 := by
  unfold tailWord_1430816
  simp only [CollatzResearch.WordTrace]
  refine ⟨26093073392202735381552151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34790764522936980508736201 26093073392202735381552151)
  ·
    refine ⟨39139610088304103072328227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26093073392202735381552151 39139610088304103072328227)
    ·
      refine ⟨58709415132456154608492341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39139610088304103072328227 58709415132456154608492341)
      ·
        refine ⟨5504007668667764494546157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58709415132456154608492341 5504007668667764494546157)
        ·
          refine ⟨2064002875750411685454809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5504007668667764494546157 2064002875750411685454809)
          ·
            refine ⟨1548002156812808764091107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2064002875750411685454809 1548002156812808764091107)
            ·
              refine ⟨2322003235219213146136661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548002156812808764091107 2322003235219213146136661)
              ·
                refine ⟨27210975412725154056289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2322003235219213146136661 27210975412725154056289)
                ·
                  rfl

theorem cell23_1430816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 8].length) (baseStart_1430816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430816 prefixEnd_1430816 := by exact prefixLift 1430816
  have htrace : WordTrace (prefixWord ++ tailWord_1430816) baseStart_1430816 baseEnd_1430816 := by
    simpa [prefixWord, tailWord_1430816, baseEnd_1430816] using wordTrace_append hprefix tailTrace_1430816
  have hstable : (prefixWord ++ tailWord_1430816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430816).length < 2 ^ (prefixWord ++ tailWord_1430816).sum := by decide
  have hdescent : baseEnd_1430816 < baseStart_1430816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430854 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1430854 : Nat := 118140960795 + 1430854 * 2 ^ 59
def prefixEnd_1430854 : Nat := 4983230072969 + 3 ^ 40 * 1430854 * 2
def baseEnd_1430854 : Nat := 244905282802816670281543

theorem tailTrace_1430854 : CollatzResearch.WordTrace tailWord_1430854 prefixEnd_1430854 244905282802816670281543 := by
  unfold tailWord_1430854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630860398695868851655863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34791688505511868835325077 1630860398695868851655863)
  ·
    refine ⟨2446290598043803277483795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1630860398695868851655863 2446290598043803277483795)
    ·
      refine ⟨3669435897065704916225693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2446290598043803277483795 3669435897065704916225693)
      ·
        refine ⟨1376038461399639343584635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3669435897065704916225693 1376038461399639343584635)
        ·
          refine ⟨2064057692099459015376953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376038461399639343584635 2064057692099459015376953)
          ·
            refine ⟨1548043269074594261532715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2064057692099459015376953 1548043269074594261532715)
            ·
              refine ⟨2322064903611891392299073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548043269074594261532715 2322064903611891392299073)
              ·
                refine ⟨1741548677708918544224305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322064903611891392299073 1741548677708918544224305)
                ·
                  refine ⟨1306161508281688908168229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1741548677708918544224305 1306161508281688908168229)
                  ·
                    refine ⟨244905282802816670281543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1306161508281688908168229 244905282802816670281543)
                    ·
                      rfl

theorem cell23_1430854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1430854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430854 prefixEnd_1430854 := by exact prefixLift 1430854
  have htrace : WordTrace (prefixWord ++ tailWord_1430854) baseStart_1430854 baseEnd_1430854 := by
    simpa [prefixWord, tailWord_1430854, baseEnd_1430854] using wordTrace_append hprefix tailTrace_1430854
  have hstable : (prefixWord ++ tailWord_1430854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430854).length < 2 ^ (prefixWord ++ tailWord_1430854).sum := by decide
  have hdescent : baseEnd_1430854 < baseStart_1430854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430860 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 2, 1, 3]
def baseStart_1430860 : Nat := 118140960795 + 1430860 * 2 ^ 59
def prefixEnd_1430860 : Nat := 4983230072969 + 3 ^ 40 * 1430860 * 2
def baseEnd_1430860 : Nat := 734718929292376987369601

theorem tailTrace_1430860 : CollatzResearch.WordTrace tailWord_1430860 prefixEnd_1430860 734718929292376987369601 := by
  unfold tailWord_1430860
  simp only [CollatzResearch.WordTrace]
  refine ⟨26093875798123033138853017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34791834397497377518470689 26093875798123033138853017)
  ·
    refine ⟨19570406848592274854139763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26093875798123033138853017 19570406848592274854139763)
    ·
      refine ⟨29355610272888412281209645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19570406848592274854139763 29355610272888412281209645)
      ·
        refine ⟨11008353852333154605453617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29355610272888412281209645 11008353852333154605453617)
        ·
          refine ⟨8256265389249865954090213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11008353852333154605453617 8256265389249865954090213)
          ·
            refine ⟨1548049760484349866391915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8256265389249865954090213 1548049760484349866391915)
            ·
              refine ⟨2322074640726524799587873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548049760484349866391915 2322074640726524799587873)
              ·
                refine ⟨1741555980544893599690905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322074640726524799587873 1741555980544893599690905)
                ·
                  refine ⟨1306166985408670199768179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1741555980544893599690905 1306166985408670199768179)
                  ·
                    refine ⟨1959250478113005299652269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1306166985408670199768179 1959250478113005299652269)
                    ·
                      refine ⟨734718929292376987369601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1959250478113005299652269 734718929292376987369601)
                      ·
                        rfl

theorem cell23_1430860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_1430860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430860 prefixEnd_1430860 := by exact prefixLift 1430860
  have htrace : WordTrace (prefixWord ++ tailWord_1430860) baseStart_1430860 baseEnd_1430860 := by
    simpa [prefixWord, tailWord_1430860, baseEnd_1430860] using wordTrace_append hprefix tailTrace_1430860
  have hstable : (prefixWord ++ tailWord_1430860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430860).length < 2 ^ (prefixWord ++ tailWord_1430860).sum := by decide
  have hdescent : baseEnd_1430860 < baseStart_1430860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430883 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 1, 4, 2]
def baseStart_1430883 : Nat := 118140960795 + 1430883 * 2 ^ 59
def prefixEnd_1430883 : Nat := 4983230072969 + 3 ^ 40 * 1430883 * 2
def baseEnd_1430883 : Nat := 734730739347430397381995

theorem tailTrace_1430883 : CollatzResearch.WordTrace tailWord_1430883 prefixEnd_1430883 734730739347430397381995 := by
  unfold tailWord_1430883
  simp only [CollatzResearch.WordTrace]
  refine ⟨52188590475162741205793303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34792393650108494137195535 52188590475162741205793303)
  ·
    refine ⟨78282885712744111808689955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52188590475162741205793303 78282885712744111808689955)
    ·
      refine ⟨117424328569116167713034933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78282885712744111808689955 117424328569116167713034933)
      ·
        refine ⟨11008530803354640723097025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117424328569116167713034933 11008530803354640723097025)
        ·
          refine ⟨8256398102515980542322769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11008530803354640723097025 8256398102515980542322769)
          ·
            refine ⟨6192298576886985406742077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8256398102515980542322769 6192298576886985406742077)
            ·
              refine ⟨2322111966332619527528279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6192298576886985406742077 2322111966332619527528279)
              ·
                refine ⟨3483167949498929291292419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322111966332619527528279 3483167949498929291292419)
                ·
                  refine ⟨5224751924248393936938629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483167949498929291292419 5224751924248393936938629)
                  ·
                    refine ⟨979640985796573863175993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5224751924248393936938629 979640985796573863175993)
                    ·
                      refine ⟨734730739347430397381995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979640985796573863175993 734730739347430397381995)
                      ·
                        rfl

theorem cell23_1430883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_1430883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430883 prefixEnd_1430883 := by exact prefixLift 1430883
  have htrace : WordTrace (prefixWord ++ tailWord_1430883) baseStart_1430883 baseEnd_1430883 := by
    simpa [prefixWord, tailWord_1430883, baseEnd_1430883] using wordTrace_append hprefix tailTrace_1430883
  have hstable : (prefixWord ++ tailWord_1430883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430883).length < 2 ^ (prefixWord ++ tailWord_1430883).sum := by decide
  have hdescent : baseEnd_1430883 < baseStart_1430883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430923 : List Nat := [1, 1, 1, 1, 4, 3, 5, 2, 5]
def baseStart_1430923 : Nat := 118140960795 + 1430923 * 2 ^ 59
def prefixEnd_1430923 : Nat := 4983230072969 + 3 ^ 40 * 1430923 * 2
def baseEnd_1430923 : Nat := 81639030952623360097979

theorem tailTrace_1430923 : CollatzResearch.WordTrace tailWord_1430923 prefixEnd_1430923 81639030952623360097979 := by
  unfold tailWord_1430923
  simp only [CollatzResearch.WordTrace]
  refine ⟨52190049395017828037249423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34793366263345218691499615 52190049395017828037249423)
  ·
    refine ⟨78285074092526742055874135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52190049395017828037249423 78285074092526742055874135)
    ·
      refine ⟨117427611138790113083811203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78285074092526742055874135 117427611138790113083811203)
      ·
        refine ⟨176141416708185169625716805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117427611138790113083811203 176141416708185169625716805)
        ·
          refine ⟨33026515632784719304821901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176141416708185169625716805 33026515632784719304821901)
          ·
            refine ⟨12384943362294269739308213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33026515632784719304821901 12384943362294269739308213)
            ·
              refine ⟨1161088440215087788060145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12384943362294269739308213 1161088440215087788060145)
              ·
                refine ⟨870816330161315841045109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161088440215087788060145 870816330161315841045109)
                ·
                  refine ⟨81639030952623360097979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 870816330161315841045109 81639030952623360097979)
                  ·
                    rfl

theorem cell23_1430923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 5].length) (baseStart_1430923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430923 prefixEnd_1430923 := by exact prefixLift 1430923
  have htrace : WordTrace (prefixWord ++ tailWord_1430923) baseStart_1430923 baseEnd_1430923 := by
    simpa [prefixWord, tailWord_1430923, baseEnd_1430923] using wordTrace_append hprefix tailTrace_1430923
  have hstable : (prefixWord ++ tailWord_1430923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430923).length < 2 ^ (prefixWord ++ tailWord_1430923).sum := by decide
  have hdescent : baseEnd_1430923 < baseStart_1430923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430929 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_1430929 : Nat := 118140960795 + 1430929 * 2 ^ 59
def prefixEnd_1430929 : Nat := 4983230072969 + 3 ^ 40 * 1430929 * 2
def baseEnd_1430929 : Nat := 734754359457537217406783

theorem tailTrace_1430929 : CollatzResearch.WordTrace tailWord_1430929 prefixEnd_1430929 734754359457537217406783 := by
  unfold tailWord_1430929
  simp only [CollatzResearch.WordTrace]
  refine ⟨52190268232996091061967841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34793512155330727374645227 52190268232996091061967841)
  ·
    refine ⟨39142701174747068296475881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52190268232996091061967841 39142701174747068296475881)
    ·
      refine ⟨29357025881060301222356911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39142701174747068296475881 29357025881060301222356911)
      ·
        refine ⟨44035538821590451833535367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29357025881060301222356911 44035538821590451833535367)
        ·
          refine ⟨66053308232385677750303051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44035538821590451833535367 66053308232385677750303051)
          ·
            refine ⟨99079962348578516625454577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66053308232385677750303051 99079962348578516625454577)
            ·
              refine ⟨74309971761433887469090933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99079962348578516625454577 74309971761433887469090933)
              ·
                refine ⟨6966559852634426950227275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74309971761433887469090933 6966559852634426950227275)
                ·
                  refine ⟨10449839778951640425340913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6966559852634426950227275 10449839778951640425340913)
                  ·
                    refine ⟨7837379834213730319005685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10449839778951640425340913 7837379834213730319005685)
                    ·
                      refine ⟨734754359457537217406783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7837379834213730319005685 734754359457537217406783)
                      ·
                        rfl

theorem cell23_1430929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_1430929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430929 prefixEnd_1430929 := by exact prefixLift 1430929
  have htrace : WordTrace (prefixWord ++ tailWord_1430929) baseStart_1430929 baseEnd_1430929 := by
    simpa [prefixWord, tailWord_1430929, baseEnd_1430929] using wordTrace_append hprefix tailTrace_1430929
  have hstable : (prefixWord ++ tailWord_1430929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430929).length < 2 ^ (prefixWord ++ tailWord_1430929).sum := by decide
  have hdescent : baseEnd_1430929 < baseStart_1430929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430956 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_1430956 : Nat := 118140960795 + 1430956 * 2 ^ 59
def prefixEnd_1430956 : Nat := 4983230072969 + 3 ^ 40 * 1430956 * 2
def baseEnd_1430956 : Nat := 734768223435208611769159

theorem tailTrace_1430956 : CollatzResearch.WordTrace tailWord_1430956 prefixEnd_1430956 734768223435208611769159 := by
  unfold tailWord_1430956
  simp only [CollatzResearch.WordTrace]
  refine ⟨26095626501949137336600361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34794168669265516448800481 26095626501949137336600361)
  ·
    refine ⟨19571719876461853002450271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26095626501949137336600361 19571719876461853002450271)
    ·
      refine ⟨29357579814692779503675407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19571719876461853002450271 29357579814692779503675407)
      ·
        refine ⟨44036369722039169255513111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29357579814692779503675407 44036369722039169255513111)
        ·
          refine ⟨66054554583058753883269667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44036369722039169255513111 66054554583058753883269667)
          ·
            refine ⟨99081831874588130824904501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66054554583058753883269667 99081831874588130824904501)
            ·
              refine ⟨9288921738242637264834797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99081831874588130824904501 9288921738242637264834797)
              ·
                refine ⟨3483345651840988974313049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9288921738242637264834797 3483345651840988974313049)
                ·
                  refine ⟨2612509238880741730734787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3483345651840988974313049 2612509238880741730734787)
                  ·
                    refine ⟨3918763858321112596102181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2612509238880741730734787 3918763858321112596102181)
                    ·
                      refine ⟨734768223435208611769159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3918763858321112596102181 734768223435208611769159)
                      ·
                        rfl

theorem cell23_1430956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_1430956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430956 prefixEnd_1430956 := by exact prefixLift 1430956
  have htrace : WordTrace (prefixWord ++ tailWord_1430956) baseStart_1430956 baseEnd_1430956 := by
    simpa [prefixWord, tailWord_1430956, baseEnd_1430956] using wordTrace_append hprefix tailTrace_1430956
  have hstable : (prefixWord ++ tailWord_1430956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430956).length < 2 ^ (prefixWord ++ tailWord_1430956).sum := by decide
  have hdescent : baseEnd_1430956 < baseStart_1430956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430973 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 2, 4, 2]
def baseStart_1430973 : Nat := 118140960795 + 1430973 * 2 ^ 59
def prefixEnd_1430973 : Nat := 4983230072969 + 3 ^ 40 * 1430973 * 2
def baseEnd_1430973 : Nat := 734776952606335045256581

theorem tailTrace_1430973 : CollatzResearch.WordTrace tailWord_1430973 prefixEnd_1430973 734776952606335045256581 := by
  unfold tailWord_1430973
  simp only [CollatzResearch.WordTrace]
  refine ⟨52191873044836686576569573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34794582029891124384379715 52191873044836686576569573)
  ·
    refine ⟨9785976195906878733106795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52191873044836686576569573 9785976195906878733106795)
    ·
      refine ⟨14678964293860318099660193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9785976195906878733106795 14678964293860318099660193)
      ·
        refine ⟨11009223220395238574745145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14678964293860318099660193 11009223220395238574745145)
        ·
          refine ⟨8256917415296428931058859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11009223220395238574745145 8256917415296428931058859)
          ·
            refine ⟨12385376122944643396588289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8256917415296428931058859 12385376122944643396588289)
            ·
              refine ⟨9289032092208482547441217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12385376122944643396588289 9289032092208482547441217)
              ·
                refine ⟨6966774069156361910580913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9289032092208482547441217 6966774069156361910580913)
                ·
                  refine ⟨5225080551867271432935685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6966774069156361910580913 5225080551867271432935685)
                  ·
                    refine ⟨979702603475113393675441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5225080551867271432935685 979702603475113393675441)
                    ·
                      refine ⟨734776952606335045256581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979702603475113393675441 734776952606335045256581)
                      ·
                        rfl

theorem cell23_1430973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_1430973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430973 prefixEnd_1430973 := by exact prefixLift 1430973
  have htrace : WordTrace (prefixWord ++ tailWord_1430973) baseStart_1430973 baseEnd_1430973 := by
    simpa [prefixWord, tailWord_1430973, baseEnd_1430973] using wordTrace_append hprefix tailTrace_1430973
  have hstable : (prefixWord ++ tailWord_1430973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430973).length < 2 ^ (prefixWord ++ tailWord_1430973).sum := by decide
  have hdescent : baseEnd_1430973 < baseStart_1430973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430979 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 8]
def baseStart_1430979 : Nat := 118140960795 + 1430979 * 2 ^ 59
def prefixEnd_1430979 : Nat := 4983230072969 + 3 ^ 40 * 1430979 * 2
def baseEnd_1430979 : Nat := 81642225943362446864617

theorem tailTrace_1430979 : CollatzResearch.WordTrace tailWord_1430979 prefixEnd_1430979 81642225943362446864617 := by
  unfold tailWord_1430979
  simp only [CollatzResearch.WordTrace]
  refine ⟨52192091882814949601287991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34794727921876633067525327 52192091882814949601287991)
  ·
    refine ⟨78288137824222424401931987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52192091882814949601287991 78288137824222424401931987)
    ·
      refine ⟨117432206736333636602897981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78288137824222424401931987 117432206736333636602897981)
      ·
        refine ⟨44037077526125113726086743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117432206736333636602897981 44037077526125113726086743)
        ·
          refine ⟨66055616289187670589130115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44037077526125113726086743 66055616289187670589130115)
          ·
            refine ⟨99083424433781505883695173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66055616289187670589130115 99083424433781505883695173)
            ·
              refine ⟨18578142081334032353192845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99083424433781505883695173 18578142081334032353192845)
              ·
                refine ⟨6966803280500262132447317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18578142081334032353192845 6966803280500262132447317)
                ·
                  refine ⟨81642225943362446864617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6966803280500262132447317 81642225943362446864617)
                  ·
                    rfl

theorem cell23_1430979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 8].length) (baseStart_1430979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1430979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1430979 prefixEnd_1430979 := by exact prefixLift 1430979
  have htrace : WordTrace (prefixWord ++ tailWord_1430979) baseStart_1430979 baseEnd_1430979 := by
    simpa [prefixWord, tailWord_1430979, baseEnd_1430979] using wordTrace_append hprefix tailTrace_1430979
  have hstable : (prefixWord ++ tailWord_1430979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430979).length < 2 ^ (prefixWord ++ tailWord_1430979).sum := by decide
  have hdescent : baseEnd_1430979 < baseStart_1430979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431030 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_1431030 : Nat := 118140960795 + 1431030 * 2 ^ 59
def prefixEnd_1431030 : Nat := 4983230072969 + 3 ^ 40 * 1431030 * 2
def baseEnd_1431030 : Nat := 81645135667071258027091

theorem tailTrace_1431030 : CollatzResearch.WordTrace tailWord_1431030 prefixEnd_1431030 81645135667071258027091 := by
  unfold tailWord_1431030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262122000351886581962159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34795968003753456874263029 3262122000351886581962159)
  ·
    refine ⟨4893183000527829872943239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3262122000351886581962159 4893183000527829872943239)
    ·
      refine ⟨7339774500791744809414859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4893183000527829872943239 7339774500791744809414859)
      ·
        refine ⟨11009661751187617214122289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7339774500791744809414859 11009661751187617214122289)
        ·
          refine ⟨8257246313390712910591717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11009661751187617214122289 8257246313390712910591717)
          ·
            refine ⟨1548233683760758670735947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8257246313390712910591717 1548233683760758670735947)
            ·
              refine ⟨2322350525641138006103921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548233683760758670735947 2322350525641138006103921)
              ·
                refine ⟨1741762894230853504577941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322350525641138006103921 1741762894230853504577941)
                ·
                  refine ⟨81645135667071258027091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1741762894230853504577941 81645135667071258027091)
                  ·
                    rfl

theorem cell23_1431030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_1431030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431030 prefixEnd_1431030 := by exact prefixLift 1431030
  have htrace : WordTrace (prefixWord ++ tailWord_1431030) baseStart_1431030 baseEnd_1431030 := by
    simpa [prefixWord, tailWord_1431030, baseEnd_1431030] using wordTrace_append hprefix tailTrace_1431030
  have hstable : (prefixWord ++ tailWord_1431030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431030).length < 2 ^ (prefixWord ++ tailWord_1431030).sum := by decide
  have hdescent : baseEnd_1431030 < baseStart_1431030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431033 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 4, 3, 2]
def baseStart_1431033 : Nat := 118140960795 + 1431033 * 2 ^ 59
def prefixEnd_1431033 : Nat := 4983230072969 + 3 ^ 40 * 1431033 * 2
def baseEnd_1431033 : Nat := 734807761445604810506305

theorem tailTrace_1431033 : CollatzResearch.WordTrace tailWord_1431033 prefixEnd_1431033 734807761445604810506305 := by
  unfold tailWord_1431033
  simp only [CollatzResearch.WordTrace]
  refine ⟨52194061424619316823753753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34796040949746211215835835 52194061424619316823753753)
  ·
    refine ⟨39145546068464487617815315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52194061424619316823753753 39145546068464487617815315)
    ·
      refine ⟨58718319102696731426722973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39145546068464487617815315 58718319102696731426722973)
      ·
        refine ⟨22019369663511274285021115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58718319102696731426722973 22019369663511274285021115)
        ·
          refine ⟨33029054495266911427531673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22019369663511274285021115 33029054495266911427531673)
          ·
            refine ⟨24771790871450183570648755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33029054495266911427531673 24771790871450183570648755)
            ·
              refine ⟨37157686307175275355973133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24771790871450183570648755 37157686307175275355973133)
              ·
                refine ⟨13934132365190728258489925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37157686307175275355973133 13934132365190728258489925)
                ·
                  refine ⟨2612649818473261548466861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13934132365190728258489925 2612649818473261548466861)
                  ·
                    refine ⟨979743681927473080675073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612649818473261548466861 979743681927473080675073)
                    ·
                      refine ⟨734807761445604810506305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979743681927473080675073 734807761445604810506305)
                      ·
                        rfl

theorem cell23_1431033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_1431033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431033 prefixEnd_1431033 := by exact prefixLift 1431033
  have htrace : WordTrace (prefixWord ++ tailWord_1431033) baseStart_1431033 baseEnd_1431033 := by
    simpa [prefixWord, tailWord_1431033, baseEnd_1431033] using wordTrace_append hprefix tailTrace_1431033
  have hstable : (prefixWord ++ tailWord_1431033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431033).length < 2 ^ (prefixWord ++ tailWord_1431033).sum := by decide
  have hdescent : baseEnd_1431033 < baseStart_1431033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431066 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1431066 : Nat := 118140960795 + 1431066 * 2 ^ 59
def prefixEnd_1431066 : Nat := 4983230072969 + 3 ^ 40 * 1431066 * 2
def baseEnd_1431066 : Nat := 734824706307203181393653

theorem tailTrace_1431066 : CollatzResearch.WordTrace tailWord_1431066 prefixEnd_1431066 734824706307203181393653 := by
  unfold tailWord_1431066
  simp only [CollatzResearch.WordTrace]
  refine ⟨13048816258374940864926263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34796843355666508973136701 13048816258374940864926263)
  ·
    refine ⟨19573224387562411297389395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13048816258374940864926263 19573224387562411297389395)
    ·
      refine ⟨29359836581343616946084093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19573224387562411297389395 29359836581343616946084093)
      ·
        refine ⟨11009938718003856354781535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29359836581343616946084093 11009938718003856354781535)
        ·
          refine ⟨16514908077005784532172303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11009938718003856354781535 16514908077005784532172303)
          ·
            refine ⟨24772362115508676798258455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16514908077005784532172303 24772362115508676798258455)
            ·
              refine ⟨37158543173263015197387683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24772362115508676798258455 37158543173263015197387683)
              ·
                refine ⟨55737814759894522796081525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37158543173263015197387683 55737814759894522796081525)
                ·
                  refine ⟨5225420133740111512132643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55737814759894522796081525 5225420133740111512132643)
                  ·
                    refine ⟨7838130200610167268198965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5225420133740111512132643 7838130200610167268198965)
                    ·
                      refine ⟨734824706307203181393653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7838130200610167268198965 734824706307203181393653)
                      ·
                        rfl

theorem cell23_1431066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1431066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431066 prefixEnd_1431066 := by exact prefixLift 1431066
  have htrace : WordTrace (prefixWord ++ tailWord_1431066) baseStart_1431066 baseEnd_1431066 := by
    simpa [prefixWord, tailWord_1431066, baseEnd_1431066] using wordTrace_append hprefix tailTrace_1431066
  have hstable : (prefixWord ++ tailWord_1431066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431066).length < 2 ^ (prefixWord ++ tailWord_1431066).sum := by decide
  have hdescent : baseEnd_1431066 < baseStart_1431066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431073 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 4, 4]
def baseStart_1431073 : Nat := 118140960795 + 1431073 * 2 ^ 59
def prefixEnd_1431073 : Nat := 4983230072969 + 3 ^ 40 * 1431073 * 2
def baseEnd_1431073 : Nat := 244942766890594884668707

theorem tailTrace_1431073 : CollatzResearch.WordTrace tailWord_1431073 prefixEnd_1431073 244942766890594884668707 := by
  unfold tailWord_1431073
  simp only [CollatzResearch.WordTrace]
  refine ⟨52195520344474403655209873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34797013562982935770139915 52195520344474403655209873)
  ·
    refine ⟨39146640258355802741407405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52195520344474403655209873 39146640258355802741407405)
    ·
      refine ⟨14679990096883426028027777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39146640258355802741407405 14679990096883426028027777)
      ·
        refine ⟨11009992572662569521020833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14679990096883426028027777 11009992572662569521020833)
        ·
          refine ⟨8257494429496927140765625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11009992572662569521020833 8257494429496927140765625)
          ·
            refine ⟨6193120822122695355574219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8257494429496927140765625 6193120822122695355574219)
            ·
              refine ⟨9289681233184043033361329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6193120822122695355574219 9289681233184043033361329)
              ·
                refine ⟨6967260924888032275020997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9289681233184043033361329 6967260924888032275020997)
                ·
                  refine ⟨1306361423416506051566437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6967260924888032275020997 1306361423416506051566437)
                  ·
                    refine ⟨244942766890594884668707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1306361423416506051566437 244942766890594884668707)
                    ·
                      rfl

theorem cell23_1431073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_1431073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431073 prefixEnd_1431073 := by exact prefixLift 1431073
  have htrace : WordTrace (prefixWord ++ tailWord_1431073) baseStart_1431073 baseEnd_1431073 := by
    simpa [prefixWord, tailWord_1431073, baseEnd_1431073] using wordTrace_append hprefix tailTrace_1431073
  have hstable : (prefixWord ++ tailWord_1431073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431073).length < 2 ^ (prefixWord ++ tailWord_1431073).sum := by decide
  have hdescent : baseEnd_1431073 < baseStart_1431073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431097 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 3, 2, 2]
def baseStart_1431097 : Nat := 118140960795 + 1431097 * 2 ^ 59
def prefixEnd_1431097 : Nat := 4983230072969 + 3 ^ 40 * 1431097 * 2
def baseEnd_1431097 : Nat := 734840624207492560106011

theorem tailTrace_1431097 : CollatzResearch.WordTrace tailWord_1431097 prefixEnd_1431097 734840624207492560106011 := by
  unfold tailWord_1431097
  simp only [CollatzResearch.WordTrace]
  refine ⟨52196395696387455754083545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34797597130924970502722363 52196395696387455754083545)
  ·
    refine ⟨39147296772290591815562659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52196395696387455754083545 39147296772290591815562659)
    ·
      refine ⟨58720945158435887723343989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39147296772290591815562659 58720945158435887723343989)
      ·
        refine ⟨5505088608603364474063499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58720945158435887723343989 5505088608603364474063499)
        ·
          refine ⟨8257632912905046711095249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5505088608603364474063499 8257632912905046711095249)
          ·
            refine ⟨6193224684678785033321437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8257632912905046711095249 6193224684678785033321437)
            ·
              refine ⟨2322459256754544387495539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6193224684678785033321437 2322459256754544387495539)
              ·
                refine ⟨3483688885131816581243309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322459256754544387495539 3483688885131816581243309)
                ·
                  refine ⟨1306383331924431217966241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3483688885131816581243309 1306383331924431217966241)
                  ·
                    refine ⟨979787498943323413474681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1306383331924431217966241 979787498943323413474681)
                    ·
                      refine ⟨734840624207492560106011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979787498943323413474681 734840624207492560106011)
                      ·
                        rfl

theorem cell23_1431097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_1431097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431097 prefixEnd_1431097 := by exact prefixLift 1431097
  have htrace : WordTrace (prefixWord ++ tailWord_1431097) baseStart_1431097 baseEnd_1431097 := by
    simpa [prefixWord, tailWord_1431097, baseEnd_1431097] using wordTrace_append hprefix tailTrace_1431097
  have hstable : (prefixWord ++ tailWord_1431097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431097).length < 2 ^ (prefixWord ++ tailWord_1431097).sum := by decide
  have hdescent : baseEnd_1431097 < baseStart_1431097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431117 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1431117 : Nat := 118140960795 + 1431117 * 2 ^ 59
def prefixEnd_1431117 : Nat := 4983230072969 + 3 ^ 40 * 1431117 * 2
def baseEnd_1431117 : Nat := 734850893820582481855919

theorem tailTrace_1431117 : CollatzResearch.WordTrace tailWord_1431117 prefixEnd_1431117 734850893820582481855919 := by
  unfold tailWord_1431117
  simp only [CollatzResearch.WordTrace]
  refine ⟨52197125156314999169811605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34798083437543332779874403 52197125156314999169811605)
  ·
    refine ⟨2446740241702265586084919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52197125156314999169811605 2446740241702265586084919)
    ·
      refine ⟨3670110362553398379127379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2446740241702265586084919 3670110362553398379127379)
      ·
        refine ⟨5505165543830097568691069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670110362553398379127379 5505165543830097568691069)
        ·
          refine ⟨2064437078936286588259151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5505165543830097568691069 2064437078936286588259151)
          ·
            refine ⟨3096655618404429882388727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064437078936286588259151 3096655618404429882388727)
            ·
              refine ⟨4644983427606644823583091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096655618404429882388727 4644983427606644823583091)
              ·
                refine ⟨6967475141409967235374637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4644983427606644823583091 6967475141409967235374637)
                ·
                  refine ⟨2612803178028737713265489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6967475141409967235374637 2612803178028737713265489)
                  ·
                    refine ⟨1959602383521553284949117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2612803178028737713265489 1959602383521553284949117)
                    ·
                      refine ⟨734850893820582481855919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1959602383521553284949117 734850893820582481855919)
                      ·
                        rfl

theorem cell23_1431117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1431117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431117 prefixEnd_1431117 := by exact prefixLift 1431117
  have htrace : WordTrace (prefixWord ++ tailWord_1431117) baseStart_1431117 baseEnd_1431117 := by
    simpa [prefixWord, tailWord_1431117, baseEnd_1431117] using wordTrace_append hprefix tailTrace_1431117
  have hstable : (prefixWord ++ tailWord_1431117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431117).length < 2 ^ (prefixWord ++ tailWord_1431117).sum := by decide
  have hdescent : baseEnd_1431117 < baseStart_1431117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431157 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1431157 : Nat := 118140960795 + 1431157 * 2 ^ 59
def prefixEnd_1431157 : Nat := 4983230072969 + 3 ^ 40 * 1431157 * 2
def baseEnd_1431157 : Nat := 734871433046762325355735

theorem tailTrace_1431157 : CollatzResearch.WordTrace tailWord_1431157 prefixEnd_1431157 734871433046762325355735 := by
  unfold tailWord_1431157
  simp only [CollatzResearch.WordTrace]
  refine ⟨52198584076170086001267725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34799056050780057334178483 52198584076170086001267725)
  ·
    refine ⟨19574469028563782250475397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52198584076170086001267725 19574469028563782250475397)
    ·
      refine ⟨3670212942855709171964137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19574469028563782250475397 3670212942855709171964137)
      ·
        refine ⟨2752659707141781878973103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3670212942855709171964137 2752659707141781878973103)
        ·
          refine ⟨4128989560712672818459655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752659707141781878973103 4128989560712672818459655)
          ·
            refine ⟨6193484341069009227689483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4128989560712672818459655 6193484341069009227689483)
            ·
              refine ⟨9290226511603513841534225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6193484341069009227689483 9290226511603513841534225)
              ·
                refine ⟨6967669883702635381150669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9290226511603513841534225 6967669883702635381150669)
                ·
                  refine ⟨2612876206388488267931501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6967669883702635381150669 2612876206388488267931501)
                  ·
                    refine ⟨979828577395683100474313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612876206388488267931501 979828577395683100474313)
                    ·
                      refine ⟨734871433046762325355735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979828577395683100474313 734871433046762325355735)
                      ·
                        rfl

theorem cell23_1431157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1431157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431157 prefixEnd_1431157 := by exact prefixLift 1431157
  have htrace : WordTrace (prefixWord ++ tailWord_1431157) baseStart_1431157 baseEnd_1431157 := by
    simpa [prefixWord, tailWord_1431157, baseEnd_1431157] using wordTrace_append hprefix tailTrace_1431157
  have hstable : (prefixWord ++ tailWord_1431157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431157).length < 2 ^ (prefixWord ++ tailWord_1431157).sum := by decide
  have hdescent : baseEnd_1431157 < baseStart_1431157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431173 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 2, 4, 3]
def baseStart_1431173 : Nat := 118140960795 + 1431173 * 2 ^ 59
def prefixEnd_1431173 : Nat := 4983230072969 + 3 ^ 40 * 1431173 * 2
def baseEnd_1431173 : Nat := 734879648737234262755661

theorem tailTrace_1431173 : CollatzResearch.WordTrace tailWord_1431173 prefixEnd_1431173 734879648737234262755661 := by
  unfold tailWord_1431173
  simp only [CollatzResearch.WordTrace]
  refine ⟨52199167644112120733850173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34799445096074747155900115 52199167644112120733850173)
  ·
    refine ⟨19574687866542045275193815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52199167644112120733850173 19574687866542045275193815)
    ·
      refine ⟨29362031799813067912790723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19574687866542045275193815 29362031799813067912790723)
      ·
        refine ⟨44043047699719601869186085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29362031799813067912790723 44043047699719601869186085)
        ·
          refine ⟨8258071443697425350472391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44043047699719601869186085 8258071443697425350472391)
          ·
            refine ⟨12387107165546138025708587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8258071443697425350472391 12387107165546138025708587)
            ·
              refine ⟨18580660748319207038562881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12387107165546138025708587 18580660748319207038562881)
              ·
                refine ⟨13935495561239405278922161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18580660748319207038562881 13935495561239405278922161)
                ·
                  refine ⟨10451621670929553959191621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13935495561239405278922161 10451621670929553959191621)
                  ·
                    refine ⟨1959679063299291367348429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10451621670929553959191621 1959679063299291367348429)
                    ·
                      refine ⟨734879648737234262755661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1959679063299291367348429 734879648737234262755661)
                      ·
                        rfl

theorem cell23_1431173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_1431173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431173 prefixEnd_1431173 := by exact prefixLift 1431173
  have htrace : WordTrace (prefixWord ++ tailWord_1431173) baseStart_1431173 baseEnd_1431173 := by
    simpa [prefixWord, tailWord_1431173, baseEnd_1431173] using wordTrace_append hprefix tailTrace_1431173
  have hstable : (prefixWord ++ tailWord_1431173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431173).length < 2 ^ (prefixWord ++ tailWord_1431173).sum := by decide
  have hdescent : baseEnd_1431173 < baseStart_1431173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431203 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 3]
def baseStart_1431203 : Nat := 118140960795 + 1431203 * 2 ^ 59
def prefixEnd_1431203 : Nat := 4983230072969 + 3 ^ 40 * 1431203 * 2
def baseEnd_1431203 : Nat := 734895053156869145380523

theorem tailTrace_1431203 : CollatzResearch.WordTrace tailWord_1431203 prefixEnd_1431203 734895053156869145380523 := by
  unfold tailWord_1431203
  simp only [CollatzResearch.WordTrace]
  refine ⟨52200261834003435857442263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34800174556002290571628175 52200261834003435857442263)
  ·
    refine ⟨78300392751005153786163395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52200261834003435857442263 78300392751005153786163395)
    ·
      refine ⟨117450589126507730679245093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78300392751005153786163395 117450589126507730679245093)
      ·
        refine ⟨22021985461220199502358455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117450589126507730679245093 22021985461220199502358455)
        ·
          refine ⟨33032978191830299253537683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22021985461220199502358455 33032978191830299253537683)
          ·
            refine ⟨49549467287745448880306525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33032978191830299253537683 49549467287745448880306525)
            ·
              refine ⟨18581050232904543330114947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49549467287745448880306525 18581050232904543330114947)
              ·
                refine ⟨27871575349356814995172421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18581050232904543330114947 27871575349356814995172421)
                ·
                  refine ⟨5225920378004402811594829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27871575349356814995172421 5225920378004402811594829)
                  ·
                    refine ⟨1959720141751651054348061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5225920378004402811594829 1959720141751651054348061)
                    ·
                      refine ⟨734895053156869145380523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1959720141751651054348061 734895053156869145380523)
                      ·
                        rfl

theorem cell23_1431203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_1431203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431203 prefixEnd_1431203 := by exact prefixLift 1431203
  have htrace : WordTrace (prefixWord ++ tailWord_1431203) baseStart_1431203 baseEnd_1431203 := by
    simpa [prefixWord, tailWord_1431203, baseEnd_1431203] using wordTrace_append hprefix tailTrace_1431203
  have hstable : (prefixWord ++ tailWord_1431203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431203).length < 2 ^ (prefixWord ++ tailWord_1431203).sum := by decide
  have hdescent : baseEnd_1431203 < baseStart_1431203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431204 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 2, 2, 2]
def baseStart_1431204 : Nat := 118140960795 + 1431204 * 2 ^ 59
def prefixEnd_1431204 : Nat := 4983230072969 + 3 ^ 40 * 1431204 * 2
def baseEnd_1431204 : Nat := 734895566637523641468019

theorem tailTrace_1431204 : CollatzResearch.WordTrace tailWord_1431204 prefixEnd_1431204 734895566637523641468019 := by
  unfold tailWord_1431204
  simp only [CollatzResearch.WordTrace]
  refine ⟨26100149153499906514114333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34800198871333208685485777 26100149153499906514114333)
  ·
    refine ⟨9787555932562464942792875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26100149153499906514114333 9787555932562464942792875)
    ·
      refine ⟨14681333898843697414189313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9787555932562464942792875 14681333898843697414189313)
      ·
        refine ⟨11011000424132773060641985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14681333898843697414189313 11011000424132773060641985)
        ·
          refine ⟨8258250318099579795481489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11011000424132773060641985 8258250318099579795481489)
          ·
            refine ⟨6193687738574684846611117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8258250318099579795481489 6193687738574684846611117)
            ·
              refine ⟨2322632901965506817479169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6193687738574684846611117 2322632901965506817479169)
              ·
                refine ⟨1741974676474130113109377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322632901965506817479169 1741974676474130113109377)
                ·
                  refine ⟨1306481007355597584832033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1741974676474130113109377 1306481007355597584832033)
                  ·
                    refine ⟨979860755516698188624025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1306481007355597584832033 979860755516698188624025)
                    ·
                      refine ⟨734895566637523641468019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979860755516698188624025 734895566637523641468019)
                      ·
                        rfl

theorem cell23_1431204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_1431204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431204 prefixEnd_1431204 := by exact prefixLift 1431204
  have htrace : WordTrace (prefixWord ++ tailWord_1431204) baseStart_1431204 baseEnd_1431204 := by
    simpa [prefixWord, tailWord_1431204, baseEnd_1431204] using wordTrace_append hprefix tailTrace_1431204
  have hstable : (prefixWord ++ tailWord_1431204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431204).length < 2 ^ (prefixWord ++ tailWord_1431204).sum := by decide
  have hdescent : baseEnd_1431204 < baseStart_1431204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431221 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_1431221 : Nat := 118140960795 + 1431221 * 2 ^ 59
def prefixEnd_1431221 : Nat := 4983230072969 + 3 ^ 40 * 1431221 * 2
def baseEnd_1431221 : Nat := 734904295808650074955441

theorem tailTrace_1431221 : CollatzResearch.WordTrace tailWord_1431221 prefixEnd_1431221 734904295808650074955441 := by
  unfold tailWord_1431221
  simp only [CollatzResearch.WordTrace]
  refine ⟨52200918347938224931597517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34800612231958816621065011 52200918347938224931597517)
  ·
    refine ⟨19575344380476834349349069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52200918347938224931597517 19575344380476834349349069)
    ·
      refine ⟨7340754142678812881005901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19575344380476834349349069 7340754142678812881005901)
      ·
        refine ⟨2752782803504554830377213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7340754142678812881005901 2752782803504554830377213)
        ·
          refine ⟨1032293551314208061391455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2752782803504554830377213 1032293551314208061391455)
          ·
            refine ⟨1548440326971312092087183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032293551314208061391455 1548440326971312092087183)
            ·
              refine ⟨2322660490456968138130775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548440326971312092087183 2322660490456968138130775)
              ·
                refine ⟨3483990735685452207196163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322660490456968138130775 3483990735685452207196163)
                ·
                  refine ⟨5225986103528178310794245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483990735685452207196163 5225986103528178310794245)
                  ·
                    refine ⟨979872394411533433273921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5225986103528178310794245 979872394411533433273921)
                    ·
                      refine ⟨734904295808650074955441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979872394411533433273921 734904295808650074955441)
                      ·
                        rfl

theorem cell23_1431221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_1431221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431221 prefixEnd_1431221 := by exact prefixLift 1431221
  have htrace : WordTrace (prefixWord ++ tailWord_1431221) baseStart_1431221 baseEnd_1431221 := by
    simpa [prefixWord, tailWord_1431221, baseEnd_1431221] using wordTrace_append hprefix tailTrace_1431221
  have hstable : (prefixWord ++ tailWord_1431221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431221).length < 2 ^ (prefixWord ++ tailWord_1431221).sum := by decide
  have hdescent : baseEnd_1431221 < baseStart_1431221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431223 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 1, 7]
def baseStart_1431223 : Nat := 118140960795 + 1431223 * 2 ^ 59
def prefixEnd_1431223 : Nat := 4983230072969 + 3 ^ 40 * 1431223 * 2
def baseEnd_1431223 : Nat := 244968440923319689043477

theorem tailTrace_1431223 : CollatzResearch.WordTrace tailWord_1431223 prefixEnd_1431223 244968440923319689043477 := by
  unfold tailWord_1431223
  simp only [CollatzResearch.WordTrace]
  refine ⟨52200991293930979273170323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34800660862620652848780215 52200991293930979273170323)
  ·
    refine ⟨78301486940896468909755485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52200991293930979273170323 78301486940896468909755485)
    ·
      refine ⟨29363057602836175841158307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78301486940896468909755485 29363057602836175841158307)
      ·
        refine ⟨44044586404254263761737461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29363057602836175841158307 44044586404254263761737461)
        ·
          refine ⟨4129179975398837227662887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44044586404254263761737461 4129179975398837227662887)
          ·
            refine ⟨6193769963098255841494331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129179975398837227662887 6193769963098255841494331)
            ·
              refine ⟨9290654944647383762241497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6193769963098255841494331 9290654944647383762241497)
              ·
                refine ⟨6967991208485537821681123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9290654944647383762241497 6967991208485537821681123)
                ·
                  refine ⟨10451986812728306732521685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6967991208485537821681123 10451986812728306732521685)
                  ·
                    refine ⟨244968440923319689043477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10451986812728306732521685 244968440923319689043477)
                    ·
                      rfl

theorem cell23_1431223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_1431223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431223 prefixEnd_1431223 := by exact prefixLift 1431223
  have htrace : WordTrace (prefixWord ++ tailWord_1431223) baseStart_1431223 baseEnd_1431223 := by
    simpa [prefixWord, tailWord_1431223, baseEnd_1431223] using wordTrace_append hprefix tailTrace_1431223
  have hstable : (prefixWord ++ tailWord_1431223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431223).length < 2 ^ (prefixWord ++ tailWord_1431223).sum := by decide
  have hdescent : baseEnd_1431223 < baseStart_1431223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
