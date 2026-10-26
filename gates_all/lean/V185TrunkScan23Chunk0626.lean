import V185TrunkScan23Chunk0625

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3702323 : List Nat := [1, 1, 1, 2, 4, 3, 4, 2, 1, 2, 2]
def baseStart_3702323 : Nat := 118140960795 + 3702323 * 2 ^ 59
def prefixEnd_3702323 : Nat := 4983230072969 + 3 ^ 40 * 3702323 * 2
def baseEnd_3702323 : Nat := 1901071237196023377935833

theorem tailTrace_3702323 : CollatzResearch.WordTrace tailWord_3702323 prefixEnd_3702323 1901071237196023377935833 := by
  unfold tailWord_3702323
  simp only [CollatzResearch.WordTrace]
  refine ⟨135034813366123552273023623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90023208910749034848682415 135034813366123552273023623)
  ·
    refine ⟨202552220049185328409535435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135034813366123552273023623 202552220049185328409535435)
    ·
      refine ⟨303828330073777992614303153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202552220049185328409535435 303828330073777992614303153)
      ·
        refine ⟨227871247555333494460727365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303828330073777992614303153 227871247555333494460727365)
        ·
          refine ⟨42725858916625030211386381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227871247555333494460727365 42725858916625030211386381)
          ·
            refine ⟨16022197093734386329269893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42725858916625030211386381 16022197093734386329269893)
            ·
              refine ⟨3004161955075197436738105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16022197093734386329269893 3004161955075197436738105)
              ·
                refine ⟨2253121466306398077553579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3004161955075197436738105 2253121466306398077553579)
                ·
                  refine ⟨3379682199459597116330369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253121466306398077553579 3379682199459597116330369)
                  ·
                    refine ⟨2534761649594697837247777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3379682199459597116330369 2534761649594697837247777)
                    ·
                      refine ⟨1901071237196023377935833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534761649594697837247777 1901071237196023377935833)
                      ·
                        rfl

theorem cell23_3702323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 1, 2, 2].length) (baseStart_3702323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702323 prefixEnd_3702323 := by exact prefixLift 3702323
  have htrace : WordTrace (prefixWord ++ tailWord_3702323) baseStart_3702323 baseEnd_3702323 := by
    simpa [prefixWord, tailWord_3702323, baseEnd_3702323] using wordTrace_append hprefix tailTrace_3702323
  have hstable : (prefixWord ++ tailWord_3702323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702323).length < 2 ^ (prefixWord ++ tailWord_3702323).sum := by decide
  have hdescent : baseEnd_3702323 < baseStart_3702323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702325 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3702325 : Nat := 118140960795 + 3702325 * 2 ^ 59
def prefixEnd_3702325 : Nat := 4983230072969 + 3 ^ 40 * 3702325 * 2
def baseEnd_3702325 : Nat := 633690754719110790036941

theorem tailTrace_3702325 : CollatzResearch.WordTrace tailWord_3702325 prefixEnd_3702325 633690754719110790036941 := by
  unfold tailWord_3702325
  simp only [CollatzResearch.WordTrace]
  refine ⟨135034886312116306614596429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90023257541410871076397619 135034886312116306614596429)
  ·
    refine ⟨50638082367043614980473661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135034886312116306614596429 50638082367043614980473661)
    ·
      refine ⟨18989280887641355617677623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50638082367043614980473661 18989280887641355617677623)
      ·
        refine ⟨28483921331462033426516435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18989280887641355617677623 28483921331462033426516435)
        ·
          refine ⟨42725881997193050139774653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28483921331462033426516435 42725881997193050139774653)
          ·
            refine ⟨16022205748947393802415495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42725881997193050139774653 16022205748947393802415495)
            ·
              refine ⟨24033308623421090703623243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16022205748947393802415495 24033308623421090703623243)
              ·
                refine ⟨36049962935131636055434865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24033308623421090703623243 36049962935131636055434865)
                ·
                  refine ⟨27037472201348727041576149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36049962935131636055434865 27037472201348727041576149)
                  ·
                    refine ⟨633690754719110790036941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27037472201348727041576149 633690754719110790036941)
                    ·
                      rfl

theorem cell23_3702325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3702325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702325 prefixEnd_3702325 := by exact prefixLift 3702325
  have htrace : WordTrace (prefixWord ++ tailWord_3702325) baseStart_3702325 baseEnd_3702325 := by
    simpa [prefixWord, tailWord_3702325, baseEnd_3702325] using wordTrace_append hprefix tailTrace_3702325
  have hstable : (prefixWord ++ tailWord_3702325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702325).length < 2 ^ (prefixWord ++ tailWord_3702325).sum := by decide
  have hdescent : baseEnd_3702325 < baseStart_3702325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702432 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 4, 5]
def baseStart_3702432 : Nat := 118140960795 + 3702432 * 2 ^ 59
def prefixEnd_3702432 : Nat := 4983230072969 + 3 ^ 40 * 3702432 * 2
def baseEnd_3702432 : Nat := 633709068862454483824277

theorem tailTrace_3702432 : CollatzResearch.WordTrace tailWord_3702432 prefixEnd_3702432 633709068862454483824277 := by
  unfold tailWord_3702432
  simp only [CollatzResearch.WordTrace]
  refine ⟨67519394461364331944370775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90025859281819109259161033 67519394461364331944370775)
  ·
    refine ⟨101279091692046497916556163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67519394461364331944370775 101279091692046497916556163)
    ·
      refine ⟨151918637538069746874834245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101279091692046497916556163 151918637538069746874834245)
      ·
        refine ⟨28484744538388077539031421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151918637538069746874834245 28484744538388077539031421)
        ·
          refine ⟨10681779201895529077136783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28484744538388077539031421 10681779201895529077136783)
          ·
            refine ⟨16022668802843293615705175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10681779201895529077136783 16022668802843293615705175)
            ·
              refine ⟨24034003204264940423557763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16022668802843293615705175 24034003204264940423557763)
              ·
                refine ⟨36051004806397410635336645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24034003204264940423557763 36051004806397410635336645)
                ·
                  refine ⟨6759563401199514494125621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36051004806397410635336645 6759563401199514494125621)
                  ·
                    refine ⟨633709068862454483824277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6759563401199514494125621 633709068862454483824277)
                    ·
                      rfl

theorem cell23_3702432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_3702432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702432 prefixEnd_3702432 := by exact prefixLift 3702432
  have htrace : WordTrace (prefixWord ++ tailWord_3702432) baseStart_3702432 baseEnd_3702432 := by
    simpa [prefixWord, tailWord_3702432, baseEnd_3702432] using wordTrace_append hprefix tailTrace_3702432
  have hstable : (prefixWord ++ tailWord_3702432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702432).length < 2 ^ (prefixWord ++ tailWord_3702432).sum := by decide
  have hdescent : baseEnd_3702432 < baseStart_3702432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702436 : List Nat := [2, 3, 1, 2, 2, 3, 3, 2, 5]
def baseStart_3702436 : Nat := 118140960795 + 3702436 * 2 ^ 59
def prefixEnd_3702436 : Nat := 4983230072969 + 3 ^ 40 * 3702436 * 2
def baseEnd_3702436 : Nat := 211236584501109048424757

theorem tailTrace_3702436 : CollatzResearch.WordTrace tailWord_3702436 prefixEnd_3702436 211236584501109048424757 := by
  unfold tailWord_3702436
  simp only [CollatzResearch.WordTrace]
  refine ⟨67519467407357086285943581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90025956543142781714591441 67519467407357086285943581)
  ·
    refine ⟨25319800277758907357228843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67519467407357086285943581 25319800277758907357228843)
    ·
      refine ⟨37979700416638361035843265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25319800277758907357228843 37979700416638361035843265)
      ·
        refine ⟨28484775312478770776882449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37979700416638361035843265 28484775312478770776882449)
        ·
          refine ⟨21363581484359078082661837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28484775312478770776882449 21363581484359078082661837)
          ·
            refine ⟨8011343056634654280998189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21363581484359078082661837 8011343056634654280998189)
            ·
              refine ⟨3004253646237995355374321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8011343056634654280998189 3004253646237995355374321)
              ·
                refine ⟨2253190234678496516530741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3004253646237995355374321 2253190234678496516530741)
                ·
                  refine ⟨211236584501109048424757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2253190234678496516530741 211236584501109048424757)
                  ·
                    rfl

theorem cell23_3702436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_3702436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702436 prefixEnd_3702436 := by exact prefixLift 3702436
  have htrace : WordTrace (prefixWord ++ tailWord_3702436) baseStart_3702436 baseEnd_3702436 := by
    simpa [prefixWord, tailWord_3702436, baseEnd_3702436] using wordTrace_append hprefix tailTrace_3702436
  have hstable : (prefixWord ++ tailWord_3702436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702436).length < 2 ^ (prefixWord ++ tailWord_3702436).sum := by decide
  have hdescent : baseEnd_3702436 < baseStart_3702436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702475 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 10]
def baseStart_3702475 : Nat := 118140960795 + 3702475 * 2 ^ 59
def prefixEnd_3702475 : Nat := 4983230072969 + 3 ^ 40 * 3702475 * 2
def baseEnd_3702475 : Nat := 211238809583945198137237

theorem tailTrace_3702475 : CollatzResearch.WordTrace tailWord_3702475 prefixEnd_3702475 211238809583945198137237 := by
  unfold tailWord_3702475
  simp only [CollatzResearch.WordTrace]
  refine ⟨135040357261572882232556879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90026904841048588155037919 135040357261572882232556879)
  ·
    refine ⟨202560535892359323348835319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135040357261572882232556879 202560535892359323348835319)
    ·
      refine ⟨303840803838538985023252979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202560535892359323348835319 303840803838538985023252979)
      ·
        refine ⟨455761205757808477534879469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303840803838538985023252979 455761205757808477534879469)
        ·
          refine ⟨170910452159178179075579801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455761205757808477534879469 170910452159178179075579801)
          ·
            refine ⟨128182839119383634306684851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170910452159178179075579801 128182839119383634306684851)
            ·
              refine ⟨192274258679075451460027277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128182839119383634306684851 192274258679075451460027277)
              ·
                refine ⟨72102847004653294297510229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192274258679075451460027277 72102847004653294297510229)
                ·
                  refine ⟨211238809583945198137237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 72102847004653294297510229 211238809583945198137237)
                  ·
                    rfl

theorem cell23_3702475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 10].length) (baseStart_3702475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702475 prefixEnd_3702475 := by exact prefixLift 3702475
  have htrace : WordTrace (prefixWord ++ tailWord_3702475) baseStart_3702475 baseEnd_3702475 := by
    simpa [prefixWord, tailWord_3702475, baseEnd_3702475] using wordTrace_append hprefix tailTrace_3702475
  have hstable : (prefixWord ++ tailWord_3702475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702475).length < 2 ^ (prefixWord ++ tailWord_3702475).sum := by decide
  have hdescent : baseEnd_3702475 < baseStart_3702475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702489 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 2, 2, 3]
def baseStart_3702489 : Nat := 118140960795 + 3702489 * 2 ^ 59
def prefixEnd_3702489 : Nat := 4983230072969 + 3 ^ 40 * 3702489 * 2
def baseEnd_3702489 : Nat := 1901156474984669728460069

theorem tailTrace_3702489 : CollatzResearch.WordTrace tailWord_3702489 prefixEnd_3702489 1901156474984669728460069 := by
  unfold tailWord_3702489
  simp only [CollatzResearch.WordTrace]
  refine ⟨135040867883522162623566521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90027245255681441749044347 135040867883522162623566521)
  ·
    refine ⟨101280650912641621967674891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135040867883522162623566521 101280650912641621967674891)
    ·
      refine ⟨151920976368962432951512337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101280650912641621967674891 151920976368962432951512337)
      ·
        refine ⟨113940732276721824713634253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151920976368962432951512337 113940732276721824713634253)
        ·
          refine ⟨42727774603770684267612845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113940732276721824713634253 42727774603770684267612845)
          ·
            refine ⟨16022915476414006600354817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42727774603770684267612845 16022915476414006600354817)
            ·
              refine ⟨12017186607310504950266113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16022915476414006600354817 12017186607310504950266113)
              ·
                refine ⟨9012889955482878712699585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12017186607310504950266113 9012889955482878712699585)
                ·
                  refine ⟨6759667466612159034524689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9012889955482878712699585 6759667466612159034524689)
                  ·
                    refine ⟨5069750599959119275893517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6759667466612159034524689 5069750599959119275893517)
                    ·
                      refine ⟨1901156474984669728460069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5069750599959119275893517 1901156474984669728460069)
                      ·
                        rfl

theorem cell23_3702489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_3702489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702489 prefixEnd_3702489 := by exact prefixLift 3702489
  have htrace : WordTrace (prefixWord ++ tailWord_3702489) baseStart_3702489 baseEnd_3702489 := by
    simpa [prefixWord, tailWord_3702489, baseEnd_3702489] using wordTrace_append hprefix tailTrace_3702489
  have hstable : (prefixWord ++ tailWord_3702489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702489).length < 2 ^ (prefixWord ++ tailWord_3702489).sum := by decide
  have hdescent : baseEnd_3702489 < baseStart_3702489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702503 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3702503 : Nat := 118140960795 + 3702503 * 2 ^ 59
def prefixEnd_3702503 : Nat := 4983230072969 + 3 ^ 40 * 3702503 * 2
def baseEnd_3702503 : Nat := 1901163663713832673685005

theorem tailTrace_3702503 : CollatzResearch.WordTrace tailWord_3702503 prefixEnd_3702503 1901163663713832673685005 := by
  unfold tailWord_3702503
  simp only [CollatzResearch.WordTrace]
  refine ⟨135041378505471443014576163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90027585670314295343050775 135041378505471443014576163)
  ·
    refine ⟨202562067758207164521864245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135041378505471443014576163 202562067758207164521864245)
    ·
      refine ⟨18990193852331921673924773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202562067758207164521864245 18990193852331921673924773)
      ·
        refine ⟨3560661347312235313860895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18990193852331921673924773 3560661347312235313860895)
        ·
          refine ⟨5340992020968352970791343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3560661347312235313860895 5340992020968352970791343)
          ·
            refine ⟨8011488031452529456187015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5340992020968352970791343 8011488031452529456187015)
            ·
              refine ⟨12017232047178794184280523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8011488031452529456187015 12017232047178794184280523)
              ·
                refine ⟨18025848070768191276420785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12017232047178794184280523 18025848070768191276420785)
                ·
                  refine ⟨13519386053076143457315589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18025848070768191276420785 13519386053076143457315589)
                  ·
                    refine ⟨2534884884951776898246673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13519386053076143457315589 2534884884951776898246673)
                    ·
                      refine ⟨1901163663713832673685005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534884884951776898246673 1901163663713832673685005)
                      ·
                        rfl

theorem cell23_3702503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3702503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702503 prefixEnd_3702503 := by exact prefixLift 3702503
  have htrace : WordTrace (prefixWord ++ tailWord_3702503) baseStart_3702503 baseEnd_3702503 := by
    simpa [prefixWord, tailWord_3702503, baseEnd_3702503] using wordTrace_append hprefix tailTrace_3702503
  have hstable : (prefixWord ++ tailWord_3702503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702503).length < 2 ^ (prefixWord ++ tailWord_3702503).sum := by decide
  have hdescent : baseEnd_3702503 < baseStart_3702503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702509 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 6]
def baseStart_3702509 : Nat := 118140960795 + 3702509 * 2 ^ 59
def prefixEnd_3702509 : Nat := 4983230072969 + 3 ^ 40 * 3702509 * 2
def baseEnd_3702509 : Nat := 211240749399751072245553

theorem tailTrace_3702509 : CollatzResearch.WordTrace tailWord_3702509 prefixEnd_3702509 211240749399751072245553 := by
  unfold tailWord_3702509
  simp only [CollatzResearch.WordTrace]
  refine ⟨135041597343449706039294581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90027731562299804026196387 135041597343449706039294581)
  ·
    refine ⟨12660149750948409941183867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135041597343449706039294581 12660149750948409941183867)
    ·
      refine ⟨18990224626422614911775801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12660149750948409941183867 18990224626422614911775801)
      ·
        refine ⟨14242668469816961183831851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18990224626422614911775801 14242668469816961183831851)
        ·
          refine ⟨21364002704725441775747777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14242668469816961183831851 21364002704725441775747777)
          ·
            refine ⟨16023002028544081331810833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21364002704725441775747777 16023002028544081331810833)
            ·
              refine ⟨12017251521408060998858125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16023002028544081331810833 12017251521408060998858125)
              ·
                refine ⟨4506469320528022874571797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12017251521408060998858125 4506469320528022874571797)
                ·
                  refine ⟨211240749399751072245553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4506469320528022874571797 211240749399751072245553)
                  ·
                    rfl

theorem cell23_3702509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_3702509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702509 prefixEnd_3702509 := by exact prefixLift 3702509
  have htrace : WordTrace (prefixWord ++ tailWord_3702509) baseStart_3702509 baseEnd_3702509 := by
    simpa [prefixWord, tailWord_3702509, baseEnd_3702509] using wordTrace_append hprefix tailTrace_3702509
  have hstable : (prefixWord ++ tailWord_3702509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702509).length < 2 ^ (prefixWord ++ tailWord_3702509).sum := by decide
  have hdescent : baseEnd_3702509 < baseStart_3702509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702519 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 5, 1, 3]
def baseStart_3702519 : Nat := 118140960795 + 3702519 * 2 ^ 59
def prefixEnd_3702519 : Nat := 4983230072969 + 3 ^ 40 * 3702519 * 2
def baseEnd_3702519 : Nat := 1901171879404304611084931

theorem tailTrace_3702519 : CollatzResearch.WordTrace tailWord_3702519 prefixEnd_3702519 1901171879404304611084931 := by
  unfold tailWord_3702519
  simp only [CollatzResearch.WordTrace]
  refine ⟨135041962073413477747158611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90027974715608985164772407 135041962073413477747158611)
  ·
    refine ⟨202562943110120216620737917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135041962073413477747158611 202562943110120216620737917)
    ·
      refine ⟨75961103666295081232776719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202562943110120216620737917 75961103666295081232776719)
      ·
        refine ⟨113941655499442621849165079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75961103666295081232776719 113941655499442621849165079)
        ·
          refine ⟨170912483249163932773747619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113941655499442621849165079 170912483249163932773747619)
          ·
            refine ⟨256368724873745899160621429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170912483249163932773747619 256368724873745899160621429)
            ·
              refine ⟨24034567956913678046308259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256368724873745899160621429 24034567956913678046308259)
              ·
                refine ⟨36051851935370517069462389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24034567956913678046308259 36051851935370517069462389)
                ·
                  refine ⟨3379861118940985975262099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36051851935370517069462389 3379861118940985975262099)
                  ·
                    refine ⟨5069791678411478962893149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3379861118940985975262099 5069791678411478962893149)
                    ·
                      refine ⟨1901171879404304611084931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5069791678411478962893149 1901171879404304611084931)
                      ·
                        rfl

theorem cell23_3702519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_3702519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702519 prefixEnd_3702519 := by exact prefixLift 3702519
  have htrace : WordTrace (prefixWord ++ tailWord_3702519) baseStart_3702519 baseEnd_3702519 := by
    simpa [prefixWord, tailWord_3702519, baseEnd_3702519] using wordTrace_append hprefix tailTrace_3702519
  have hstable : (prefixWord ++ tailWord_3702519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702519).length < 2 ^ (prefixWord ++ tailWord_3702519).sum := by decide
  have hdescent : baseEnd_3702519 < baseStart_3702519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702552 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 3, 6]
def baseStart_3702552 : Nat := 118140960795 + 3702552 * 2 ^ 59
def prefixEnd_3702552 : Nat := 4983230072969 + 3 ^ 40 * 3702552 * 2
def baseEnd_3702552 : Nat := 633729608088634327324093

theorem tailTrace_3702552 : CollatzResearch.WordTrace tailWord_3702552 prefixEnd_3702552 633729608088634327324093 := by
  unfold tailWord_3702552
  simp only [CollatzResearch.WordTrace]
  refine ⟨67521582841146962191554955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90028777121529282922073273 67521582841146962191554955)
  ·
    refine ⟨101282374261720443287332433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67521582841146962191554955 101282374261720443287332433)
    ·
      refine ⟨75961780696290332465499325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101282374261720443287332433 75961780696290332465499325)
      ·
        refine ⟨28485667761108874674562247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75961780696290332465499325 28485667761108874674562247)
        ·
          refine ⟨42728501641663312011843371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28485667761108874674562247 42728501641663312011843371)
          ·
            refine ⟨64092752462494968017765057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42728501641663312011843371 64092752462494968017765057)
            ·
              refine ⟨48069564346871226013323793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64092752462494968017765057 48069564346871226013323793)
              ·
                refine ⟨36052173260153419509992845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48069564346871226013323793 36052173260153419509992845)
                ·
                  refine ⟨13519564972557532316247317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36052173260153419509992845 13519564972557532316247317)
                  ·
                    refine ⟨633729608088634327324093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13519564972557532316247317 633729608088634327324093)
                    ·
                      rfl

theorem cell23_3702552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_3702552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702552 prefixEnd_3702552 := by exact prefixLift 3702552
  have htrace : WordTrace (prefixWord ++ tailWord_3702552) baseStart_3702552 baseEnd_3702552 := by
    simpa [prefixWord, tailWord_3702552, baseEnd_3702552] using wordTrace_append hprefix tailTrace_3702552
  have hstable : (prefixWord ++ tailWord_3702552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702552).length < 2 ^ (prefixWord ++ tailWord_3702552).sum := by decide
  have hdescent : baseEnd_3702552 < baseStart_3702552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702610 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_3702610 : Nat := 118140960795 + 3702610 * 2 ^ 59
def prefixEnd_3702610 : Nat := 4983230072969 + 3 ^ 40 * 3702610 * 2
def baseEnd_3702610 : Nat := 1901218606143863755047013

theorem tailTrace_3702610 : CollatzResearch.WordTrace tailWord_3702610 prefixEnd_3702610 1901218606143863755047013 := by
  unfold tailWord_3702610
  simp only [CollatzResearch.WordTrace]
  refine ⟨33761320279020950072180321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90030187410722533525814189 33761320279020950072180321)
  ·
    refine ⟨25320990209265712554135241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33761320279020950072180321 25320990209265712554135241)
    ·
      refine ⟨18990742656949284415601431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25320990209265712554135241 18990742656949284415601431)
      ·
        refine ⟨28486113985423926623402147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18990742656949284415601431 28486113985423926623402147)
        ·
          refine ⟨42729170978135889935103221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28486113985423926623402147 42729170978135889935103221)
          ·
            refine ⟨4005859779200239681415927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42729170978135889935103221 4005859779200239681415927)
            ·
              refine ⟨6008789668800359522123891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005859779200239681415927 6008789668800359522123891)
              ·
                refine ⟨9013184503200539283185837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6008789668800359522123891 9013184503200539283185837)
                ·
                  refine ⟨3379944188700202231194689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9013184503200539283185837 3379944188700202231194689)
                  ·
                    refine ⟨2534958141525151673396017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3379944188700202231194689 2534958141525151673396017)
                    ·
                      refine ⟨1901218606143863755047013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534958141525151673396017 1901218606143863755047013)
                      ·
                        rfl

theorem cell23_3702610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_3702610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702610 prefixEnd_3702610 := by exact prefixLift 3702610
  have htrace : WordTrace (prefixWord ++ tailWord_3702610) baseStart_3702610 baseEnd_3702610 := by
    simpa [prefixWord, tailWord_3702610, baseEnd_3702610] using wordTrace_append hprefix tailTrace_3702610
  have hstable : (prefixWord ++ tailWord_3702610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702610).length < 2 ^ (prefixWord ++ tailWord_3702610).sum := by decide
  have hdescent : baseEnd_3702610 < baseStart_3702610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702676 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_3702676 : Nat := 118140960795 + 3702676 * 2 ^ 59
def prefixEnd_3702676 : Nat := 4983230072969 + 3 ^ 40 * 3702676 * 2
def baseEnd_3702676 : Nat := 633750831955686832273903

theorem tailTrace_3702676 : CollatzResearch.WordTrace tailWord_3702676 prefixEnd_3702676 633750831955686832273903 := by
  unfold tailWord_3702676
  simp only [CollatzResearch.WordTrace]
  refine ⟨67523844166922346780311941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90031792222563129040415921 67523844166922346780311941)
  ·
    refine ⟨12660720781297940021308489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67523844166922346780311941 12660720781297940021308489)
    ·
      refine ⟨9495540585973455015981367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12660720781297940021308489 9495540585973455015981367)
      ·
        refine ⟨14243310878960182523972051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9495540585973455015981367 14243310878960182523972051)
        ·
          refine ⟨21364966318440273785958077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14243310878960182523972051 21364966318440273785958077)
          ·
            refine ⟨8011862369415102669734279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21364966318440273785958077 8011862369415102669734279)
            ·
              refine ⟨12017793554122654004601419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8011862369415102669734279 12017793554122654004601419)
              ·
                refine ⟨18026690331183981006902129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12017793554122654004601419 18026690331183981006902129)
                ·
                  refine ⟨13520017748387985755176597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18026690331183981006902129 13520017748387985755176597)
                  ·
                    refine ⟨633750831955686832273903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13520017748387985755176597 633750831955686832273903)
                    ·
                      rfl

theorem cell23_3702676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_3702676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702676 prefixEnd_3702676 := by exact prefixLift 3702676
  have htrace : WordTrace (prefixWord ++ tailWord_3702676) baseStart_3702676 baseEnd_3702676 := by
    simpa [prefixWord, tailWord_3702676, baseEnd_3702676] using wordTrace_append hprefix tailTrace_3702676
  have hstable : (prefixWord ++ tailWord_3702676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702676).length < 2 ^ (prefixWord ++ tailWord_3702676).sum := by decide
  have hdescent : baseEnd_3702676 < baseStart_3702676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702679 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_3702679 : Nat := 118140960795 + 3702679 * 2 ^ 59
def prefixEnd_3702679 : Nat := 4983230072969 + 3 ^ 40 * 3702679 * 2
def baseEnd_3702679 : Nat := 1901254036309023985084195

theorem tailTrace_3702679 : CollatzResearch.WordTrace tailWord_3702679 prefixEnd_3702679 1901254036309023985084195 := by
  unfold tailWord_3702679
  simp only [CollatzResearch.WordTrace]
  refine ⟨135047797752833825072983091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90031865168555883381988727 135047797752833825072983091)
  ·
    refine ⟨202571696629250737609474637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135047797752833825072983091 202571696629250737609474637)
    ·
      refine ⟨75964386235969026603552989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202571696629250737609474637 75964386235969026603552989)
      ·
        refine ⟨28486644838488384976332371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75964386235969026603552989 28486644838488384976332371)
        ·
          refine ⟨42729967257732577464498557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28486644838488384976332371 42729967257732577464498557)
          ·
            refine ⟨16023737721649716549186959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42729967257732577464498557 16023737721649716549186959)
            ·
              refine ⟨24035606582474574823780439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16023737721649716549186959 24035606582474574823780439)
              ·
                refine ⟨36053409873711862235670659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24035606582474574823780439 36053409873711862235670659)
                ·
                  refine ⟨54080114810567793353505989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36053409873711862235670659 54080114810567793353505989)
                  ·
                    refine ⟨10140021526981461253782373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54080114810567793353505989 10140021526981461253782373)
                    ·
                      refine ⟨1901254036309023985084195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10140021526981461253782373 1901254036309023985084195)
                      ·
                        rfl

theorem cell23_3702679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_3702679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702679 prefixEnd_3702679 := by exact prefixLift 3702679
  have htrace : WordTrace (prefixWord ++ tailWord_3702679) baseStart_3702679 baseEnd_3702679 := by
    simpa [prefixWord, tailWord_3702679, baseEnd_3702679] using wordTrace_append hprefix tailTrace_3702679
  have hstable : (prefixWord ++ tailWord_3702679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702679).length < 2 ^ (prefixWord ++ tailWord_3702679).sum := by decide
  have hdescent : baseEnd_3702679 < baseStart_3702679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702699 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 3]
def baseStart_3702699 : Nat := 118140960795 + 3702699 * 2 ^ 59
def prefixEnd_3702699 : Nat := 4983230072969 + 3 ^ 40 * 3702699 * 2
def baseEnd_3702699 : Nat := 1901264305922113906834103

theorem tailTrace_3702699 : CollatzResearch.WordTrace tailWord_3702699 prefixEnd_3702699 1901264305922113906834103 := by
  unfold tailWord_3702699
  simp only [CollatzResearch.WordTrace]
  refine ⟨135048527212761368488711151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90032351475174245659140767 135048527212761368488711151)
  ·
    refine ⟨202572790819142052733066727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135048527212761368488711151 202572790819142052733066727)
    ·
      refine ⟨303859186228713079099600091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202572790819142052733066727 303859186228713079099600091)
      ·
        refine ⟨455788779343069618649400137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303859186228713079099600091 455788779343069618649400137)
        ·
          refine ⟨341841584507302213987050103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455788779343069618649400137 341841584507302213987050103)
          ·
            refine ⟨512762376760953320980575155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341841584507302213987050103 512762376760953320980575155)
            ·
              refine ⟨769143565141429981470862733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512762376760953320980575155 769143565141429981470862733)
              ·
                refine ⟨288428836928036243051573525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 769143565141429981470862733 288428836928036243051573525)
                ·
                  refine ⟨13520101731001698893042509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 288428836928036243051573525 13520101731001698893042509)
                  ·
                    refine ⟨5070038149125637084890941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13520101731001698893042509 5070038149125637084890941)
                    ·
                      refine ⟨1901264305922113906834103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5070038149125637084890941 1901264305922113906834103)
                      ·
                        rfl

theorem cell23_3702699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 3].length) (baseStart_3702699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702699 prefixEnd_3702699 := by exact prefixLift 3702699
  have htrace : WordTrace (prefixWord ++ tailWord_3702699) baseStart_3702699 baseEnd_3702699 := by
    simpa [prefixWord, tailWord_3702699, baseEnd_3702699] using wordTrace_append hprefix tailTrace_3702699
  have hstable : (prefixWord ++ tailWord_3702699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702699).length < 2 ^ (prefixWord ++ tailWord_3702699).sum := by decide
  have hdescent : baseEnd_3702699 < baseStart_3702699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702717 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 2, 2, 2]
def baseStart_3702717 : Nat := 118140960795 + 3702717 * 2 ^ 59
def prefixEnd_3702717 : Nat := 4983230072969 + 3 ^ 40 * 3702717 * 2
def baseEnd_3702717 : Nat := 1901273548573894836409021

theorem tailTrace_3702717 : CollatzResearch.WordTrace tailWord_3702717 prefixEnd_3702717 1901273548573894836409021 := by
  unfold tailWord_3702717
  simp only [CollatzResearch.WordTrace]
  refine ⟨135049183726696157562866405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90032789151130771708577603 135049183726696157562866405)
  ·
    refine ⟨25321721948755529543037451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135049183726696157562866405 25321721948755529543037451)
    ·
      refine ⟨37982582923133294314556177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25321721948755529543037451 37982582923133294314556177)
      ·
        refine ⟨28486937192349970735917133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37982582923133294314556177 28486937192349970735917133)
        ·
          refine ⟨10682601447131239025968925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28486937192349970735917133 10682601447131239025968925)
          ·
            refine ⟨4005975542674214634738347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10682601447131239025968925 4005975542674214634738347)
            ·
              refine ⟨6008963314011321952107521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005975542674214634738347 6008963314011321952107521)
              ·
                refine ⟨4506722485508491464080641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6008963314011321952107521 4506722485508491464080641)
                ·
                  refine ⟨3380041864131368598060481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4506722485508491464080641 3380041864131368598060481)
                  ·
                    refine ⟨2535031398098526448545361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3380041864131368598060481 2535031398098526448545361)
                    ·
                      refine ⟨1901273548573894836409021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535031398098526448545361 1901273548573894836409021)
                      ·
                        rfl

theorem cell23_3702717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_3702717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702717 prefixEnd_3702717 := by exact prefixLift 3702717
  have htrace : WordTrace (prefixWord ++ tailWord_3702717) baseStart_3702717 baseEnd_3702717 := by
    simpa [prefixWord, tailWord_3702717, baseEnd_3702717] using wordTrace_append hprefix tailTrace_3702717
  have hstable : (prefixWord ++ tailWord_3702717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702717).length < 2 ^ (prefixWord ++ tailWord_3702717).sum := by decide
  have hdescent : baseEnd_3702717 < baseStart_3702717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702719 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 4, 5]
def baseStart_3702719 : Nat := 118140960795 + 3702719 * 2 ^ 59
def prefixEnd_3702719 : Nat := 4983230072969 + 3 ^ 40 * 3702719 * 2
def baseEnd_3702719 : Nat := 633758191845067942861337

theorem tailTrace_3702719 : CollatzResearch.WordTrace tailWord_3702719 prefixEnd_3702719 633758191845067942861337 := by
  unfold tailWord_3702719
  simp only [CollatzResearch.WordTrace]
  refine ⟨135049256672688911904439211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90032837781792607936292807 135049256672688911904439211)
  ·
    refine ⟨202573885009033367856658817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135049256672688911904439211 202573885009033367856658817)
    ·
      refine ⟨151930413756775025892494113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202573885009033367856658817 151930413756775025892494113)
      ·
        refine ⟨113947810317581269419370585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151930413756775025892494113 113947810317581269419370585)
        ·
          refine ⟨85460857738185952064527939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113947810317581269419370585 85460857738185952064527939)
          ·
            refine ⟨128191286607278928096791909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85460857738185952064527939 128191286607278928096791909)
            ·
              refine ⟨24035866238864799018148483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128191286607278928096791909 24035866238864799018148483)
              ·
                refine ⟨36053799358297198527222725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24035866238864799018148483 36053799358297198527222725)
                ·
                  refine ⟨6760087379680724723854261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36053799358297198527222725 6760087379680724723854261)
                  ·
                    refine ⟨633758191845067942861337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6760087379680724723854261 633758191845067942861337)
                    ·
                      rfl

theorem cell23_3702719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_3702719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702719 prefixEnd_3702719 := by exact prefixLift 3702719
  have htrace : WordTrace (prefixWord ++ tailWord_3702719) baseStart_3702719 baseEnd_3702719 := by
    simpa [prefixWord, tailWord_3702719, baseEnd_3702719] using wordTrace_append hprefix tailTrace_3702719
  have hstable : (prefixWord ++ tailWord_3702719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702719).length < 2 ^ (prefixWord ++ tailWord_3702719).sum := by decide
  have hdescent : baseEnd_3702719 < baseStart_3702719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702756 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3702756 : Nat := 118140960795 + 3702756 * 2 ^ 59
def prefixEnd_3702756 : Nat := 4983230072969 + 3 ^ 40 * 3702756 * 2
def baseEnd_3702756 : Nat := 1901293574319420183821341

theorem tailTrace_3702756 : CollatzResearch.WordTrace tailWord_3702756 prefixEnd_3702756 1901293574319420183821341 := by
  unfold tailWord_3702756
  simp only [CollatzResearch.WordTrace]
  refine ⟨67525303086777433611768061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90033737449036578149024081 67525303086777433611768061)
  ·
    refine ⟨25321988657541537604413023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67525303086777433611768061 25321988657541537604413023)
    ·
      refine ⟨37982982986312306406619535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25321988657541537604413023 37982982986312306406619535)
      ·
        refine ⟨56974474479468459609929303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37982982986312306406619535 56974474479468459609929303)
        ·
          refine ⟨85461711719202689414893955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56974474479468459609929303 85461711719202689414893955)
          ·
            refine ⟨128192567578804034122340933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85461711719202689414893955 128192567578804034122340933)
            ·
              refine ⟨24036106421025756397938925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128192567578804034122340933 24036106421025756397938925)
              ·
                refine ⟨9013539907884658649227097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24036106421025756397938925 9013539907884658649227097)
                ·
                  refine ⟨6760154930913493986920323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9013539907884658649227097 6760154930913493986920323)
                  ·
                    refine ⟨10140232396370240980380485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6760154930913493986920323 10140232396370240980380485)
                    ·
                      refine ⟨1901293574319420183821341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10140232396370240980380485 1901293574319420183821341)
                      ·
                        rfl

theorem cell23_3702756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3702756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702756 prefixEnd_3702756 := by exact prefixLift 3702756
  have htrace : WordTrace (prefixWord ++ tailWord_3702756) baseStart_3702756 baseEnd_3702756 := by
    simpa [prefixWord, tailWord_3702756, baseEnd_3702756] using wordTrace_append hprefix tailTrace_3702756
  have hstable : (prefixWord ++ tailWord_3702756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702756).length < 2 ^ (prefixWord ++ tailWord_3702756).sum := by decide
  have hdescent : baseEnd_3702756 < baseStart_3702756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702776 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 4, 2, 3]
def baseStart_3702776 : Nat := 118140960795 + 3702776 * 2 ^ 59
def prefixEnd_3702776 : Nat := 4983230072969 + 3 ^ 40 * 3702776 * 2
def baseEnd_3702776 : Nat := 1901303843932510105571249

theorem tailTrace_3702776 : CollatzResearch.WordTrace tailWord_3702776 prefixEnd_3702776 1901303843932510105571249 := by
  unfold tailWord_3702776
  simp only [CollatzResearch.WordTrace]
  refine ⟨67525667816741205319632091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90034223755654940426176121 67525667816741205319632091)
  ·
    refine ⟨101288501725111807979448137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67525667816741205319632091 101288501725111807979448137)
    ·
      refine ⟨75966376293833855984586103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101288501725111807979448137 75966376293833855984586103)
      ·
        refine ⟨113949564440750783976879155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75966376293833855984586103 113949564440750783976879155)
        ·
          refine ⟨170924346661126175965318733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113949564440750783976879155 170924346661126175965318733)
          ·
            refine ⟨64096629997922315986994525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170924346661126175965318733 64096629997922315986994525)
            ·
              refine ⟨24036236249220868495122947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64096629997922315986994525 24036236249220868495122947)
              ·
                refine ⟨36054354373831302742684421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24036236249220868495122947 36054354373831302742684421)
                ·
                  refine ⟨6760191445093369264253329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36054354373831302742684421 6760191445093369264253329)
                  ·
                    refine ⟨5070143583820026948189997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6760191445093369264253329 5070143583820026948189997)
                    ·
                      refine ⟨1901303843932510105571249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5070143583820026948189997 1901303843932510105571249)
                      ·
                        rfl

theorem cell23_3702776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_3702776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702776 prefixEnd_3702776 := by exact prefixLift 3702776
  have htrace : WordTrace (prefixWord ++ tailWord_3702776) baseStart_3702776 baseEnd_3702776 := by
    simpa [prefixWord, tailWord_3702776, baseEnd_3702776] using wordTrace_append hprefix tailTrace_3702776
  have hstable : (prefixWord ++ tailWord_3702776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702776).length < 2 ^ (prefixWord ++ tailWord_3702776).sum := by decide
  have hdescent : baseEnd_3702776 < baseStart_3702776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702779 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 8]
def baseStart_3702779 : Nat := 118140960795 + 3702779 * 2 ^ 59
def prefixEnd_3702779 : Nat := 4983230072969 + 3 ^ 40 * 3702779 * 2
def baseEnd_3702779 : Nat := 211256153819385954870415

theorem tailTrace_3702779 : CollatzResearch.WordTrace tailWord_3702779 prefixEnd_3702779 211256153819385954870415 := by
  unfold tailWord_3702779
  simp only [CollatzResearch.WordTrace]
  refine ⟨135051445052471542151623391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90034296701647694767748927 135051445052471542151623391)
  ·
    refine ⟨202577167578707313227435087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135051445052471542151623391 202577167578707313227435087)
    ·
      refine ⟨303865751368060969841152631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202577167578707313227435087 303865751368060969841152631)
      ·
        refine ⟨455798627052091454761728947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303865751368060969841152631 455798627052091454761728947)
        ·
          refine ⟨683697940578137182142593421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455798627052091454761728947 683697940578137182142593421)
          ·
            refine ⟨256386727716801443303472533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683697940578137182142593421 256386727716801443303472533)
            ·
              refine ⟨12018127861725067654850275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256386727716801443303472533 12018127861725067654850275)
              ·
                refine ⟨18027191792587601482275413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12018127861725067654850275 18027191792587601482275413)
                ·
                  refine ⟨211256153819385954870415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18027191792587601482275413 211256153819385954870415)
                  ·
                    rfl

theorem cell23_3702779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 8].length) (baseStart_3702779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702779 prefixEnd_3702779 := by exact prefixLift 3702779
  have htrace : WordTrace (prefixWord ++ tailWord_3702779) baseStart_3702779 baseEnd_3702779 := by
    simpa [prefixWord, tailWord_3702779, baseEnd_3702779] using wordTrace_append hprefix tailTrace_3702779
  have hstable : (prefixWord ++ tailWord_3702779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702779).length < 2 ^ (prefixWord ++ tailWord_3702779).sum := by decide
  have hdescent : baseEnd_3702779 < baseStart_3702779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702783 : List Nat := [1, 1, 2, 2, 1, 2, 1, 8, 1, 4]
def baseStart_3702783 : Nat := 118140960795 + 3702783 * 2 ^ 59
def prefixEnd_3702783 : Nat := 4983230072969 + 3 ^ 40 * 3702783 * 2
def baseEnd_3702783 : Nat := 633769146099030526061239

theorem tailTrace_3702783 : CollatzResearch.WordTrace tailWord_3702783 prefixEnd_3702783 633769146099030526061239 := by
  unfold tailWord_3702783
  simp only [CollatzResearch.WordTrace]
  refine ⟨135051590944457050834769003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90034393962971367223179335 135051590944457050834769003)
  ·
    refine ⟨202577386416685576252153505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135051590944457050834769003 202577386416685576252153505)
    ·
      refine ⟨151933039812514182189115129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202577386416685576252153505 151933039812514182189115129)
      ·
        refine ⟨113949779859385636641836347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151933039812514182189115129 113949779859385636641836347)
        ·
          refine ⟨170924669789078454962754521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113949779859385636641836347 170924669789078454962754521)
          ·
            refine ⟨128193502341808841222065891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170924669789078454962754521 128193502341808841222065891)
            ·
              refine ⟨192290253512713261833098837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128193502341808841222065891 192290253512713261833098837)
              ·
                refine ⟨2253401408352108537106627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 192290253512713261833098837 2253401408352108537106627)
                ·
                  refine ⟨3380102112528162805659941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253401408352108537106627 3380102112528162805659941)
                  ·
                    refine ⟨633769146099030526061239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3380102112528162805659941 633769146099030526061239)
                    ·
                      rfl

theorem cell23_3702783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 1, 4].length) (baseStart_3702783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702783 prefixEnd_3702783 := by exact prefixLift 3702783
  have htrace : WordTrace (prefixWord ++ tailWord_3702783) baseStart_3702783 baseEnd_3702783 := by
    simpa [prefixWord, tailWord_3702783, baseEnd_3702783] using wordTrace_append hprefix tailTrace_3702783
  have hstable : (prefixWord ++ tailWord_3702783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702783).length < 2 ^ (prefixWord ++ tailWord_3702783).sum := by decide
  have hdescent : baseEnd_3702783 < baseStart_3702783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702796 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 6]
def baseStart_3702796 : Nat := 118140960795 + 3702796 * 2 ^ 59
def prefixEnd_3702796 : Nat := 4983230072969 + 3 ^ 40 * 3702796 * 2
def baseEnd_3702796 : Nat := 211257123727288891924573

theorem tailTrace_3702796 : CollatzResearch.WordTrace tailWord_3702796 prefixEnd_3702796 211257123727288891924573 := by
  unfold tailWord_3702796
  simp only [CollatzResearch.WordTrace]
  refine ⟨67526032546704977027496121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90034710062273302703328161 67526032546704977027496121)
  ·
    refine ⟨50644524410028732770622091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67526032546704977027496121 50644524410028732770622091)
    ·
      refine ⟨75966786615043099155933137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50644524410028732770622091 75966786615043099155933137)
      ·
        refine ⟨56975089961282324366949853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75966786615043099155933137 56975089961282324366949853)
        ·
          refine ⟨21365658735480871637606195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56975089961282324366949853 21365658735480871637606195)
          ·
            refine ⟨32048488103221307456409293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21365658735480871637606195 32048488103221307456409293)
            ·
              refine ⟨12018183038707990296153485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32048488103221307456409293 12018183038707990296153485)
              ·
                refine ⟨4506818639515496361057557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12018183038707990296153485 4506818639515496361057557)
                ·
                  refine ⟨211257123727288891924573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4506818639515496361057557 211257123727288891924573)
                  ·
                    rfl

theorem cell23_3702796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_3702796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702796 prefixEnd_3702796 := by exact prefixLift 3702796
  have htrace : WordTrace (prefixWord ++ tailWord_3702796) baseStart_3702796 baseEnd_3702796 := by
    simpa [prefixWord, tailWord_3702796, baseEnd_3702796] using wordTrace_append hprefix tailTrace_3702796
  have hstable : (prefixWord ++ tailWord_3702796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702796).length < 2 ^ (prefixWord ++ tailWord_3702796).sum := by decide
  have hdescent : baseEnd_3702796 < baseStart_3702796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702877 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3702877 : Nat := 118140960795 + 3702877 * 2 ^ 59
def prefixEnd_3702877 : Nat := 4983230072969 + 3 ^ 40 * 3702877 * 2
def baseEnd_3702877 : Nat := 633785235159538070136095

theorem tailTrace_3702877 : CollatzResearch.WordTrace tailWord_3702877 prefixEnd_3702877 633785235159538070136095 := by
  unfold tailWord_3702877
  simp only [CollatzResearch.WordTrace]
  refine ⟨135055019406116504888690885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90036679604077669925793923 135055019406116504888690885)
  ·
    refine ⟨25322816138646844666629541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135055019406116504888690885 25322816138646844666629541)
    ·
      refine ⟨4748028025996283374993039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25322816138646844666629541 4748028025996283374993039)
      ·
        refine ⟨7122042038994425062489559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4748028025996283374993039 7122042038994425062489559)
        ·
          refine ⟨10683063058491637593734339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7122042038994425062489559 10683063058491637593734339)
          ·
            refine ⟨16024594587737456390601509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10683063058491637593734339 16024594587737456390601509)
            ·
              refine ⟨3004611485200773073237783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16024594587737456390601509 3004611485200773073237783)
              ·
                refine ⟨4506917227801159609856675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004611485200773073237783 4506917227801159609856675)
                ·
                  refine ⟨6760375841701739414785013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506917227801159609856675 6760375841701739414785013)
                  ·
                    refine ⟨633785235159538070136095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6760375841701739414785013 633785235159538070136095)
                    ·
                      rfl

theorem cell23_3702877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3702877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702877 prefixEnd_3702877 := by exact prefixLift 3702877
  have htrace : WordTrace (prefixWord ++ tailWord_3702877) baseStart_3702877 baseEnd_3702877 := by
    simpa [prefixWord, tailWord_3702877, baseEnd_3702877] using wordTrace_append hprefix tailTrace_3702877
  have hstable : (prefixWord ++ tailWord_3702877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702877).length < 2 ^ (prefixWord ++ tailWord_3702877).sum := by decide
  have hdescent : baseEnd_3702877 < baseStart_3702877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702880 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 1, 1, 4]
def baseStart_3702880 : Nat := 118140960795 + 3702880 * 2 ^ 59
def prefixEnd_3702880 : Nat := 4983230072969 + 3 ^ 40 * 3702880 * 2
def baseEnd_3702880 : Nat := 1901357245920577698670771

theorem tailTrace_3702880 : CollatzResearch.WordTrace tailWord_3702880 prefixEnd_3702880 1901357245920577698670771 := by
  unfold tailWord_3702880
  simp only [CollatzResearch.WordTrace]
  refine ⟨67527564412552818200525047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90036752550070424267366729 67527564412552818200525047)
  ·
    refine ⟨101291346618829227300787571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67527564412552818200525047 101291346618829227300787571)
    ·
      refine ⟨151937019928243840951181357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101291346618829227300787571 151937019928243840951181357)
      ·
        refine ⟨56976382473091440356693009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151937019928243840951181357 56976382473091440356693009)
        ·
          refine ⟨42732286854818580267519757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56976382473091440356693009 42732286854818580267519757)
          ·
            refine ⟨16024607570556967600319909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42732286854818580267519757 16024607570556967600319909)
            ·
              refine ⟨3004613919479431425059983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16024607570556967600319909 3004613919479431425059983)
              ·
                refine ⟨4506920879219147137589975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004613919479431425059983 4506920879219147137589975)
                ·
                  refine ⟨6760381318828720706384963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506920879219147137589975 6760381318828720706384963)
                  ·
                    refine ⟨10140571978243081059577445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6760381318828720706384963 10140571978243081059577445)
                    ·
                      refine ⟨1901357245920577698670771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10140571978243081059577445 1901357245920577698670771)
                      ·
                        rfl

theorem cell23_3702880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_3702880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702880 prefixEnd_3702880 := by exact prefixLift 3702880
  have htrace : WordTrace (prefixWord ++ tailWord_3702880) baseStart_3702880 baseEnd_3702880 := by
    simpa [prefixWord, tailWord_3702880, baseEnd_3702880] using wordTrace_append hprefix tailTrace_3702880
  have hstable : (prefixWord ++ tailWord_3702880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702880).length < 2 ^ (prefixWord ++ tailWord_3702880).sum := by decide
  have hdescent : baseEnd_3702880 < baseStart_3702880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702890 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_3702890 : Nat := 118140960795 + 3702890 * 2 ^ 59
def prefixEnd_3702890 : Nat := 4983230072969 + 3 ^ 40 * 3702890 * 2
def baseEnd_3702890 : Nat := 633787460242374219848575

theorem tailTrace_3702890 : CollatzResearch.WordTrace tailWord_3702890 prefixEnd_3702890 633787460242374219848575 := by
  unfold tailWord_3702890
  simp only [CollatzResearch.WordTrace]
  refine ⟨33763873388767352027228531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90036995703379605405942749 33763873388767352027228531)
  ·
    refine ⟨50645810083151028040842797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33763873388767352027228531 50645810083151028040842797)
    ·
      refine ⟨18992178781181635515316049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50645810083151028040842797 18992178781181635515316049)
      ·
        refine ⟨14244134085886226636487037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18992178781181635515316049 14244134085886226636487037)
        ·
          refine ⟨5341550282207334988682639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14244134085886226636487037 5341550282207334988682639)
          ·
            refine ⟨8012325423311002483023959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5341550282207334988682639 8012325423311002483023959)
            ·
              refine ⟨12018488134966503724535939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8012325423311002483023959 12018488134966503724535939)
              ·
                refine ⟨18027732202449755586803909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12018488134966503724535939 18027732202449755586803909)
                ·
                  refine ⟨3380199787959329172525733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18027732202449755586803909 3380199787959329172525733)
                  ·
                    refine ⟨633787460242374219848575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3380199787959329172525733 633787460242374219848575)
                    ·
                      rfl

theorem cell23_3702890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_3702890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702890 prefixEnd_3702890 := by exact prefixLift 3702890
  have htrace : WordTrace (prefixWord ++ tailWord_3702890) baseStart_3702890 baseEnd_3702890 := by
    simpa [prefixWord, tailWord_3702890, baseEnd_3702890] using wordTrace_append hprefix tailTrace_3702890
  have hstable : (prefixWord ++ tailWord_3702890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702890).length < 2 ^ (prefixWord ++ tailWord_3702890).sum := by decide
  have hdescent : baseEnd_3702890 < baseStart_3702890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702897 : List Nat := [1, 2, 2, 2, 1, 1, 3, 6, 1, 2, 2]
def baseStart_3702897 : Nat := 118140960795 + 3702897 * 2 ^ 59
def prefixEnd_3702897 : Nat := 4983230072969 + 3 ^ 40 * 3702897 * 2
def baseEnd_3702897 : Nat := 1901365975091704132158193

theorem tailTrace_3702897 : CollatzResearch.WordTrace tailWord_3702897 prefixEnd_3702897 1901365975091704132158193 := by
  unfold tailWord_3702897
  simp only [CollatzResearch.WordTrace]
  refine ⟨135055748866044048304418945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90037165910696032202945963 135055748866044048304418945)
  ·
    refine ⟨101291811649533036228314209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135055748866044048304418945 101291811649533036228314209)
    ·
      refine ⟨75968858737149777171235657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101291811649533036228314209 75968858737149777171235657)
      ·
        refine ⟨56976644052862332878426743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75968858737149777171235657 56976644052862332878426743)
        ·
          refine ⟨85464966079293499317640115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56976644052862332878426743 85464966079293499317640115)
          ·
            refine ⟨128197449118940248976460173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85464966079293499317640115 128197449118940248976460173)
            ·
              refine ⟨48074043419602593366172565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128197449118940248976460173 48074043419602593366172565)
              ·
                refine ⟨2253470785293871564039339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48074043419602593366172565 2253470785293871564039339)
                ·
                  refine ⟨3380206177940807346059009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253470785293871564039339 3380206177940807346059009)
                  ·
                    refine ⟨2535154633455605509544257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3380206177940807346059009 2535154633455605509544257)
                    ·
                      refine ⟨1901365975091704132158193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535154633455605509544257 1901365975091704132158193)
                      ·
                        rfl

theorem cell23_3702897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_3702897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702897 prefixEnd_3702897 := by exact prefixLift 3702897
  have htrace : WordTrace (prefixWord ++ tailWord_3702897) baseStart_3702897 baseEnd_3702897 := by
    simpa [prefixWord, tailWord_3702897, baseEnd_3702897] using wordTrace_append hprefix tailTrace_3702897
  have hstable : (prefixWord ++ tailWord_3702897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702897).length < 2 ^ (prefixWord ++ tailWord_3702897).sum := by decide
  have hdescent : baseEnd_3702897 < baseStart_3702897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702920 : List Nat := [2, 1, 3, 4, 1, 3, 2, 7]
def baseStart_3702920 : Nat := 118140960795 + 3702920 * 2 ^ 59
def prefixEnd_3702920 : Nat := 4983230072969 + 3 ^ 40 * 3702920 * 2
def baseEnd_3702920 : Nat := 70421399449879908969281

theorem tailTrace_3702920 : CollatzResearch.WordTrace tailWord_3702920 prefixEnd_3702920 70421399449879908969281 := by
  unfold tailWord_3702920
  simp only [CollatzResearch.WordTrace]
  refine ⟨67528293872480361616253107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90037725163307148821670809 67528293872480361616253107)
  ·
    refine ⟨101292440808720542424379661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67528293872480361616253107 101292440808720542424379661)
    ·
      refine ⟨37984665303270203409142373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101292440808720542424379661 37984665303270203409142373)
      ·
        refine ⟨7122124744363163139214195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37984665303270203409142373 7122124744363163139214195)
        ·
          refine ⟨10683187116544744708821293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7122124744363163139214195 10683187116544744708821293)
          ·
            refine ⟨4006195168704279265807985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10683187116544744708821293 4006195168704279265807985)
            ·
              refine ⟨3004646376528209449355989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006195168704279265807985 3004646376528209449355989)
              ·
                refine ⟨70421399449879908969281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3004646376528209449355989 70421399449879908969281)
                ·
                  rfl

theorem cell23_3702920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 7].length) (baseStart_3702920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702920 prefixEnd_3702920 := by exact prefixLift 3702920
  have htrace : WordTrace (prefixWord ++ tailWord_3702920) baseStart_3702920 baseEnd_3702920 := by
    simpa [prefixWord, tailWord_3702920, baseEnd_3702920] using wordTrace_append hprefix tailTrace_3702920
  have hstable : (prefixWord ++ tailWord_3702920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702920).length < 2 ^ (prefixWord ++ tailWord_3702920).sum := by decide
  have hdescent : baseEnd_3702920 < baseStart_3702920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702930 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3702930 : Nat := 118140960795 + 3702930 * 2 ^ 59
def prefixEnd_3702930 : Nat := 4983230072969 + 3 ^ 40 * 3702930 * 2
def baseEnd_3702930 : Nat := 1901382919953302503045541

theorem tailTrace_3702930 : CollatzResearch.WordTrace tailWord_3702930 prefixEnd_3702930 1901382919953302503045541 := by
  unfold tailWord_3702930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33764238118731123735092561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90037968316616329960246829 33764238118731123735092561)
  ·
    refine ⟨25323178589048342801319421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33764238118731123735092561 25323178589048342801319421)
    ·
      refine ⟨9496191970893128550494783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25323178589048342801319421 9496191970893128550494783)
      ·
        refine ⟨14244287956339692825742175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496191970893128550494783 14244287956339692825742175)
        ·
          refine ⟨21366431934509539238613263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14244287956339692825742175 21366431934509539238613263)
          ·
            refine ⟨32049647901764308857919895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21366431934509539238613263 32049647901764308857919895)
            ·
              refine ⟨48074471852646463286879843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32049647901764308857919895 48074471852646463286879843)
              ·
                refine ⟨72111707778969694930319765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48074471852646463286879843 72111707778969694930319765)
                ·
                  refine ⟨3380236302139204449858739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72111707778969694930319765 3380236302139204449858739)
                  ·
                    refine ⟨5070354453208806674788109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3380236302139204449858739 5070354453208806674788109)
                    ·
                      refine ⟨1901382919953302503045541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5070354453208806674788109 1901382919953302503045541)
                      ·
                        rfl

theorem cell23_3702930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3702930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702930 prefixEnd_3702930 := by exact prefixLift 3702930
  have htrace : WordTrace (prefixWord ++ tailWord_3702930) baseStart_3702930 baseEnd_3702930 := by
    simpa [prefixWord, tailWord_3702930, baseEnd_3702930] using wordTrace_append hprefix tailTrace_3702930
  have hstable : (prefixWord ++ tailWord_3702930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702930).length < 2 ^ (prefixWord ++ tailWord_3702930).sum := by decide
  have hdescent : baseEnd_3702930 < baseStart_3702930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702958 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3702958 : Nat := 118140960795 + 3702958 * 2 ^ 59
def prefixEnd_3702958 : Nat := 4983230072969 + 3 ^ 40 * 3702958 * 2
def baseEnd_3702958 : Nat := 633799099137209464498471

theorem tailTrace_3702958 : CollatzResearch.WordTrace tailWord_3702958 prefixEnd_3702958 633799099137209464498471 := by
  unfold tailWord_3702958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16882246714852881965298691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90038649145882037148259685 16882246714852881965298691)
  ·
    refine ⟨25323370072279322947948037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16882246714852881965298691 25323370072279322947948037)
    ·
      refine ⟨4748131888552373052740257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25323370072279322947948037 4748131888552373052740257)
      ·
        refine ⟨3561098916414279789555193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4748131888552373052740257 3561098916414279789555193)
        ·
          refine ⟨2670824187310709842166395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3561098916414279789555193 2670824187310709842166395)
          ·
            refine ⟨4006236280966064763249593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670824187310709842166395 4006236280966064763249593)
            ·
              refine ⟨3004677210724548572437195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006236280966064763249593 3004677210724548572437195)
              ·
                refine ⟨4507015816086822858655793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004677210724548572437195 4507015816086822858655793)
                ·
                  refine ⟨3380261862065117143991845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4507015816086822858655793 3380261862065117143991845)
                  ·
                    refine ⟨633799099137209464498471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3380261862065117143991845 633799099137209464498471)
                    ·
                      rfl

theorem cell23_3702958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3702958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702958 prefixEnd_3702958 := by exact prefixLift 3702958
  have htrace : WordTrace (prefixWord ++ tailWord_3702958) baseStart_3702958 baseEnd_3702958 := by
    simpa [prefixWord, tailWord_3702958, baseEnd_3702958] using wordTrace_append hprefix tailTrace_3702958
  have hstable : (prefixWord ++ tailWord_3702958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702958).length < 2 ^ (prefixWord ++ tailWord_3702958).sum := by decide
  have hdescent : baseEnd_3702958 < baseStart_3702958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703043 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 4]
def baseStart_3703043 : Nat := 118140960795 + 3703043 * 2 ^ 59
def prefixEnd_3703043 : Nat := 4983230072969 + 3 ^ 40 * 3703043 * 2
def baseEnd_3703043 : Nat := 1901440943267260560932521

theorem tailTrace_3703043 : CollatzResearch.WordTrace tailWord_3703043 prefixEnd_3703043 1901440943267260560932521 := by
  unfold tailWord_3703043
  simp only [CollatzResearch.WordTrace]
  refine ⟨135061073923515115239233783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90040715949010076826155855 135061073923515115239233783)
  ·
    refine ⟨202591610885272672858850675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135061073923515115239233783 202591610885272672858850675)
    ·
      refine ⟨303887416327909009288276013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202591610885272672858850675 303887416327909009288276013)
      ·
        refine ⟨113957781122965878483103505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303887416327909009288276013 113957781122965878483103505)
        ·
          refine ⟨85468335842224408862327629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113957781122965878483103505 85468335842224408862327629)
          ·
            refine ⟨32050625940834153323372861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85468335842224408862327629 32050625940834153323372861)
            ·
              refine ⟨12018984727812807496264823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32050625940834153323372861 12018984727812807496264823)
              ·
                refine ⟨18028477091719211244397235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12018984727812807496264823 18028477091719211244397235)
                ·
                  refine ⟨27042715637578816866595853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18028477091719211244397235 27042715637578816866595853)
                  ·
                    refine ⟨10141018364092056324973445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27042715637578816866595853 10141018364092056324973445)
                    ·
                      refine ⟨1901440943267260560932521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10141018364092056324973445 1901440943267260560932521)
                      ·
                        rfl

theorem cell23_3703043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_3703043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703043 prefixEnd_3703043 := by exact prefixLift 3703043
  have htrace : WordTrace (prefixWord ++ tailWord_3703043) baseStart_3703043 baseEnd_3703043 := by
    simpa [prefixWord, tailWord_3703043, baseEnd_3703043] using wordTrace_append hprefix tailTrace_3703043
  have hstable : (prefixWord ++ tailWord_3703043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703043).length < 2 ^ (prefixWord ++ tailWord_3703043).sum := by decide
  have hdescent : baseEnd_3703043 < baseStart_3703043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703113 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 5, 5]
def baseStart_3703113 : Nat := 118140960795 + 3703113 * 2 ^ 59
def prefixEnd_3703113 : Nat := 4983230072969 + 3 ^ 40 * 3703113 * 2
def baseEnd_3703113 : Nat := 633825628971025095685733

theorem tailTrace_3703113 : CollatzResearch.WordTrace tailWord_3703113 prefixEnd_3703113 633825628971025095685733 := by
  unfold tailWord_3703113
  simp only [CollatzResearch.WordTrace]
  refine ⟨135063627033261517194281993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90042418022174344796187995 135063627033261517194281993)
  ·
    refine ⟨101297720274946137895711495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135063627033261517194281993 101297720274946137895711495)
    ·
      refine ⟨151946580412419206843567243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101297720274946137895711495 151946580412419206843567243)
      ·
        refine ⟨227919870618628810265350865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151946580412419206843567243 227919870618628810265350865)
        ·
          refine ⟨170939902963971607699013149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227919870618628810265350865 170939902963971607699013149)
          ·
            refine ⟨64102463611489352887129931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170939902963971607699013149 64102463611489352887129931)
            ·
              refine ⟨96153695417234029330694897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64102463611489352887129931 96153695417234029330694897)
              ·
                refine ⟨72115271562925521998021173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96153695417234029330694897 72115271562925521998021173)
                ·
                  refine ⟨6760806709024267687314485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72115271562925521998021173 6760806709024267687314485)
                  ·
                    refine ⟨633825628971025095685733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6760806709024267687314485 633825628971025095685733)
                    ·
                      rfl

theorem cell23_3703113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_3703113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703113 prefixEnd_3703113 := by exact prefixLift 3703113
  have htrace : WordTrace (prefixWord ++ tailWord_3703113) baseStart_3703113 baseEnd_3703113 := by
    simpa [prefixWord, tailWord_3703113, baseEnd_3703113] using wordTrace_append hprefix tailTrace_3703113
  have hstable : (prefixWord ++ tailWord_3703113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703113).length < 2 ^ (prefixWord ++ tailWord_3703113).sum := by decide
  have hdescent : baseEnd_3703113 < baseStart_3703113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703154 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 2, 3, 2]
def baseStart_3703154 : Nat := 118140960795 + 3703154 * 2 ^ 59
def prefixEnd_3703154 : Nat := 4983230072969 + 3 ^ 40 * 3703154 * 2
def baseEnd_3703154 : Nat := 1901497939619909626644511

theorem tailTrace_3703154 : CollatzResearch.WordTrace tailWord_3703154 prefixEnd_3703154 1901497939619909626644511 := by
  unfold tailWord_3703154
  simp only [CollatzResearch.WordTrace]
  refine ⟨33766280606528245299131129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90043414950741987464349677 33766280606528245299131129)
  ·
    refine ⟨25324710454896183974348347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33766280606528245299131129 25324710454896183974348347)
    ·
      refine ⟨37987065682344275961522521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25324710454896183974348347 37987065682344275961522521)
      ·
        refine ⟨28490299261758206971141891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37987065682344275961522521 28490299261758206971141891)
        ·
          refine ⟨42735448892637310456712837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28490299261758206971141891 42735448892637310456712837)
          ·
            refine ⟨8012896667369495710633657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42735448892637310456712837 8012896667369495710633657)
            ·
              refine ⟨6009672500527121782975243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8012896667369495710633657 6009672500527121782975243)
              ·
                refine ⟨9014508750790682674462865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6009672500527121782975243 9014508750790682674462865)
                ·
                  refine ⟨6760881563093012005847149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9014508750790682674462865 6760881563093012005847149)
                  ·
                    refine ⟨2535330586159879502192681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6760881563093012005847149 2535330586159879502192681)
                    ·
                      refine ⟨1901497939619909626644511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535330586159879502192681 1901497939619909626644511)
                      ·
                        rfl

theorem cell23_3703154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_3703154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703154 prefixEnd_3703154 := by exact prefixLift 3703154
  have htrace : WordTrace (prefixWord ++ tailWord_3703154) baseStart_3703154 baseEnd_3703154 := by
    simpa [prefixWord, tailWord_3703154, baseEnd_3703154] using wordTrace_append hprefix tailTrace_3703154
  have hstable : (prefixWord ++ tailWord_3703154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703154).length < 2 ^ (prefixWord ++ tailWord_3703154).sum := by decide
  have hdescent : baseEnd_3703154 < baseStart_3703154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703167 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 5, 2, 2]
def baseStart_3703167 : Nat := 118140960795 + 3703167 * 2 ^ 59
def prefixEnd_3703167 : Nat := 4983230072969 + 3 ^ 40 * 3703167 * 2
def baseEnd_3703167 : Nat := 1901504614868418075781951

theorem tailTrace_3703167 : CollatzResearch.WordTrace tailWord_3703167 prefixEnd_3703167 1901504614868418075781951 := by
  unfold tailWord_3703167
  simp only [CollatzResearch.WordTrace]
  refine ⟨135065596575065884416747755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90043731050043922944498503 135065596575065884416747755)
  ·
    refine ⟨202598394862598826625121633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135065596575065884416747755 202598394862598826625121633)
    ·
      refine ⟨151948796146949119968841225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202598394862598826625121633 151948796146949119968841225)
      ·
        refine ⟨113961597110211839976630919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151948796146949119968841225 113961597110211839976630919)
        ·
          refine ⟨170942395665317759964946379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113961597110211839976630919 170942395665317759964946379)
          ·
            refine ⟨256413593497976639947419569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170942395665317759964946379 256413593497976639947419569)
            ·
              refine ⟨192310195123482479960564677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256413593497976639947419569 192310195123482479960564677)
              ·
                refine ⟨36058161585652964992605877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192310195123482479960564677 36058161585652964992605877)
                ·
                  refine ⟨3380452648654965468056801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36058161585652964992605877 3380452648654965468056801)
                  ·
                    refine ⟨2535339486491224101042601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3380452648654965468056801 2535339486491224101042601)
                    ·
                      refine ⟨1901504614868418075781951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535339486491224101042601 1901504614868418075781951)
                      ·
                        rfl

theorem cell23_3703167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_3703167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703167 prefixEnd_3703167 := by exact prefixLift 3703167
  have htrace : WordTrace (prefixWord ++ tailWord_3703167) baseStart_3703167 baseEnd_3703167 := by
    simpa [prefixWord, tailWord_3703167, baseEnd_3703167] using wordTrace_append hprefix tailTrace_3703167
  have hstable : (prefixWord ++ tailWord_3703167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703167).length < 2 ^ (prefixWord ++ tailWord_3703167).sum := by decide
  have hdescent : baseEnd_3703167 < baseStart_3703167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703177 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 2, 4]
def baseStart_3703177 : Nat := 118140960795 + 3703177 * 2 ^ 59
def prefixEnd_3703177 : Nat := 4983230072969 + 3 ^ 40 * 3703177 * 2
def baseEnd_3703177 : Nat := 633836583224987678885635

theorem tailTrace_3703177 : CollatzResearch.WordTrace tailWord_3703177 prefixEnd_3703177 633836583224987678885635 := by
  unfold tailWord_3703177
  simp only [CollatzResearch.WordTrace]
  refine ⟨135065961305029656124611785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90043974203353104083074523 135065961305029656124611785)
  ·
    refine ⟨101299470978772242093458839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135065961305029656124611785 101299470978772242093458839)
    ·
      refine ⟨151949206468158363140188259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101299470978772242093458839 151949206468158363140188259)
      ·
        refine ⟨227923809702237544710282389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151949206468158363140188259 227923809702237544710282389)
        ·
          refine ⟨10683928579792384908294487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227923809702237544710282389 10683928579792384908294487)
          ·
            refine ⟨16025892869688577362441731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10683928579792384908294487 16025892869688577362441731)
            ·
              refine ⟨24038839304532866043662597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16025892869688577362441731 24038839304532866043662597)
              ·
                refine ⟨4507282369599912383186737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24038839304532866043662597 4507282369599912383186737)
                ·
                  refine ⟨3380461777199934287390053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4507282369599912383186737 3380461777199934287390053)
                  ·
                    refine ⟨633836583224987678885635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3380461777199934287390053 633836583224987678885635)
                    ·
                      rfl

theorem cell23_3703177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 4].length) (baseStart_3703177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703177 prefixEnd_3703177 := by exact prefixLift 3703177
  have htrace : WordTrace (prefixWord ++ tailWord_3703177) baseStart_3703177 baseEnd_3703177 := by
    simpa [prefixWord, tailWord_3703177, baseEnd_3703177] using wordTrace_append hprefix tailTrace_3703177
  have hstable : (prefixWord ++ tailWord_3703177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703177).length < 2 ^ (prefixWord ++ tailWord_3703177).sum := by decide
  have hdescent : baseEnd_3703177 < baseStart_3703177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703178 : List Nat := [3, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3]
def baseStart_3703178 : Nat := 118140960795 + 3703178 * 2 ^ 59
def prefixEnd_3703178 : Nat := 4983230072969 + 3 ^ 40 * 3703178 * 2
def baseEnd_3703178 : Nat := 1901510263155617532744401

theorem tailTrace_3703178 : CollatzResearch.WordTrace tailWord_3703178 prefixEnd_3703178 1901510263155617532744401 := by
  unfold tailWord_3703178
  simp only [CollatzResearch.WordTrace]
  refine ⟨33766499444506508323849547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90043998518684022196932125 33766499444506508323849547)
  ·
    refine ⟨50649749166759762485774321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33766499444506508323849547 50649749166759762485774321)
    ·
      refine ⟨37987311875069821864330741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50649749166759762485774321 37987311875069821864330741)
      ·
        refine ⟨3561310488287795799781007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37987311875069821864330741 3561310488287795799781007)
        ·
          refine ⟨5341965732431693699671511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561310488287795799781007 5341965732431693699671511)
          ·
            refine ⟨8012948598647540549507267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5341965732431693699671511 8012948598647540549507267)
            ·
              refine ⟨12019422897971310824260901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8012948598647540549507267 12019422897971310824260901)
              ·
                refine ⟨2253641793369620779548919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12019422897971310824260901 2253641793369620779548919)
                ·
                  refine ⟨3380462690054431169323379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253641793369620779548919 3380462690054431169323379)
                  ·
                    refine ⟨5070694035081646753985069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3380462690054431169323379 5070694035081646753985069)
                    ·
                      refine ⟨1901510263155617532744401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5070694035081646753985069 1901510263155617532744401)
                      ·
                        rfl

theorem cell23_3703178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_3703178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703178 prefixEnd_3703178 := by exact prefixLift 3703178
  have htrace : WordTrace (prefixWord ++ tailWord_3703178) baseStart_3703178 baseEnd_3703178 := by
    simpa [prefixWord, tailWord_3703178, baseEnd_3703178] using wordTrace_append hprefix tailTrace_3703178
  have hstable : (prefixWord ++ tailWord_3703178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703178).length < 2 ^ (prefixWord ++ tailWord_3703178).sum := by decide
  have hdescent : baseEnd_3703178 < baseStart_3703178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703207 : List Nat := [1, 1, 6, 1, 1, 3, 3, 7]
def baseStart_3703207 : Nat := 118140960795 + 3703207 * 2 ^ 59
def prefixEnd_3703207 : Nat := 4983230072969 + 3 ^ 40 * 3703207 * 2
def baseEnd_3703207 : Nat := 70426857559059182195621

theorem tailTrace_3703207 : CollatzResearch.WordTrace tailWord_3703207 prefixEnd_3703207 70426857559059182195621 := by
  unfold tailWord_3703207
  simp only [CollatzResearch.WordTrace]
  refine ⟨135067055494920971248203875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90044703663280647498802583 135067055494920971248203875)
  ·
    refine ⟨202600583242381456872305813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135067055494920971248203875 202600583242381456872305813)
    ·
      refine ⟨9496902339486630790889335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202600583242381456872305813 9496902339486630790889335)
      ·
        refine ⟨14245353509229946186334003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496902339486630790889335 14245353509229946186334003)
        ·
          refine ⟨21368030263844919279501005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14245353509229946186334003 21368030263844919279501005)
          ·
            refine ⟨8013011348941844729812877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21368030263844919279501005 8013011348941844729812877)
            ·
              refine ⟨3004879255853191773679829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8013011348941844729812877 3004879255853191773679829)
              ·
                refine ⟨70426857559059182195621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3004879255853191773679829 70426857559059182195621)
                ·
                  rfl

theorem cell23_3703207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 7].length) (baseStart_3703207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703207 prefixEnd_3703207 := by exact prefixLift 3703207
  have htrace : WordTrace (prefixWord ++ tailWord_3703207) baseStart_3703207 baseEnd_3703207 := by
    simpa [prefixWord, tailWord_3703207, baseEnd_3703207] using wordTrace_append hprefix tailTrace_3703207
  have hstable : (prefixWord ++ tailWord_3703207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703207).length < 2 ^ (prefixWord ++ tailWord_3703207).sum := by decide
  have hdescent : baseEnd_3703207 < baseStart_3703207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703217 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3703217 : Nat := 118140960795 + 3703217 * 2 ^ 59
def prefixEnd_3703217 : Nat := 4983230072969 + 3 ^ 40 * 3703217 * 2
def baseEnd_3703217 : Nat := 1901530288901142880156721

theorem tailTrace_3703217 : CollatzResearch.WordTrace tailWord_3703217 prefixEnd_3703217 1901530288901142880156721 := by
  unfold tailWord_3703217
  simp only [CollatzResearch.WordTrace]
  refine ⟨135067420224884742956067905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90044946816589828637378603 135067420224884742956067905)
  ·
    refine ⟨101300565168663557217050929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135067420224884742956067905 101300565168663557217050929)
    ·
      refine ⟨75975423876497667912788197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101300565168663557217050929 75975423876497667912788197)
      ·
        refine ⟨14245391976843312733647787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75975423876497667912788197 14245391976843312733647787)
        ·
          refine ⟨21368087965264969100471681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14245391976843312733647787 21368087965264969100471681)
          ·
            refine ⟨16026065973948726825353761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21368087965264969100471681 16026065973948726825353761)
            ·
              refine ⟨12019549480461545119015321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16026065973948726825353761 12019549480461545119015321)
              ·
                refine ⟨9014662110346158839261491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12019549480461545119015321 9014662110346158839261491)
                ·
                  refine ⟨13521993165519238258892237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9014662110346158839261491 13521993165519238258892237)
                  ·
                    refine ⟨5070747437069714347084589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13521993165519238258892237 5070747437069714347084589)
                    ·
                      refine ⟨1901530288901142880156721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5070747437069714347084589 1901530288901142880156721)
                      ·
                        rfl

theorem cell23_3703217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3703217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703217 prefixEnd_3703217 := by exact prefixLift 3703217
  have htrace : WordTrace (prefixWord ++ tailWord_3703217) baseStart_3703217 baseEnd_3703217 := by
    simpa [prefixWord, tailWord_3703217, baseEnd_3703217] using wordTrace_append hprefix tailTrace_3703217
  have hstable : (prefixWord ++ tailWord_3703217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703217).length < 2 ^ (prefixWord ++ tailWord_3703217).sum := by decide
  have hdescent : baseEnd_3703217 < baseStart_3703217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703261 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_3703261 : Nat := 118140960795 + 3703261 * 2 ^ 59
def prefixEnd_3703261 : Nat := 4983230072969 + 3 ^ 40 * 3703261 * 2
def baseEnd_3703261 : Nat := 1901552882049940708006519

theorem tailTrace_3703261 : CollatzResearch.WordTrace tailWord_3703261 prefixEnd_3703261 1901552882049940708006519 := by
  unfold tailWord_3703261
  simp only [CollatzResearch.WordTrace]
  refine ⟨135069025036725338470669637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90046016691150225647113091 135069025036725338470669637)
  ·
    refine ⟨25325442194386000963250557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135069025036725338470669637 25325442194386000963250557)
    ·
      refine ⟨9497040822894750361218959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25325442194386000963250557 9497040822894750361218959)
      ·
        refine ⟨14245561234342125541828439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9497040822894750361218959 14245561234342125541828439)
        ·
          refine ⟨21368341851513188312742659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14245561234342125541828439 21368341851513188312742659)
          ·
            refine ⟨32052512777269782469113989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21368341851513188312742659 32052512777269782469113989)
            ·
              refine ⟨6009846145738084212958873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32052512777269782469113989 6009846145738084212958873)
              ·
                refine ⟨4507384609303563159719155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6009846145738084212958873 4507384609303563159719155)
                ·
                  refine ⟨6761076913955344739578733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507384609303563159719155 6761076913955344739578733)
                  ·
                    refine ⟨2535403842733254277342025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6761076913955344739578733 2535403842733254277342025)
                    ·
                      refine ⟨1901552882049940708006519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535403842733254277342025 1901552882049940708006519)
                      ·
                        rfl

theorem cell23_3703261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_3703261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703261 prefixEnd_3703261 := by exact prefixLift 3703261
  have htrace : WordTrace (prefixWord ++ tailWord_3703261) baseStart_3703261 baseEnd_3703261 := by
    simpa [prefixWord, tailWord_3703261, baseEnd_3703261] using wordTrace_append hprefix tailTrace_3703261
  have hstable : (prefixWord ++ tailWord_3703261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703261).length < 2 ^ (prefixWord ++ tailWord_3703261).sum := by decide
  have hdescent : baseEnd_3703261 < baseStart_3703261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703277 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3703277 : Nat := 118140960795 + 3703277 * 2 ^ 59
def prefixEnd_3703277 : Nat := 4983230072969 + 3 ^ 40 * 3703277 * 2
def baseEnd_3703277 : Nat := 1901561097740412645406445

theorem tailTrace_3703277 : CollatzResearch.WordTrace tailWord_3703277 prefixEnd_3703277 1901561097740412645406445 := by
  unfold tailWord_3703277
  simp only [CollatzResearch.WordTrace]
  refine ⟨135069608604667373203252085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90046405736444915468834723 135069608604667373203252085)
  ·
    refine ⟨12662775806687566237804883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135069608604667373203252085 12662775806687566237804883)
    ·
      refine ⟨18994163710031349356707325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12662775806687566237804883 18994163710031349356707325)
      ·
        refine ⟨7122811391261756008765247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18994163710031349356707325 7122811391261756008765247)
        ·
          refine ⟨10684217086892634013147871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7122811391261756008765247 10684217086892634013147871)
          ·
            refine ⟨16026325630338951019721807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10684217086892634013147871 16026325630338951019721807)
            ·
              refine ⟨24039488445508426529582711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16026325630338951019721807 24039488445508426529582711)
              ·
                refine ⟨36059232668262639794374067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24039488445508426529582711 36059232668262639794374067)
                ·
                  refine ⟨54088849002393959691561101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36059232668262639794374067 54088849002393959691561101)
                  ·
                    refine ⟨20283318375897734884335413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54088849002393959691561101 20283318375897734884335413)
                    ·
                      refine ⟨1901561097740412645406445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20283318375897734884335413 1901561097740412645406445)
                      ·
                        rfl

theorem cell23_3703277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3703277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703277 prefixEnd_3703277 := by exact prefixLift 3703277
  have htrace : WordTrace (prefixWord ++ tailWord_3703277) baseStart_3703277 baseEnd_3703277 := by
    simpa [prefixWord, tailWord_3703277, baseEnd_3703277] using wordTrace_append hprefix tailTrace_3703277
  have hstable : (prefixWord ++ tailWord_3703277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703277).length < 2 ^ (prefixWord ++ tailWord_3703277).sum := by decide
  have hdescent : baseEnd_3703277 < baseStart_3703277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703297 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 7]
def baseStart_3703297 : Nat := 118140960795 + 3703297 * 2 ^ 59
def prefixEnd_3703297 : Nat := 4983230072969 + 3 ^ 40 * 3703297 * 2
def baseEnd_3703297 : Nat := 211285707483722507461817

theorem tailTrace_3703297 : CollatzResearch.WordTrace tailWord_3703297 prefixEnd_3703297 211285707483722507461817 := by
  unfold tailWord_3703297
  simp only [CollatzResearch.WordTrace]
  refine ⟨135070338064594916618980145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90046892043063277745986763 135070338064594916618980145)
  ·
    refine ⟨101302753548446187464235109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135070338064594916618980145 101302753548446187464235109)
    ·
      refine ⟨18994266290333660149544083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101302753548446187464235109 18994266290333660149544083)
      ·
        refine ⟨28491399435500490224316125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18994266290333660149544083 28491399435500490224316125)
        ·
          refine ⟨10684274788312683834118547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28491399435500490224316125 10684274788312683834118547)
          ·
            refine ⟨16026412182469025751177821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10684274788312683834118547 16026412182469025751177821)
            ·
              refine ⟨6009904568425884656691683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16026412182469025751177821 6009904568425884656691683)
              ·
                refine ⟨9014856852638826985037525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6009904568425884656691683 9014856852638826985037525)
                ·
                  refine ⟨211285707483722507461817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9014856852638826985037525 211285707483722507461817)
                  ·
                    rfl

theorem cell23_3703297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 7].length) (baseStart_3703297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703297 prefixEnd_3703297 := by exact prefixLift 3703297
  have htrace : WordTrace (prefixWord ++ tailWord_3703297) baseStart_3703297 baseEnd_3703297 := by
    simpa [prefixWord, tailWord_3703297, baseEnd_3703297] using wordTrace_append hprefix tailTrace_3703297
  have hstable : (prefixWord ++ tailWord_3703297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703297).length < 2 ^ (prefixWord ++ tailWord_3703297).sum := by decide
  have hdescent : baseEnd_3703297 < baseStart_3703297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703302 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_3703302 : Nat := 118140960795 + 3703302 * 2 ^ 59
def prefixEnd_3703302 : Nat := 4983230072969 + 3 ^ 40 * 3703302 * 2
def baseEnd_3703302 : Nat := 1901573934756775047593831

theorem tailTrace_3703302 : CollatzResearch.WordTrace tailWord_3703302 prefixEnd_3703302 1901573934756775047593831 := by
  unfold tailWord_3703302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220953763424275077278505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90047013619717868315274773 4220953763424275077278505)
  ·
    refine ⟨3165715322568206307958879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4220953763424275077278505 3165715322568206307958879)
    ·
      refine ⟨4748572983852309461938319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165715322568206307958879 4748572983852309461938319)
      ·
        refine ⟨7122859475778464192907479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4748572983852309461938319 7122859475778464192907479)
        ·
          refine ⟨10684289213667696289361219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7122859475778464192907479 10684289213667696289361219)
          ·
            refine ⟨16026433820501544434041829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10684289213667696289361219 16026433820501544434041829)
            ·
              refine ⟨3004956341344039581382843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16026433820501544434041829 3004956341344039581382843)
              ·
                refine ⟨4507434512016059372074265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004956341344039581382843 4507434512016059372074265)
                ·
                  refine ⟨3380575884012044529055699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4507434512016059372074265 3380575884012044529055699)
                  ·
                    refine ⟨5070863826018066793583549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3380575884012044529055699 5070863826018066793583549)
                    ·
                      refine ⟨1901573934756775047593831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5070863826018066793583549 1901573934756775047593831)
                      ·
                        rfl

theorem cell23_3703302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_3703302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703302 prefixEnd_3703302 := by exact prefixLift 3703302
  have htrace : WordTrace (prefixWord ++ tailWord_3703302) baseStart_3703302 baseEnd_3703302 := by
    simpa [prefixWord, tailWord_3703302, baseEnd_3703302] using wordTrace_append hprefix tailTrace_3703302
  have hstable : (prefixWord ++ tailWord_3703302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703302).length < 2 ^ (prefixWord ++ tailWord_3703302).sum := by decide
  have hdescent : baseEnd_3703302 < baseStart_3703302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703308 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 2, 2, 2]
def baseStart_3703308 : Nat := 118140960795 + 3703308 * 2 ^ 59
def prefixEnd_3703308 : Nat := 4983230072969 + 3 ^ 40 * 3703308 * 2
def baseEnd_3703308 : Nat := 1901577015640702024118803

theorem tailTrace_3703308 : CollatzResearch.WordTrace tailWord_3703308 prefixEnd_3703308 1901577015640702024118803 := by
  unfold tailWord_3703308
  simp only [CollatzResearch.WordTrace]
  refine ⟨67535369633777532748815289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90047159511703376998420385 67535369633777532748815289)
  ·
    refine ⟨50651527225333149561611467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67535369633777532748815289 50651527225333149561611467)
    ·
      refine ⟨75977290837999724342417201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50651527225333149561611467 75977290837999724342417201)
      ·
        refine ⟨56982968128499793256812901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75977290837999724342417201 56982968128499793256812901)
        ·
          refine ⟨10684306524093711235652419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56982968128499793256812901 10684306524093711235652419)
          ·
            refine ⟨16026459786140566853478629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10684306524093711235652419 16026459786140566853478629)
            ·
              refine ⟨3004961209901356285027243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16026459786140566853478629 3004961209901356285027243)
              ·
                refine ⟨4507441814852034427540865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004961209901356285027243 4507441814852034427540865)
                ·
                  refine ⟨3380581361139025820655649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4507441814852034427540865 3380581361139025820655649)
                  ·
                    refine ⟨2535436020854269365491737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3380581361139025820655649 2535436020854269365491737)
                    ·
                      refine ⟨1901577015640702024118803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535436020854269365491737 1901577015640702024118803)
                      ·
                        rfl

theorem cell23_3703308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_3703308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703308 prefixEnd_3703308 := by exact prefixLift 3703308
  have htrace : WordTrace (prefixWord ++ tailWord_3703308) baseStart_3703308 baseEnd_3703308 := by
    simpa [prefixWord, tailWord_3703308, baseEnd_3703308] using wordTrace_append hprefix tailTrace_3703308
  have hstable : (prefixWord ++ tailWord_3703308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703308).length < 2 ^ (prefixWord ++ tailWord_3703308).sum := by decide
  have hdescent : baseEnd_3703308 < baseStart_3703308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703347 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 4]
def baseStart_3703347 : Nat := 118140960795 + 3703347 * 2 ^ 59
def prefixEnd_3703347 : Nat := 4983230072969 + 3 ^ 40 * 3703347 * 2
def baseEnd_3703347 : Nat := 1901597041386227371531123

theorem tailTrace_3703347 : CollatzResearch.WordTrace tailWord_3703347 prefixEnd_3703347 1901597041386227371531123 := by
  unfold tailWord_3703347
  simp only [CollatzResearch.WordTrace]
  refine ⟨135072161714413775158300295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90048107809609183438866863 135072161714413775158300295)
  ·
    refine ⟨202608242571620662737450443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135072161714413775158300295 202608242571620662737450443)
    ·
      refine ⟨303912363857430994106175665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202608242571620662737450443 303912363857430994106175665)
      ·
        refine ⟨227934272893073245579631749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303912363857430994106175665 227934272893073245579631749)
        ·
          refine ⟨42737676167451233546180953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227934272893073245579631749 42737676167451233546180953)
          ·
            refine ⟨32053257125588425159635715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42737676167451233546180953 32053257125588425159635715)
            ·
              refine ⟨48079885688382637739453573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32053257125588425159635715 48079885688382637739453573)
              ·
                refine ⟨9014978566571744576147545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48079885688382637739453573 9014978566571744576147545)
                ·
                  refine ⟨6761233924928808432110659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9014978566571744576147545 6761233924928808432110659)
                  ·
                    refine ⟨10141850887393212648165989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6761233924928808432110659 10141850887393212648165989)
                    ·
                      refine ⟨1901597041386227371531123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10141850887393212648165989 1901597041386227371531123)
                      ·
                        rfl

theorem cell23_3703347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_3703347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703347 prefixEnd_3703347 := by exact prefixLift 3703347
  have htrace : WordTrace (prefixWord ++ tailWord_3703347) baseStart_3703347 baseEnd_3703347 := by
    simpa [prefixWord, tailWord_3703347, baseEnd_3703347] using wordTrace_append hprefix tailTrace_3703347
  have hstable : (prefixWord ++ tailWord_3703347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703347).length < 2 ^ (prefixWord ++ tailWord_3703347).sum := by decide
  have hdescent : baseEnd_3703347 < baseStart_3703347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703348 : List Nat := [2, 5, 1, 3, 1, 1, 1, 4, 5]
def baseStart_3703348 : Nat := 118140960795 + 3703348 * 2 ^ 59
def prefixEnd_3703348 : Nat := 4983230072969 + 3 ^ 40 * 3703348 * 2
def baseEnd_3703348 : Nat := 211288617207431318624291

theorem tailTrace_3703348 : CollatzResearch.WordTrace tailWord_3703348 prefixEnd_3703348 211288617207431318624291 := by
  unfold tailWord_3703348
  simp only [CollatzResearch.WordTrace]
  refine ⟨67536099093705076164543349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90048132124940101552724465 67536099093705076164543349)
  ·
    refine ⟨6331509290034850890425939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67536099093705076164543349 6331509290034850890425939)
    ·
      refine ⟨9497263935052276335638909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6331509290034850890425939 9497263935052276335638909)
      ·
        refine ⟨3561473975644603625864591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9497263935052276335638909 3561473975644603625864591)
        ·
          refine ⟨5342210963466905438796887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561473975644603625864591 5342210963466905438796887)
          ·
            refine ⟨8013316445200358158195331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342210963466905438796887 8013316445200358158195331)
            ·
              refine ⟨12019974667800537237292997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8013316445200358158195331 12019974667800537237292997)
              ·
                refine ⟨2253745250212600731992437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12019974667800537237292997 2253745250212600731992437)
                ·
                  refine ⟨211288617207431318624291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2253745250212600731992437 211288617207431318624291)
                  ·
                    rfl

theorem cell23_3703348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_3703348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703348 prefixEnd_3703348 := by exact prefixLift 3703348
  have htrace : WordTrace (prefixWord ++ tailWord_3703348) baseStart_3703348 baseEnd_3703348 := by
    simpa [prefixWord, tailWord_3703348, baseEnd_3703348] using wordTrace_append hprefix tailTrace_3703348
  have hstable : (prefixWord ++ tailWord_3703348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703348).length < 2 ^ (prefixWord ++ tailWord_3703348).sum := by decide
  have hdescent : baseEnd_3703348 < baseStart_3703348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703384 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 2, 2, 3]
def baseStart_3703384 : Nat := 118140960795 + 3703384 * 2 ^ 59
def prefixEnd_3703384 : Nat := 4983230072969 + 3 ^ 40 * 3703384 * 2
def baseEnd_3703384 : Nat := 1901616040170443726768453

theorem tailTrace_3703384 : CollatzResearch.WordTrace tailWord_3703384 prefixEnd_3703384 1901616040170443726768453 := by
  unfold tailWord_3703384
  simp only [CollatzResearch.WordTrace]
  refine ⟨67536755607639865238698603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90049007476853153651598137 67536755607639865238698603)
  ·
    refine ⟨101305133411459797858047905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67536755607639865238698603 101305133411459797858047905)
    ·
      refine ⟨75978850058594848393535929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101305133411459797858047905 75978850058594848393535929)
      ·
        refine ⟨56984137543946136295151947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75978850058594848393535929 56984137543946136295151947)
        ·
          refine ⟨85476206315919204442727921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56984137543946136295151947 85476206315919204442727921)
          ·
            refine ⟨64107154736939403332045941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85476206315919204442727921 64107154736939403332045941)
            ·
              refine ⟨6010045756588069062379307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64107154736939403332045941 6010045756588069062379307)
              ·
                refine ⟨9015068634882103593568961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6010045756588069062379307 9015068634882103593568961)
                ·
                  refine ⟨6761301476161577695176721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9015068634882103593568961 6761301476161577695176721)
                  ·
                    refine ⟨5070976107121183271382541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6761301476161577695176721 5070976107121183271382541)
                    ·
                      refine ⟨1901616040170443726768453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5070976107121183271382541 1901616040170443726768453)
                      ·
                        rfl

theorem cell23_3703384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_3703384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703384 prefixEnd_3703384 := by exact prefixLift 3703384
  have htrace : WordTrace (prefixWord ++ tailWord_3703384) baseStart_3703384 baseEnd_3703384 := by
    simpa [prefixWord, tailWord_3703384, baseEnd_3703384] using wordTrace_append hprefix tailTrace_3703384
  have hstable : (prefixWord ++ tailWord_3703384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703384).length < 2 ^ (prefixWord ++ tailWord_3703384).sum := by decide
  have hdescent : baseEnd_3703384 < baseStart_3703384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703421 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 6]
def baseStart_3703421 : Nat := 118140960795 + 3703421 * 2 ^ 59
def prefixEnd_3703421 : Nat := 4983230072969 + 3 ^ 40 * 3703421 * 2
def baseEnd_3703421 : Nat := 211292782106073342445087

theorem tailTrace_3703421 : CollatzResearch.WordTrace tailWord_3703421 prefixEnd_3703421 211292782106073342445087 := by
  unfold tailWord_3703421
  simp only [CollatzResearch.WordTrace]
  refine ⟨135074860716145685796494117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90049907144097123864329411 135074860716145685796494117)
  ·
    refine ⟨25326536384277316086842647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135074860716145685796494117 25326536384277316086842647)
    ·
      refine ⟨37989804576415974130263971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25326536384277316086842647 37989804576415974130263971)
      ·
        refine ⟨56984706864623961195395957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37989804576415974130263971 56984706864623961195395957)
        ·
          refine ⟨5342316268558496362068371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56984706864623961195395957 5342316268558496362068371)
          ·
            refine ⟨8013474402837744543102557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342316268558496362068371 8013474402837744543102557)
            ·
              refine ⟨3005052901064154203663459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8013474402837744543102557 3005052901064154203663459)
              ·
                refine ⟨4507579351596231305495189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005052901064154203663459 4507579351596231305495189)
                ·
                  refine ⟨211292782106073342445087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4507579351596231305495189 211292782106073342445087)
                  ·
                    rfl

theorem cell23_3703421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_3703421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703421 prefixEnd_3703421 := by exact prefixLift 3703421
  have htrace : WordTrace (prefixWord ++ tailWord_3703421) baseStart_3703421 baseEnd_3703421 := by
    simpa [prefixWord, tailWord_3703421, baseEnd_3703421] using wordTrace_append hprefix tailTrace_3703421
  have hstable : (prefixWord ++ tailWord_3703421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703421).length < 2 ^ (prefixWord ++ tailWord_3703421).sum := by decide
  have hdescent : baseEnd_3703421 < baseStart_3703421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703424 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 1, 5, 2]
def baseStart_3703424 : Nat := 118140960795 + 3703424 * 2 ^ 59
def prefixEnd_3703424 : Nat := 4983230072969 + 3 ^ 40 * 3703424 * 2
def baseEnd_3703424 : Nat := 1901636579396623570268269

theorem tailTrace_3703424 : CollatzResearch.WordTrace tailWord_3703424 prefixEnd_3703424 1901636579396623570268269 := by
  unfold tailWord_3703424
  simp only [CollatzResearch.WordTrace]
  refine ⟨67537485067567408654426663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90049980090089878205902217 67537485067567408654426663)
  ·
    refine ⟨101306227601351112981639995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67537485067567408654426663 101306227601351112981639995)
    ·
      refine ⟨151959341402026669472459993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101306227601351112981639995 151959341402026669472459993)
      ·
        refine ⟨113969506051520002104344995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151959341402026669472459993 113969506051520002104344995)
        ·
          refine ⟨170954259077280003156517493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113969506051520002104344995 170954259077280003156517493)
          ·
            refine ⟨16026961788495000295923515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170954259077280003156517493 16026961788495000295923515)
            ·
              refine ⟨24040442682742500443885273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16026961788495000295923515 24040442682742500443885273)
              ·
                refine ⟨18030332012056875332913955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24040442682742500443885273 18030332012056875332913955)
                ·
                  refine ⟨27045498018085312999370933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18030332012056875332913955 27045498018085312999370933)
                  ·
                    refine ⟨2535515439195498093691025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27045498018085312999370933 2535515439195498093691025)
                    ·
                      refine ⟨1901636579396623570268269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535515439195498093691025 1901636579396623570268269)
                      ·
                        rfl

theorem cell23_3703424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_3703424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703424 prefixEnd_3703424 := by exact prefixLift 3703424
  have htrace : WordTrace (prefixWord ++ tailWord_3703424) baseStart_3703424 baseEnd_3703424 := by
    simpa [prefixWord, tailWord_3703424, baseEnd_3703424] using wordTrace_append hprefix tailTrace_3703424
  have hstable : (prefixWord ++ tailWord_3703424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703424).length < 2 ^ (prefixWord ++ tailWord_3703424).sum := by decide
  have hdescent : baseEnd_3703424 < baseStart_3703424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703447 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 3, 6]
def baseStart_3703447 : Nat := 118140960795 + 3703447 * 2 ^ 59
def prefixEnd_3703447 : Nat := 4983230072969 + 3 ^ 40 * 3703447 * 2
def baseEnd_3703447 : Nat := 633882796483892326760221

theorem tailTrace_3703447 : CollatzResearch.WordTrace tailWord_3703447 prefixEnd_3703447 633882796483892326760221 := by
  unfold tailWord_3703447
  simp only [CollatzResearch.WordTrace]
  refine ⟨135075809014051492236940595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90050539342700994824627063 135075809014051492236940595)
  ·
    refine ⟨202613713521077238355410893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135075809014051492236940595 202613713521077238355410893)
    ·
      refine ⟨75980142570403964383279085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202613713521077238355410893 75980142570403964383279085)
      ·
        refine ⟨28492553463901486643729657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75980142570403964383279085 28492553463901486643729657)
        ·
          refine ⟨21369415097926114982797243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28492553463901486643729657 21369415097926114982797243)
          ·
            refine ⟨32054122646889172474195865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21369415097926114982797243 32054122646889172474195865)
            ·
              refine ⟨24040591985166879355646899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32054122646889172474195865 24040591985166879355646899)
              ·
                refine ⟨36060887977750319033470349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24040591985166879355646899 36060887977750319033470349)
                ·
                  refine ⟨13522832991656369637551381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36060887977750319033470349 13522832991656369637551381)
                  ·
                    refine ⟨633882796483892326760221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13522832991656369637551381 633882796483892326760221)
                    ·
                      rfl

theorem cell23_3703447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_3703447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703447 prefixEnd_3703447 := by exact prefixLift 3703447
  have htrace : WordTrace (prefixWord ++ tailWord_3703447) baseStart_3703447 baseEnd_3703447 := by
    simpa [prefixWord, tailWord_3703447, baseEnd_3703447] using wordTrace_append hprefix tailTrace_3703447
  have hstable : (prefixWord ++ tailWord_3703447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703447).length < 2 ^ (prefixWord ++ tailWord_3703447).sum := by decide
  have hdescent : baseEnd_3703447 < baseStart_3703447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703474 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_3703474 : Nat := 118140960795 + 3703474 * 2 ^ 59
def prefixEnd_3703474 : Nat := 4983230072969 + 3 ^ 40 * 3703474 * 2
def baseEnd_3703474 : Nat := 1901662253429348374643039

theorem tailTrace_3703474 : CollatzResearch.WordTrace tailWord_3703474 prefixEnd_3703474 1901662253429348374643039 := by
  unfold tailWord_3703474
  simp only [CollatzResearch.WordTrace]
  refine ⟨33769198446238418962043369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90051195856635783898782317 33769198446238418962043369)
  ·
    refine ⟨25326898834678814221532527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33769198446238418962043369 25326898834678814221532527)
    ·
      refine ⟨37990348252018221332298791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25326898834678814221532527 37990348252018221332298791)
      ·
        refine ⟨56985522378027331998448187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37990348252018221332298791 56985522378027331998448187)
        ·
          refine ⟨85478283567040997997672281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56985522378027331998448187 85478283567040997997672281)
          ·
            refine ⟨64108712675280748498254211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85478283567040997997672281 64108712675280748498254211)
            ·
              refine ⟨96163069012921122747381317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64108712675280748498254211 96163069012921122747381317)
              ·
                refine ⟨18030575439922710515133997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96163069012921122747381317 18030575439922710515133997)
                ·
                  refine ⟨6761465789971016443175249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18030575439922710515133997 6761465789971016443175249)
                  ·
                    refine ⟨5071099342478262332381437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6761465789971016443175249 5071099342478262332381437)
                    ·
                      refine ⟨1901662253429348374643039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5071099342478262332381437 1901662253429348374643039)
                      ·
                        rfl

theorem cell23_3703474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_3703474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703474 prefixEnd_3703474 := by exact prefixLift 3703474
  have htrace : WordTrace (prefixWord ++ tailWord_3703474) baseStart_3703474 baseEnd_3703474 := by
    simpa [prefixWord, tailWord_3703474, baseEnd_3703474] using wordTrace_append hprefix tailTrace_3703474
  have hstable : (prefixWord ++ tailWord_3703474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703474).length < 2 ^ (prefixWord ++ tailWord_3703474).sum := by decide
  have hdescent : baseEnd_3703474 < baseStart_3703474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703484 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3703484 : Nat := 118140960795 + 3703484 * 2 ^ 59
def prefixEnd_3703484 : Nat := 4983230072969 + 3 ^ 40 * 3703484 * 2
def baseEnd_3703484 : Nat := 1901667388235893335517993

theorem tailTrace_3703484 : CollatzResearch.WordTrace tailWord_3703484 prefixEnd_3703484 1901667388235893335517993 := by
  unfold tailWord_3703484
  simp only [CollatzResearch.WordTrace]
  refine ⟨67538579257458723778018753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90051439009944965037358337 67538579257458723778018753)
  ·
    refine ⟨50653934443094042833514065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67538579257458723778018753 50653934443094042833514065)
    ·
      refine ⟨37990450832320532125135549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50653934443094042833514065 37990450832320532125135549)
      ·
        refine ⟨14246419062120199546925831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37990450832320532125135549 14246419062120199546925831)
        ·
          refine ⟨21369628593180299320388747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14246419062120199546925831 21369628593180299320388747)
          ·
            refine ⟨32054442889770448980583121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21369628593180299320388747 32054442889770448980583121)
            ·
              refine ⟨24040832167327836735437341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32054442889770448980583121 24040832167327836735437341)
              ·
                refine ⟨9015312062747938775789003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24040832167327836735437341 9015312062747938775789003)
                ·
                  refine ⟨13522968094121908163683505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9015312062747938775789003 13522968094121908163683505)
                  ·
                    refine ⟨10142226070591431122762629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13522968094121908163683505 10142226070591431122762629)
                    ·
                      refine ⟨1901667388235893335517993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10142226070591431122762629 1901667388235893335517993)
                      ·
                        rfl

theorem cell23_3703484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3703484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703484 prefixEnd_3703484 := by exact prefixLift 3703484
  have htrace : WordTrace (prefixWord ++ tailWord_3703484) baseStart_3703484 baseEnd_3703484 := by
    simpa [prefixWord, tailWord_3703484, baseEnd_3703484] using wordTrace_append hprefix tailTrace_3703484
  have hstable : (prefixWord ++ tailWord_3703484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703484).length < 2 ^ (prefixWord ++ tailWord_3703484).sum := by decide
  have hdescent : baseEnd_3703484 < baseStart_3703484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703508 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3703508 : Nat := 118140960795 + 3703508 * 2 ^ 59
def prefixEnd_3703508 : Nat := 4983230072969 + 3 ^ 40 * 3703508 * 2
def baseEnd_3703508 : Nat := 1901679711771601241617883

theorem tailTrace_3703508 : CollatzResearch.WordTrace tailWord_3703508 prefixEnd_3703508 1901679711771601241617883 := by
  unfold tailWord_3703508
  simp only [CollatzResearch.WordTrace]
  refine ⟨67539016933415249827455589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90052022577886999769940785 67539016933415249827455589)
  ·
    refine ⟨12663565675015359342647923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67539016933415249827455589 12663565675015359342647923)
    ·
      refine ⟨18995348512523039013971885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12663565675015359342647923 18995348512523039013971885)
      ·
        refine ⟨7123255692196139630239457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18995348512523039013971885 7123255692196139630239457)
        ·
          refine ⟨5342441769147104722679593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7123255692196139630239457 5342441769147104722679593)
          ·
            refine ⟨4006831326860328542009695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5342441769147104722679593 4006831326860328542009695)
            ·
              refine ⟨6010246990290492813014543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006831326860328542009695 6010246990290492813014543)
              ·
                refine ⟨9015370485435739219521815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6010246990290492813014543 9015370485435739219521815)
                ·
                  refine ⟨13523055728153608829282723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9015370485435739219521815 13523055728153608829282723)
                  ·
                    refine ⟨20284583592230413243924085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13523055728153608829282723 20284583592230413243924085)
                    ·
                      refine ⟨1901679711771601241617883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20284583592230413243924085 1901679711771601241617883)
                      ·
                        rfl

theorem cell23_3703508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3703508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703508 prefixEnd_3703508 := by exact prefixLift 3703508
  have htrace : WordTrace (prefixWord ++ tailWord_3703508) baseStart_3703508 baseEnd_3703508 := by
    simpa [prefixWord, tailWord_3703508, baseEnd_3703508] using wordTrace_append hprefix tailTrace_3703508
  have hstable : (prefixWord ++ tailWord_3703508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703508).length < 2 ^ (prefixWord ++ tailWord_3703508).sum := by decide
  have hdescent : baseEnd_3703508 < baseStart_3703508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703538 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_3703538 : Nat := 118140960795 + 3703538 * 2 ^ 59
def prefixEnd_3703538 : Nat := 4983230072969 + 3 ^ 40 * 3703538 * 2
def baseEnd_3703538 : Nat := 1901695116191236124242745

theorem tailTrace_3703538 : CollatzResearch.WordTrace tailWord_3703538 prefixEnd_3703538 1901695116191236124242745 := by
  unfold tailWord_3703538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33769782014180453694625817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90052752037814543185668845 33769782014180453694625817)
  ·
    refine ⟨25327336510635340270969363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33769782014180453694625817 25327336510635340270969363)
    ·
      refine ⟨37991004765953010406454045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25327336510635340270969363 37991004765953010406454045)
      ·
        refine ⟨14246626787232378902420267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37991004765953010406454045 14246626787232378902420267)
        ·
          refine ⟨21369940180848568353630401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14246626787232378902420267 21369940180848568353630401)
          ·
            refine ⟨16027455135636426265222801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21369940180848568353630401 16027455135636426265222801)
            ·
              refine ⟨12020591351727319698917101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16027455135636426265222801 12020591351727319698917101)
              ·
                refine ⟨4507721756897744887093913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12020591351727319698917101 4507721756897744887093913)
                ·
                  refine ⟨3380791317673308665320435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4507721756897744887093913 3380791317673308665320435)
                  ·
                    refine ⟨5071186976509962997980653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3380791317673308665320435 5071186976509962997980653)
                    ·
                      refine ⟨1901695116191236124242745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5071186976509962997980653 1901695116191236124242745)
                      ·
                        rfl

theorem cell23_3703538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_3703538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703538 prefixEnd_3703538 := by exact prefixLift 3703538
  have htrace : WordTrace (prefixWord ++ tailWord_3703538) baseStart_3703538 baseEnd_3703538 := by
    simpa [prefixWord, tailWord_3703538, baseEnd_3703538] using wordTrace_append hprefix tailTrace_3703538
  have hstable : (prefixWord ++ tailWord_3703538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703538).length < 2 ^ (prefixWord ++ tailWord_3703538).sum := by decide
  have hdescent : baseEnd_3703538 < baseStart_3703538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703561 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 1, 4, 2]
def baseStart_3703561 : Nat := 118140960795 + 3703561 * 2 ^ 59
def prefixEnd_3703561 : Nat := 4983230072969 + 3 ^ 40 * 3703561 * 2
def baseEnd_3703561 : Nat := 1901706926246289534255139

theorem tailTrace_3703561 : CollatzResearch.WordTrace tailWord_3703561 prefixEnd_3703561 1901706926246289534255139 := by
  unfold tailWord_3703561
  simp only [CollatzResearch.WordTrace]
  refine ⟨135079966935638489706590537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90053311290425659804393691 135079966935638489706590537)
  ·
    refine ⟨101309975201728867279942903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135079966935638489706590537 101309975201728867279942903)
    ·
      refine ⟨151964962802593300919914355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101309975201728867279942903 151964962802593300919914355)
      ·
        refine ⟨227947444203889951379871533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151964962802593300919914355 227947444203889951379871533)
        ·
          refine ⟨85480291576458731767451825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227947444203889951379871533 85480291576458731767451825)
          ·
            refine ⟨64110218682344048825588869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85480291576458731767451825 64110218682344048825588869)
            ·
              refine ⟨12020666002939509154797913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64110218682344048825588869 12020666002939509154797913)
              ·
                refine ⟨9015499502204631866098435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12020666002939509154797913 9015499502204631866098435)
                ·
                  refine ⟨13523249253306947799147653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9015499502204631866098435 13523249253306947799147653)
                  ·
                    refine ⟨2535609234995052712340185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13523249253306947799147653 2535609234995052712340185)
                    ·
                      refine ⟨1901706926246289534255139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535609234995052712340185 1901706926246289534255139)
                      ·
                        rfl

theorem cell23_3703561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 4, 2].length) (baseStart_3703561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703561 prefixEnd_3703561 := by exact prefixLift 3703561
  have htrace : WordTrace (prefixWord ++ tailWord_3703561) baseStart_3703561 baseEnd_3703561 := by
    simpa [prefixWord, tailWord_3703561, baseEnd_3703561] using wordTrace_append hprefix tailTrace_3703561
  have hstable : (prefixWord ++ tailWord_3703561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703561).length < 2 ^ (prefixWord ++ tailWord_3703561).sum := by decide
  have hdescent : baseEnd_3703561 < baseStart_3703561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703567 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 9]
def baseStart_3703567 : Nat := 118140960795 + 3703567 * 2 ^ 59
def prefixEnd_3703567 : Nat := 4983230072969 + 3 ^ 40 * 3703567 * 2
def baseEnd_3703567 : Nat := 211301111903357390086679

theorem tailTrace_3703567 : CollatzResearch.WordTrace tailWord_3703567 prefixEnd_3703567 211301111903357390086679 := by
  unfold tailWord_3703567
  simp only [CollatzResearch.WordTrace]
  refine ⟨135080185773616752731308955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90053457182411168487539303 135080185773616752731308955)
  ·
    refine ⟨202620278660425129096963433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135080185773616752731308955 202620278660425129096963433)
    ·
      refine ⟨151965208995318846822722575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202620278660425129096963433 151965208995318846822722575)
      ·
        refine ⟨227947813492978270234083863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151965208995318846822722575 227947813492978270234083863)
        ·
          refine ⟨341921720239467405351125795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227947813492978270234083863 341921720239467405351125795)
          ·
            refine ⟨512882580359201108026688693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341921720239467405351125795 512882580359201108026688693)
            ·
              refine ⟨48082741908675103877502065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 512882580359201108026688693 48082741908675103877502065)
              ·
                refine ⟨36062056431506327908126549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48082741908675103877502065 36062056431506327908126549)
                ·
                  refine ⟨211301111903357390086679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36062056431506327908126549 211301111903357390086679)
                  ·
                    rfl

theorem cell23_3703567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 9].length) (baseStart_3703567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703567 prefixEnd_3703567 := by exact prefixLift 3703567
  have htrace : WordTrace (prefixWord ++ tailWord_3703567) baseStart_3703567 baseEnd_3703567 := by
    simpa [prefixWord, tailWord_3703567, baseEnd_3703567] using wordTrace_append hprefix tailTrace_3703567
  have hstable : (prefixWord ++ tailWord_3703567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703567).length < 2 ^ (prefixWord ++ tailWord_3703567).sum := by decide
  have hdescent : baseEnd_3703567 < baseStart_3703567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703577 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_3703577 : Nat := 118140960795 + 3703577 * 2 ^ 59
def prefixEnd_3703577 : Nat := 4983230072969 + 3 ^ 40 * 3703577 * 2
def baseEnd_3703577 : Nat := 1901715141936761471655065

theorem tailTrace_3703577 : CollatzResearch.WordTrace tailWord_3703577 prefixEnd_3703577 1901715141936761471655065 := by
  unfold tailWord_3703577
  simp only [CollatzResearch.WordTrace]
  refine ⟨135080550503580524439172985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90053700335720349626115323 135080550503580524439172985)
  ·
    refine ⟨101310412877685393329379739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135080550503580524439172985 101310412877685393329379739)
    ·
      refine ⟨151965619316528089994069609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101310412877685393329379739 151965619316528089994069609)
      ·
        refine ⟨113974214487396067495552207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151965619316528089994069609 113974214487396067495552207)
        ·
          refine ⟨170961321731094101243328311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113974214487396067495552207 170961321731094101243328311)
          ·
            refine ⟨256441982596641151864992467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170961321731094101243328311 256441982596641151864992467)
            ·
              refine ⟨384662973894961727797488701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256441982596641151864992467 384662973894961727797488701)
              ·
                refine ⟨144248615210610647924058263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384662973894961727797488701 144248615210610647924058263)
                ·
                  refine ⟨216372922815915971886087395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144248615210610647924058263 216372922815915971886087395)
                  ·
                    refine ⟨324559384223873957829131093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216372922815915971886087395 324559384223873957829131093)
                    ·
                      refine ⟨1901715141936761471655065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 324559384223873957829131093 1901715141936761471655065)
                      ·
                        rfl

theorem cell23_3703577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_3703577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703577 prefixEnd_3703577 := by exact prefixLift 3703577
  have htrace : WordTrace (prefixWord ++ tailWord_3703577) baseStart_3703577 baseEnd_3703577 := by
    simpa [prefixWord, tailWord_3703577, baseEnd_3703577] using wordTrace_append hprefix tailTrace_3703577
  have hstable : (prefixWord ++ tailWord_3703577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703577).length < 2 ^ (prefixWord ++ tailWord_3703577).sum := by decide
  have hdescent : baseEnd_3703577 < baseStart_3703577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703578 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2]
def baseStart_3703578 : Nat := 118140960795 + 3703578 * 2 ^ 59
def prefixEnd_3703578 : Nat := 4983230072969 + 3 ^ 40 * 3703578 * 2
def baseEnd_3703578 : Nat := 1901715655417415967742561

theorem tailTrace_3703578 : CollatzResearch.WordTrace tailWord_3703578 prefixEnd_3703578 1901715655417415967742561 := by
  unfold tailWord_3703578
  simp only [CollatzResearch.WordTrace]
  refine ⟨33770146744144225402489847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90053724651051267739972925 33770146744144225402489847)
  ·
    refine ⟨50655220116216338103734771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33770146744144225402489847 50655220116216338103734771)
    ·
      refine ⟨75982830174324507155602157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50655220116216338103734771 75982830174324507155602157)
      ·
        refine ⟨28493561315371690183350809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75982830174324507155602157 28493561315371690183350809)
        ·
          refine ⟨21370170986528767637513107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28493561315371690183350809 21370170986528767637513107)
          ·
            refine ⟨32055256479793151456269661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21370170986528767637513107 32055256479793151456269661)
            ·
              refine ⟨12020721179922431796101123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32055256479793151456269661 12020721179922431796101123)
              ·
                refine ⟨18031081769883647694151685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12020721179922431796101123 18031081769883647694151685)
                ·
                  refine ⟨3380827831853183942653441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18031081769883647694151685 3380827831853183942653441)
                  ·
                    refine ⟨2535620873889887956990081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3380827831853183942653441 2535620873889887956990081)
                    ·
                      refine ⟨1901715655417415967742561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535620873889887956990081 1901715655417415967742561)
                      ·
                        rfl

theorem cell23_3703578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_3703578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703578 prefixEnd_3703578 := by exact prefixLift 3703578
  have htrace : WordTrace (prefixWord ++ tailWord_3703578) baseStart_3703578 baseEnd_3703578 := by
    simpa [prefixWord, tailWord_3703578, baseEnd_3703578] using wordTrace_append hprefix tailTrace_3703578
  have hstable : (prefixWord ++ tailWord_3703578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703578).length < 2 ^ (prefixWord ++ tailWord_3703578).sum := by decide
  have hdescent : baseEnd_3703578 < baseStart_3703578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703584 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 7]
def baseStart_3703584 : Nat := 118140960795 + 3703584 * 2 ^ 59
def prefixEnd_3703584 : Nat := 4983230072969 + 3 ^ 40 * 3703584 * 2
def baseEnd_3703584 : Nat := 211302081811260327140837

theorem tailTrace_3703584 : CollatzResearch.WordTrace tailWord_3703584 prefixEnd_3703584 211302081811260327140837 := by
  unfold tailWord_3703584
  simp only [CollatzResearch.WordTrace]
  refine ⟨67540402907277582317338903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90053870543036776423118537 67540402907277582317338903)
  ·
    refine ⟨101310604360916373476008355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67540402907277582317338903 101310604360916373476008355)
    ·
      refine ⟨151965906541374560214012533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101310604360916373476008355 151965906541374560214012533)
      ·
        refine ⟨14246803738253865020063675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151965906541374560214012533 14246803738253865020063675)
        ·
          refine ⟨21370205607380797530095513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14246803738253865020063675 21370205607380797530095513)
          ·
            refine ⟨16027654205535598147571635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21370205607380797530095513 16027654205535598147571635)
            ·
              refine ⟨24041481308303397221357453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16027654205535598147571635 24041481308303397221357453)
              ·
                refine ⟨9015555490613773958009045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24041481308303397221357453 9015555490613773958009045)
                ·
                  refine ⟨211302081811260327140837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9015555490613773958009045 211302081811260327140837)
                  ·
                    rfl

theorem cell23_3703584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 7].length) (baseStart_3703584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703584 prefixEnd_3703584 := by exact prefixLift 3703584
  have htrace : WordTrace (prefixWord ++ tailWord_3703584) baseStart_3703584 baseEnd_3703584 := by
    simpa [prefixWord, tailWord_3703584, baseEnd_3703584] using wordTrace_append hprefix tailTrace_3703584
  have hstable : (prefixWord ++ tailWord_3703584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703584).length < 2 ^ (prefixWord ++ tailWord_3703584).sum := by decide
  have hdescent : baseEnd_3703584 < baseStart_3703584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703624 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_3703624 : Nat := 118140960795 + 3703624 * 2 ^ 59
def prefixEnd_3703624 : Nat := 4983230072969 + 3 ^ 40 * 3703624 * 2
def baseEnd_3703624 : Nat := 1901739275527522787767349

theorem tailTrace_3703624 : CollatzResearch.WordTrace tailWord_3703624 prefixEnd_3703624 1901739275527522787767349 := by
  unfold tailWord_3703624
  simp only [CollatzResearch.WordTrace]
  refine ⟨67541132367205125733066963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90054843156273500977422617 67541132367205125733066963)
  ·
    refine ⟨101311698550807688599600445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67541132367205125733066963 101311698550807688599600445)
    ·
      refine ⟨37991886956552883224850167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101311698550807688599600445 37991886956552883224850167)
      ·
        refine ⟨56987830434829324837275251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37991886956552883224850167 56987830434829324837275251)
        ·
          refine ⟨85481745652243987255912877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56987830434829324837275251 85481745652243987255912877)
          ·
            refine ⟨32055654619591495220967329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85481745652243987255912877 32055654619591495220967329)
            ·
              refine ⟨24041740964693621415725497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32055654619591495220967329 24041740964693621415725497)
              ·
                refine ⟨18031305723520216061794123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24041740964693621415725497 18031305723520216061794123)
                ·
                  refine ⟨27046958585280324092691185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18031305723520216061794123 27046958585280324092691185)
                  ·
                    refine ⟨20285218938960243069518389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27046958585280324092691185 20285218938960243069518389)
                    ·
                      refine ⟨1901739275527522787767349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20285218938960243069518389 1901739275527522787767349)
                      ·
                        rfl

theorem cell23_3703624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_3703624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703624 prefixEnd_3703624 := by exact prefixLift 3703624
  have htrace : WordTrace (prefixWord ++ tailWord_3703624) baseStart_3703624 baseEnd_3703624 := by
    simpa [prefixWord, tailWord_3703624, baseEnd_3703624] using wordTrace_append hprefix tailTrace_3703624
  have hstable : (prefixWord ++ tailWord_3703624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703624).length < 2 ^ (prefixWord ++ tailWord_3703624).sum := by decide
  have hdescent : baseEnd_3703624 < baseStart_3703624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703661 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_3703661 : Nat := 118140960795 + 3703661 * 2 ^ 59
def prefixEnd_3703661 : Nat := 4983230072969 + 3 ^ 40 * 3703661 * 2
def baseEnd_3703661 : Nat := 633919424770579714334893

theorem tailTrace_3703661 : CollatzResearch.WordTrace tailWord_3703661 prefixEnd_3703661 633919424770579714334893 := by
  unfold tailWord_3703661
  simp only [CollatzResearch.WordTrace]
  refine ⟨135083614235276206785230837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90055742823517471190153891 135083614235276206785230837)
  ·
    refine ⟨12664088834557144386115391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135083614235276206785230837 12664088834557144386115391)
    ·
      refine ⟨18996133251835716579173087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12664088834557144386115391 18996133251835716579173087)
      ·
        refine ⟨28494199877753574868759631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18996133251835716579173087 28494199877753574868759631)
        ·
          refine ⟨42741299816630362303139447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28494199877753574868759631 42741299816630362303139447)
          ·
            refine ⟨64111949724945543454709171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42741299816630362303139447 64111949724945543454709171)
            ·
              refine ⟨96167924587418315182063757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64111949724945543454709171 96167924587418315182063757)
              ·
                refine ⟨36062971720281868193273909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96167924587418315182063757 36062971720281868193273909)
                ·
                  refine ⟨3380903598776425143119429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36062971720281868193273909 3380903598776425143119429)
                  ·
                    refine ⟨633919424770579714334893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3380903598776425143119429 633919424770579714334893)
                    ·
                      rfl

theorem cell23_3703661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_3703661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703661 prefixEnd_3703661 := by exact prefixLift 3703661
  have htrace : WordTrace (prefixWord ++ tailWord_3703661) baseStart_3703661 baseEnd_3703661 := by
    simpa [prefixWord, tailWord_3703661, baseEnd_3703661] using wordTrace_append hprefix tailTrace_3703661
  have hstable : (prefixWord ++ tailWord_3703661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703661).length < 2 ^ (prefixWord ++ tailWord_3703661).sum := by decide
  have hdescent : baseEnd_3703661 < baseStart_3703661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703664 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_3703664 : Nat := 118140960795 + 3703664 * 2 ^ 59
def prefixEnd_3703664 : Nat := 4983230072969 + 3 ^ 40 * 3703664 * 2
def baseEnd_3703664 : Nat := 1901759814753702631267165

theorem tailTrace_3703664 : CollatzResearch.WordTrace tailWord_3703664 prefixEnd_3703664 1901759814753702631267165 := by
  unfold tailWord_3703664
  simp only [CollatzResearch.WordTrace]
  refine ⟨67541861827132669148795023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90055815769510225531726697 67541861827132669148795023)
  ·
    refine ⟨101312792740699003723192535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67541861827132669148795023 101312792740699003723192535)
    ·
      refine ⟨151969189111048505584788803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101312792740699003723192535 151969189111048505584788803)
      ·
        refine ⟨227953783666572758377183205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151969189111048505584788803 227953783666572758377183205)
        ·
          refine ⟨42741334437482392195721851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227953783666572758377183205 42741334437482392195721851)
          ·
            refine ⟨64112001656223588293582777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42741334437482392195721851 64112001656223588293582777)
            ·
              refine ⟨48084001242167691220187083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64112001656223588293582777 48084001242167691220187083)
              ·
                refine ⟨72126001863251536830280625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48084001242167691220187083 72126001863251536830280625)
                ·
                  refine ⟨54094501397438652622710469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72126001863251536830280625 54094501397438652622710469)
                  ·
                    refine ⟨10142719012019747366758213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54094501397438652622710469 10142719012019747366758213)
                    ·
                      refine ⟨1901759814753702631267165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10142719012019747366758213 1901759814753702631267165)
                      ·
                        rfl

theorem cell23_3703664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_3703664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703664 prefixEnd_3703664 := by exact prefixLift 3703664
  have htrace : WordTrace (prefixWord ++ tailWord_3703664) baseStart_3703664 baseEnd_3703664 := by
    simpa [prefixWord, tailWord_3703664, baseEnd_3703664] using wordTrace_append hprefix tailTrace_3703664
  have hstable : (prefixWord ++ tailWord_3703664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703664).length < 2 ^ (prefixWord ++ tailWord_3703664).sum := by decide
  have hdescent : baseEnd_3703664 < baseStart_3703664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703688 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3703688 : Nat := 118140960795 + 3703688 * 2 ^ 59
def prefixEnd_3703688 : Nat := 4983230072969 + 3 ^ 40 * 3703688 * 2
def baseEnd_3703688 : Nat := 1901772138289410537367055

theorem tailTrace_3703688 : CollatzResearch.WordTrace tailWord_3703688 prefixEnd_3703688 1901772138289410537367055 := by
  unfold tailWord_3703688
  simp only [CollatzResearch.WordTrace]
  refine ⟨67542299503089195198231859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90056399337452260264309145 67542299503089195198231859)
  ·
    refine ⟨101313449254633792797347789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67542299503089195198231859 101313449254633792797347789)
    ·
      refine ⟨37992543470487672299005421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101313449254633792797347789 37992543470487672299005421)
      ·
        refine ⟨14247203801432877112127033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37992543470487672299005421 14247203801432877112127033)
        ·
          refine ⟨10685402851074657834095275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14247203801432877112127033 10685402851074657834095275)
          ·
            refine ⟨16028104276611986751142913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10685402851074657834095275 16028104276611986751142913)
            ·
              refine ⟨12021078207458990063357185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16028104276611986751142913 12021078207458990063357185)
              ·
                refine ⟨9015808655594242547517889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12021078207458990063357185 9015808655594242547517889)
                ·
                  refine ⟨6761856491695681910638417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9015808655594242547517889 6761856491695681910638417)
                  ·
                    refine ⟨5071392368771761432978813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6761856491695681910638417 5071392368771761432978813)
                    ·
                      refine ⟨1901772138289410537367055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5071392368771761432978813 1901772138289410537367055)
                      ·
                        rfl

theorem cell23_3703688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3703688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703688 prefixEnd_3703688 := by exact prefixLift 3703688
  have htrace : WordTrace (prefixWord ++ tailWord_3703688) baseStart_3703688 baseEnd_3703688 := by
    simpa [prefixWord, tailWord_3703688, baseEnd_3703688] using wordTrace_append hprefix tailTrace_3703688
  have hstable : (prefixWord ++ tailWord_3703688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703688).length < 2 ^ (prefixWord ++ tailWord_3703688).sum := by decide
  have hdescent : baseEnd_3703688 < baseStart_3703688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703702 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3703702 : Nat := 118140960795 + 3703702 * 2 ^ 59
def prefixEnd_3703702 : Nat := 4983230072969 + 3 ^ 40 * 3703702 * 2
def baseEnd_3703702 : Nat := 1901779327018573482591991

theorem tailTrace_3703702 : CollatzResearch.WordTrace tailWord_3703702 prefixEnd_3703702 1901779327018573482591991 := by
  unfold tailWord_3703702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8442819351757979424217085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90056739752085113858315573 8442819351757979424217085)
  ·
    refine ⟨3166057256909242284081407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8442819351757979424217085 3166057256909242284081407)
    ·
      refine ⟨4749085885363863426122111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166057256909242284081407 4749085885363863426122111)
      ·
        refine ⟨7123628828045795139183167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4749085885363863426122111 7123628828045795139183167)
        ·
          refine ⟨10685443242068692708774751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7123628828045795139183167 10685443242068692708774751)
          ·
            refine ⟨16028164863103039063162127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10685443242068692708774751 16028164863103039063162127)
            ·
              refine ⟨24042247294654558594743191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16028164863103039063162127 24042247294654558594743191)
              ·
                refine ⟨36063370941981837892114787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24042247294654558594743191 36063370941981837892114787)
                ·
                  refine ⟨54095056412972756838172181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36063370941981837892114787 54095056412972756838172181)
                  ·
                    refine ⟨2535705769358097976789321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54095056412972756838172181 2535705769358097976789321)
                    ·
                      refine ⟨1901779327018573482591991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535705769358097976789321 1901779327018573482591991)
                      ·
                        rfl

theorem cell23_3703702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3703702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703702 prefixEnd_3703702 := by exact prefixLift 3703702
  have htrace : WordTrace (prefixWord ++ tailWord_3703702) baseStart_3703702 baseEnd_3703702 := by
    simpa [prefixWord, tailWord_3703702, baseEnd_3703702] using wordTrace_append hprefix tailTrace_3703702
  have hstable : (prefixWord ++ tailWord_3703702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703702).length < 2 ^ (prefixWord ++ tailWord_3703702).sum := by decide
  have hdescent : baseEnd_3703702 < baseStart_3703702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703721 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 1, 5]
def baseStart_3703721 : Nat := 118140960795 + 3703721 * 2 ^ 59
def prefixEnd_3703721 : Nat := 4983230072969 + 3 ^ 40 * 3703721 * 2
def baseEnd_3703721 : Nat := 633929694383669636084801

theorem tailTrace_3703721 : CollatzResearch.WordTrace tailWord_3703721 prefixEnd_3703721 633929694383669636084801 := by
  unfold tailWord_3703721
  simp only [CollatzResearch.WordTrace]
  refine ⟨135085802615058837032415017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90057201743372558021610011 135085802615058837032415017)
  ·
    refine ⟨101314351961294127774311263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135085802615058837032415017 101314351961294127774311263)
    ·
      refine ⟨151971527941941191661466895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101314351961294127774311263 151971527941941191661466895)
      ·
        refine ⟨227957291912911787492200343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151971527941941191661466895 227957291912911787492200343)
        ·
          refine ⟨341935937869367681238300515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227957291912911787492200343 341935937869367681238300515)
          ·
            refine ⟨512903906804051521857450773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341935937869367681238300515 512903906804051521857450773)
            ·
              refine ⟨24042370631439915087068005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 512903906804051521857450773 24042370631439915087068005)
              ·
                refine ⟨4507944493394984078825251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24042370631439915087068005 4507944493394984078825251)
                ·
                  refine ⟨6761916740092476118237877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507944493394984078825251 6761916740092476118237877)
                  ·
                    refine ⟨633929694383669636084801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6761916740092476118237877 633929694383669636084801)
                    ·
                      rfl

theorem cell23_3703721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 5].length) (baseStart_3703721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703721 prefixEnd_3703721 := by exact prefixLift 3703721
  have htrace : WordTrace (prefixWord ++ tailWord_3703721) baseStart_3703721 baseEnd_3703721 := by
    simpa [prefixWord, tailWord_3703721, baseEnd_3703721] using wordTrace_append hprefix tailTrace_3703721
  have hstable : (prefixWord ++ tailWord_3703721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703721).length < 2 ^ (prefixWord ++ tailWord_3703721).sum := by decide
  have hdescent : baseEnd_3703721 < baseStart_3703721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703735 : List Nat := [1, 1, 3, 1, 3, 1, 3, 5, 1, 1, 3]
def baseStart_3703735 : Nat := 118140960795 + 3703735 * 2 ^ 59
def prefixEnd_3703735 : Nat := 4983230072969 + 3 ^ 40 * 3703735 * 2
def baseEnd_3703735 : Nat := 1901796271880171853479339

theorem tailTrace_3703735 : CollatzResearch.WordTrace tailWord_3703735 prefixEnd_3703735 1901796271880171853479339 := by
  unfold tailWord_3703735
  simp only [CollatzResearch.WordTrace]
  refine ⟨135086313237008117423424659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90057542158005411615616439 135086313237008117423424659)
  ·
    refine ⟨202629469855512176135136989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135086313237008117423424659 202629469855512176135136989)
    ·
      refine ⟨75986051195817066050676371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202629469855512176135136989 75986051195817066050676371)
      ·
        refine ⟨113979076793725599076014557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75986051195817066050676371 113979076793725599076014557)
        ·
          refine ⟨42742153797647099653505459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113979076793725599076014557 42742153797647099653505459)
          ·
            refine ⟨64113230696470649480258189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42742153797647099653505459 64113230696470649480258189)
            ·
              refine ⟨24042461511176493555096821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64113230696470649480258189 24042461511176493555096821)
              ·
                refine ⟨2253980766672796270790327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24042461511176493555096821 2253980766672796270790327)
                ·
                  refine ⟨3380971150009194406185491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253980766672796270790327 3380971150009194406185491)
                  ·
                    refine ⟨5071456725013791609278237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3380971150009194406185491 5071456725013791609278237)
                    ·
                      refine ⟨1901796271880171853479339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5071456725013791609278237 1901796271880171853479339)
                      ·
                        rfl

theorem cell23_3703735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 1, 1, 3].length) (baseStart_3703735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703735 prefixEnd_3703735 := by exact prefixLift 3703735
  have htrace : WordTrace (prefixWord ++ tailWord_3703735) baseStart_3703735 baseEnd_3703735 := by
    simpa [prefixWord, tailWord_3703735, baseEnd_3703735] using wordTrace_append hprefix tailTrace_3703735
  have hstable : (prefixWord ++ tailWord_3703735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703735).length < 2 ^ (prefixWord ++ tailWord_3703735).sum := by decide
  have hdescent : baseEnd_3703735 < baseStart_3703735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703761 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_3703761 : Nat := 118140960795 + 3703761 * 2 ^ 59
def prefixEnd_3703761 : Nat := 4983230072969 + 3 ^ 40 * 3703761 * 2
def baseEnd_3703761 : Nat := 1901809622377188751754219

theorem tailTrace_3703761 : CollatzResearch.WordTrace tailWord_3703761 prefixEnd_3703761 1901809622377188751754219 := by
  unfold tailWord_3703761
  simp only [CollatzResearch.WordTrace]
  refine ⟨135087261534913923863871137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90058174356609282575914091 135087261534913923863871137)
  ·
    refine ⟨101315446151185442897903353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135087261534913923863871137 101315446151185442897903353)
    ·
      refine ⟨75986584613389082173427515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101315446151185442897903353 75986584613389082173427515)
      ·
        refine ⟨113979876920083623260141273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75986584613389082173427515 113979876920083623260141273)
        ·
          refine ⟨85484907690062717445105955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113979876920083623260141273 85484907690062717445105955)
          ·
            refine ⟨128227361535094076167658933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85484907690062717445105955 128227361535094076167658933)
            ·
              refine ⟨12021315143915069640718025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128227361535094076167658933 12021315143915069640718025)
              ·
                refine ⟨9015986357936302230538519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12021315143915069640718025 9015986357936302230538519)
                ·
                  refine ⟨13523979536904453345807779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9015986357936302230538519 13523979536904453345807779)
                  ·
                    refine ⟨20285969305356680018711669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13523979536904453345807779 20285969305356680018711669)
                    ·
                      refine ⟨1901809622377188751754219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20285969305356680018711669 1901809622377188751754219)
                      ·
                        rfl

theorem cell23_3703761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_3703761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703761 prefixEnd_3703761 := by exact prefixLift 3703761
  have htrace : WordTrace (prefixWord ++ tailWord_3703761) baseStart_3703761 baseEnd_3703761 := by
    simpa [prefixWord, tailWord_3703761, baseEnd_3703761] using wordTrace_append hprefix tailTrace_3703761
  have hstable : (prefixWord ++ tailWord_3703761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703761).length < 2 ^ (prefixWord ++ tailWord_3703761).sum := by decide
  have hdescent : baseEnd_3703761 < baseStart_3703761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703768 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 1, 6]
def baseStart_3703768 : Nat := 118140960795 + 3703768 * 2 ^ 59
def prefixEnd_3703768 : Nat := 4983230072969 + 3 ^ 40 * 3703768 * 2
def baseEnd_3703768 : Nat := 633937738913923408122229

theorem tailTrace_3703768 : CollatzResearch.WordTrace tailWord_3703768 prefixEnd_3703768 633937738913923408122229 := by
  unfold tailWord_3703768
  simp only [CollatzResearch.WordTrace]
  refine ⟨67543758422944282029687979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90058344563925709372917305 67543758422944282029687979)
  ·
    refine ⟨101315637634416423044531969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67543758422944282029687979 101315637634416423044531969)
    ·
      refine ⟨75986728225812317283398977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101315637634416423044531969 75986728225812317283398977)
      ·
        refine ⟨56990046169359237962549233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75986728225812317283398977 56990046169359237962549233)
        ·
          refine ⟨42742534627019428471911925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56990046169359237962549233 42742534627019428471911925)
          ·
            refine ⟨4007112621283071419241743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42742534627019428471911925 4007112621283071419241743)
            ·
              refine ⟨6010668931924607128862615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4007112621283071419241743 6010668931924607128862615)
              ·
                refine ⟨9016003397886910693293923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6010668931924607128862615 9016003397886910693293923)
                ·
                  refine ⟨13524005096830366039940885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9016003397886910693293923 13524005096830366039940885)
                  ·
                    refine ⟨633937738913923408122229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13524005096830366039940885 633937738913923408122229)
                    ·
                      rfl

theorem cell23_3703768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_3703768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703768 prefixEnd_3703768 := by exact prefixLift 3703768
  have htrace : WordTrace (prefixWord ++ tailWord_3703768) baseStart_3703768 baseEnd_3703768 := by
    simpa [prefixWord, tailWord_3703768, baseEnd_3703768] using wordTrace_append hprefix tailTrace_3703768
  have hstable : (prefixWord ++ tailWord_3703768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703768).length < 2 ^ (prefixWord ++ tailWord_3703768).sum := by decide
  have hdescent : baseEnd_3703768 < baseStart_3703768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703775 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 4]
def baseStart_3703775 : Nat := 118140960795 + 3703775 * 2 ^ 59
def prefixEnd_3703775 : Nat := 4983230072969 + 3 ^ 40 * 3703775 * 2
def baseEnd_3703775 : Nat := 1901816811106351696979155

theorem tailTrace_3703775 : CollatzResearch.WordTrace tailWord_3703775 prefixEnd_3703775 1901816811106351696979155 := by
  unfold tailWord_3703775
  simp only [CollatzResearch.WordTrace]
  refine ⟨135087772156863204254880779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90058514771242136169920519 135087772156863204254880779)
  ·
    refine ⟨202631658235294806382321169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135087772156863204254880779 202631658235294806382321169)
    ·
      refine ⟨151973743676471104786740877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202631658235294806382321169 151973743676471104786740877)
      ·
        refine ⟨56990153878676664295027829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151973743676471104786740877 56990153878676664295027829)
        ·
          refine ⟨5342826926125937277658859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56990153878676664295027829 5342826926125937277658859)
          ·
            refine ⟨8014240389188905916488289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342826926125937277658859 8014240389188905916488289)
            ·
              refine ⟨6010680291891679437366217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8014240389188905916488289 6010680291891679437366217)
              ·
                refine ⟨4508010218918759578024663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6010680291891679437366217 4508010218918759578024663)
                ·
                  refine ⟨6762015328378139367036995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508010218918759578024663 6762015328378139367036995)
                  ·
                    refine ⟨10143022992567209050555493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6762015328378139367036995 10143022992567209050555493)
                    ·
                      refine ⟨1901816811106351696979155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10143022992567209050555493 1901816811106351696979155)
                      ·
                        rfl

theorem cell23_3703775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_3703775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703775 prefixEnd_3703775 := by exact prefixLift 3703775
  have htrace : WordTrace (prefixWord ++ tailWord_3703775) baseStart_3703775 baseEnd_3703775 := by
    simpa [prefixWord, tailWord_3703775, baseEnd_3703775] using wordTrace_append hprefix tailTrace_3703775
  have hstable : (prefixWord ++ tailWord_3703775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703775).length < 2 ^ (prefixWord ++ tailWord_3703775).sum := by decide
  have hdescent : baseEnd_3703775 < baseStart_3703775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703798 : List Nat := [5, 1, 1, 1, 3, 3, 9]
def baseStart_3703798 : Nat := 118140960795 + 3703798 * 2 ^ 59
def prefixEnd_3703798 : Nat := 4983230072969 + 3 ^ 40 * 3703798 * 2
def baseEnd_3703798 : Nat := 23479365693350680333229

theorem tailTrace_3703798 : CollatzResearch.WordTrace tailWord_3703798 prefixEnd_3703798 23479365693350680333229 := by
  unfold tailWord_3703798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443038189736242448935503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90059074023853252788645365 8443038189736242448935503)
  ·
    refine ⟨12664557284604363673403255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8443038189736242448935503 12664557284604363673403255)
    ·
      refine ⟨18996835926906545510104883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12664557284604363673403255 18996835926906545510104883)
      ·
        refine ⟨28495253890359818265157325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18996835926906545510104883 28495253890359818265157325)
        ·
          refine ⟨10685720208884931849433997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28495253890359818265157325 10685720208884931849433997)
          ·
            refine ⟨4007145078331849443537749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10685720208884931849433997 4007145078331849443537749)
            ·
              refine ⟨23479365693350680333229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4007145078331849443537749 23479365693350680333229)
              ·
                rfl

theorem cell23_3703798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 9].length) (baseStart_3703798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703798 prefixEnd_3703798 := by exact prefixLift 3703798
  have htrace : WordTrace (prefixWord ++ tailWord_3703798) baseStart_3703798 baseEnd_3703798 := by
    simpa [prefixWord, tailWord_3703798, baseEnd_3703798] using wordTrace_append hprefix tailTrace_3703798
  have hstable : (prefixWord ++ tailWord_3703798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703798).length < 2 ^ (prefixWord ++ tailWord_3703798).sum := by decide
  have hdescent : baseEnd_3703798 < baseStart_3703798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703826 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3703826 : Nat := 118140960795 + 3703826 * 2 ^ 59
def prefixEnd_3703826 : Nat := 4983230072969 + 3 ^ 40 * 3703826 * 2
def baseEnd_3703826 : Nat := 1901842998619730997441421

theorem tailTrace_3703826 : CollatzResearch.WordTrace tailWord_3703826 prefixEnd_3703826 1901842998619730997441421 := by
  unfold tailWord_3703826
  simp only [CollatzResearch.WordTrace]
  refine ⟨33772408069919609991246833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90059754853118959976658221 33772408069919609991246833)
  ·
    refine ⟨25329306052439707493435125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33772408069919609991246833 25329306052439707493435125)
    ·
      refine ⟨2374622442416222577509543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25329306052439707493435125 2374622442416222577509543)
      ·
        refine ⟨3561933663624333866264315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374622442416222577509543 3561933663624333866264315)
        ·
          refine ⟨5342900495436500799396473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561933663624333866264315 5342900495436500799396473)
          ·
            refine ⟨4007175371577375599547355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5342900495436500799396473 4007175371577375599547355)
            ·
              refine ⟨6010763057366063399321033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4007175371577375599547355 6010763057366063399321033)
              ·
                refine ⟨4508072293024547549490775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6010763057366063399321033 4508072293024547549490775)
                ·
                  refine ⟨6762108439536821324236163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508072293024547549490775 6762108439536821324236163)
                  ·
                    refine ⟨10143162659305231986354245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6762108439536821324236163 10143162659305231986354245)
                    ·
                      refine ⟨1901842998619730997441421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10143162659305231986354245 1901842998619730997441421)
                      ·
                        rfl

theorem cell23_3703826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3703826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703826 prefixEnd_3703826 := by exact prefixLift 3703826
  have htrace : WordTrace (prefixWord ++ tailWord_3703826) baseStart_3703826 baseEnd_3703826 := by
    simpa [prefixWord, tailWord_3703826, baseEnd_3703826] using wordTrace_append hprefix tailTrace_3703826
  have hstable : (prefixWord ++ tailWord_3703826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703826).length < 2 ^ (prefixWord ++ tailWord_3703826).sum := by decide
  have hdescent : baseEnd_3703826 < baseStart_3703826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703851 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 5]
def baseStart_3703851 : Nat := 118140960795 + 3703851 * 2 ^ 59
def prefixEnd_3703851 : Nat := 4983230072969 + 3 ^ 40 * 3703851 * 2
def baseEnd_3703851 : Nat := 1901855835636093399628805

theorem tailTrace_3703851 : CollatzResearch.WordTrace tailWord_3703851 prefixEnd_3703851 1901855835636093399628805 := by
  unfold tailWord_3703851
  simp only [CollatzResearch.WordTrace]
  refine ⟨135090544104587869234647407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90060362736391912823098271 135090544104587869234647407)
  ·
    refine ⟨202635816156881803851971111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135090544104587869234647407 202635816156881803851971111)
    ·
      refine ⟨303953724235322705777956667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202635816156881803851971111 303953724235322705777956667)
      ·
        refine ⟨455930586352984058666935001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303953724235322705777956667 455930586352984058666935001)
        ·
          refine ⟨341947939764738044000201251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455930586352984058666935001 341947939764738044000201251)
          ·
            refine ⟨512921909647107066000301877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341947939764738044000201251 512921909647107066000301877)
            ·
              refine ⟨48086429029416287437528301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 512921909647107066000301877 48086429029416287437528301)
              ·
                refine ⟨18032410886031107789073113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48086429029416287437528301 18032410886031107789073113)
                ·
                  refine ⟨13524308164523330841804835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18032410886031107789073113 13524308164523330841804835)
                  ·
                    refine ⟨20286462246784996262707253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13524308164523330841804835 20286462246784996262707253)
                    ·
                      refine ⟨1901855835636093399628805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20286462246784996262707253 1901855835636093399628805)
                      ·
                        rfl

theorem cell23_3703851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 5].length) (baseStart_3703851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703851 prefixEnd_3703851 := by exact prefixLift 3703851
  have htrace : WordTrace (prefixWord ++ tailWord_3703851) baseStart_3703851 baseEnd_3703851 := by
    simpa [prefixWord, tailWord_3703851, baseEnd_3703851] using wordTrace_append hprefix tailTrace_3703851
  have hstable : (prefixWord ++ tailWord_3703851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703851).length < 2 ^ (prefixWord ++ tailWord_3703851).sum := by decide
  have hdescent : baseEnd_3703851 < baseStart_3703851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703852 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 1, 3, 2]
def baseStart_3703852 : Nat := 118140960795 + 3703852 * 2 ^ 59
def prefixEnd_3703852 : Nat := 4983230072969 + 3 ^ 40 * 3703852 * 2
def baseEnd_3703852 : Nat := 1901856349116747895716301

theorem tailTrace_3703852 : CollatzResearch.WordTrace tailWord_3703852 prefixEnd_3703852 1901856349116747895716301 := by
  unfold tailWord_3703852
  simp only [CollatzResearch.WordTrace]
  refine ⟨67545290288792123202716905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90060387051722830936955873 67545290288792123202716905)
  ·
    refine ⟨50658967716594092402037679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67545290288792123202716905 50658967716594092402037679)
    ·
      refine ⟨75988451574891138603056519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50658967716594092402037679 75988451574891138603056519)
      ·
        refine ⟨113982677362336707904584779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75988451574891138603056519 113982677362336707904584779)
        ·
          refine ⟨170974016043505061856877169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113982677362336707904584779 170974016043505061856877169)
          ·
            refine ⟨128230512032628796392657877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170974016043505061856877169 128230512032628796392657877)
            ·
              refine ⟨3005402625764737415452919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 128230512032628796392657877 3005402625764737415452919)
              ·
                refine ⟨4508103938647106123179379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005402625764737415452919 4508103938647106123179379)
                ·
                  refine ⟨6762155907970659184769069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508103938647106123179379 6762155907970659184769069)
                  ·
                    refine ⟨2535808465488997194288401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6762155907970659184769069 2535808465488997194288401)
                    ·
                      refine ⟨1901856349116747895716301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535808465488997194288401 1901856349116747895716301)
                      ·
                        rfl

theorem cell23_3703852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_3703852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703852 prefixEnd_3703852 := by exact prefixLift 3703852
  have htrace : WordTrace (prefixWord ++ tailWord_3703852) baseStart_3703852 baseEnd_3703852 := by
    simpa [prefixWord, tailWord_3703852, baseEnd_3703852] using wordTrace_append hprefix tailTrace_3703852
  have hstable : (prefixWord ++ tailWord_3703852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703852).length < 2 ^ (prefixWord ++ tailWord_3703852).sum := by decide
  have hdescent : baseEnd_3703852 < baseStart_3703852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703861 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3703861 : Nat := 118140960795 + 3703861 * 2 ^ 59
def prefixEnd_3703861 : Nat := 4983230072969 + 3 ^ 40 * 3703861 * 2
def baseEnd_3703861 : Nat := 1901860970442638360503759

theorem tailTrace_3703861 : CollatzResearch.WordTrace tailWord_3703861 prefixEnd_3703861 1901860970442638360503759 := by
  unfold tailWord_3703861
  simp only [CollatzResearch.WordTrace]
  refine ⟨135090908834551640942511437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90060605889701093961674291 135090908834551640942511437)
  ·
    refine ⟨50659090812956865353441789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135090908834551640942511437 50659090812956865353441789)
    ·
      refine ⟨18997159054858824507540671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50659090812956865353441789 18997159054858824507540671)
      ·
        refine ⟨28495738582288236761311007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18997159054858824507540671 28495738582288236761311007)
        ·
          refine ⟨42743607873432355141966511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28495738582288236761311007 42743607873432355141966511)
          ·
            refine ⟨64115411810148532712949767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42743607873432355141966511 64115411810148532712949767)
            ·
              refine ⟨96173117715222799069424651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64115411810148532712949767 96173117715222799069424651)
              ·
                refine ⟨144259676572834198604136977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96173117715222799069424651 144259676572834198604136977)
                ·
                  refine ⟨108194757429625648953102733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144259676572834198604136977 108194757429625648953102733)
                  ·
                    refine ⟨40573034036109618357413525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108194757429625648953102733 40573034036109618357413525)
                    ·
                      refine ⟨1901860970442638360503759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40573034036109618357413525 1901860970442638360503759)
                      ·
                        rfl

theorem cell23_3703861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3703861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703861 prefixEnd_3703861 := by exact prefixLift 3703861
  have htrace : WordTrace (prefixWord ++ tailWord_3703861) baseStart_3703861 baseEnd_3703861 := by
    simpa [prefixWord, tailWord_3703861, baseEnd_3703861] using wordTrace_append hprefix tailTrace_3703861
  have hstable : (prefixWord ++ tailWord_3703861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703861).length < 2 ^ (prefixWord ++ tailWord_3703861).sum := by decide
  have hdescent : baseEnd_3703861 < baseStart_3703861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703868 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_3703868 : Nat := 118140960795 + 3703868 * 2 ^ 59
def prefixEnd_3703868 : Nat := 4983230072969 + 3 ^ 40 * 3703868 * 2
def baseEnd_3703868 : Nat := 1901864564807219833116227

theorem tailTrace_3703868 : CollatzResearch.WordTrace tailWord_3703868 prefixEnd_3703868 1901864564807219833116227 := by
  unfold tailWord_3703868
  simp only [CollatzResearch.WordTrace]
  refine ⟨67545582072763140569008129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90060776097017520758677505 67545582072763140569008129)
  ·
    refine ⟨50659186554572355426756097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67545582072763140569008129 50659186554572355426756097)
    ·
      refine ⟨37994389915929266570067073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50659186554572355426756097 37994389915929266570067073)
      ·
        refine ⟨28495792436946949927550305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37994389915929266570067073 28495792436946949927550305)
        ·
          refine ⟨21371844327710212445662729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28495792436946949927550305 21371844327710212445662729)
          ·
            refine ⟨16028883245782659334247047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21371844327710212445662729 16028883245782659334247047)
            ·
              refine ⟨24043324868673989001370571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16028883245782659334247047 24043324868673989001370571)
              ·
                refine ⟨36064987303010983502055857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24043324868673989001370571 36064987303010983502055857)
                ·
                  refine ⟨27048740477258237626541893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36064987303010983502055857 27048740477258237626541893)
                  ·
                    refine ⟨5071638839485919554976605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27048740477258237626541893 5071638839485919554976605)
                    ·
                      refine ⟨1901864564807219833116227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5071638839485919554976605 1901864564807219833116227)
                      ·
                        rfl

theorem cell23_3703868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_3703868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703868 prefixEnd_3703868 := by exact prefixLift 3703868
  have htrace : WordTrace (prefixWord ++ tailWord_3703868) baseStart_3703868 baseEnd_3703868 := by
    simpa [prefixWord, tailWord_3703868, baseEnd_3703868] using wordTrace_append hprefix tailTrace_3703868
  have hstable : (prefixWord ++ tailWord_3703868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703868).length < 2 ^ (prefixWord ++ tailWord_3703868).sum := by decide
  have hdescent : baseEnd_3703868 < baseStart_3703868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703871 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 7]
def baseStart_3703871 : Nat := 118140960795 + 3703871 * 2 ^ 59
def prefixEnd_3703871 : Nat := 4983230072969 + 3 ^ 40 * 3703871 * 2
def baseEnd_3703871 : Nat := 211318456138798146819857

theorem tailTrace_3703871 : CollatzResearch.WordTrace tailWord_3703871 prefixEnd_3703871 211318456138798146819857 := by
  unfold tailWord_3703871
  simp only [CollatzResearch.WordTrace]
  refine ⟨135091273564515412650375467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90060849043010275100250311 135091273564515412650375467)
  ·
    refine ⟨202636910346773118975563201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135091273564515412650375467 202636910346773118975563201)
    ·
      refine ⟨151977682760079839231672401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202636910346773118975563201 151977682760079839231672401)
      ·
        refine ⟨113983262070059879423754301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151977682760079839231672401 113983262070059879423754301)
        ·
          refine ⟨42743723276272454783907863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113983262070059879423754301 42743723276272454783907863)
          ·
            refine ⟨64115584914408682175861795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42743723276272454783907863 64115584914408682175861795)
            ·
              refine ⟨96173377371613023263792693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64115584914408682175861795 96173377371613023263792693)
              ·
                refine ⟨9016254128588720930980565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96173377371613023263792693 9016254128588720930980565)
                ·
                  refine ⟨211318456138798146819857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9016254128588720930980565 211318456138798146819857)
                  ·
                    rfl

theorem cell23_3703871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 7].length) (baseStart_3703871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703871 prefixEnd_3703871 := by exact prefixLift 3703871
  have htrace : WordTrace (prefixWord ++ tailWord_3703871) baseStart_3703871 baseEnd_3703871 := by
    simpa [prefixWord, tailWord_3703871, baseEnd_3703871] using wordTrace_append hprefix tailTrace_3703871
  have hstable : (prefixWord ++ tailWord_3703871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703871).length < 2 ^ (prefixWord ++ tailWord_3703871).sum := by decide
  have hdescent : baseEnd_3703871 < baseStart_3703871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703882 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2]
def baseStart_3703882 : Nat := 118140960795 + 3703882 * 2 ^ 59
def prefixEnd_3703882 : Nat := 4983230072969 + 3 ^ 40 * 3703882 * 2
def baseEnd_3703882 : Nat := 1901871753536382778341163

theorem tailTrace_3703882 : CollatzResearch.WordTrace tailWord_3703882 prefixEnd_3703882 1901871753536382778341163 := by
  unfold tailWord_3703882
  simp only [CollatzResearch.WordTrace]
  refine ⟨33772918691868890382256475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90061116511650374352683933 33772918691868890382256475)
  ·
    refine ⟨50659378037803335573384713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33772918691868890382256475 50659378037803335573384713)
    ·
      refine ⟨37994533528352501680038535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50659378037803335573384713 37994533528352501680038535)
      ·
        refine ⟨56991800292528752520057803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37994533528352501680038535 56991800292528752520057803)
        ·
          refine ⟨85487700438793128780086705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56991800292528752520057803 85487700438793128780086705)
          ·
            refine ⟨64115775329094846585065029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85487700438793128780086705 64115775329094846585065029)
            ·
              refine ⟨12021707874205283734699693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64115775329094846585065029 12021707874205283734699693)
              ·
                refine ⟨4508140452826981400512385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12021707874205283734699693 4508140452826981400512385)
                ·
                  refine ⟨3381105339620236050384289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4508140452826981400512385 3381105339620236050384289)
                  ·
                    refine ⟨2535829004715177037788217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3381105339620236050384289 2535829004715177037788217)
                    ·
                      refine ⟨1901871753536382778341163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535829004715177037788217 1901871753536382778341163)
                      ·
                        rfl

theorem cell23_3703882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_3703882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3703882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3703882 prefixEnd_3703882 := by exact prefixLift 3703882
  have htrace : WordTrace (prefixWord ++ tailWord_3703882) baseStart_3703882 baseEnd_3703882 := by
    simpa [prefixWord, tailWord_3703882, baseEnd_3703882] using wordTrace_append hprefix tailTrace_3703882
  have hstable : (prefixWord ++ tailWord_3703882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703882).length < 2 ^ (prefixWord ++ tailWord_3703882).sum := by decide
  have hdescent : baseEnd_3703882 < baseStart_3703882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704005 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 5, 1, 3]
def baseStart_3704005 : Nat := 118140960795 + 3704005 * 2 ^ 59
def prefixEnd_3704005 : Nat := 4983230072969 + 3 ^ 40 * 3704005 * 2
def baseEnd_3704005 : Nat := 1901934911656885797103097

theorem tailTrace_3704005 : CollatzResearch.WordTrace tailWord_3704005 prefixEnd_3704005 1901934911656885797103097 := by
  unfold tailWord_3704005
  simp only [CollatzResearch.WordTrace]
  refine ⟨135096160946029953535753469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90064107297353302357168979 135096160946029953535753469)
  ·
    refine ⟨50661060354761232575907551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135096160946029953535753469 50661060354761232575907551)
    ·
      refine ⟨75991590532141848863861327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50661060354761232575907551 75991590532141848863861327)
      ·
        refine ⟨113987385798212773295791991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75991590532141848863861327 113987385798212773295791991)
        ·
          refine ⟨170981078697319159943687987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113987385798212773295791991 170981078697319159943687987)
          ·
            refine ⟨256471618045978739915531981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170981078697319159943687987 256471618045978739915531981)
            ·
              refine ⟨96176856767242027468324493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256471618045978739915531981 96176856767242027468324493)
              ·
                refine ⟨36066321287715760300621685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96176856767242027468324493 36066321287715760300621685)
                ·
                  refine ⟨3381217620723352528183283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36066321287715760300621685 3381217620723352528183283)
                  ·
                    refine ⟨5071826431085028792274925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3381217620723352528183283 5071826431085028792274925)
                    ·
                      refine ⟨1901934911656885797103097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5071826431085028792274925 1901934911656885797103097)
                      ·
                        rfl

theorem cell23_3704005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_3704005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704005 prefixEnd_3704005 := by exact prefixLift 3704005
  have htrace : WordTrace (prefixWord ++ tailWord_3704005) baseStart_3704005 baseEnd_3704005 := by
    simpa [prefixWord, tailWord_3704005, baseEnd_3704005] using wordTrace_append hprefix tailTrace_3704005
  have hstable : (prefixWord ++ tailWord_3704005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704005).length < 2 ^ (prefixWord ++ tailWord_3704005).sum := by decide
  have hdescent : baseEnd_3704005 < baseStart_3704005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704032 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 2, 3, 2]
def baseStart_3704032 : Nat := 118140960795 + 3704032 * 2 ^ 59
def prefixEnd_3704032 : Nat := 4983230072969 + 3 ^ 40 * 3704032 * 2
def baseEnd_3704032 : Nat := 1901948775634557191465473

theorem tailTrace_3704032 : CollatzResearch.WordTrace tailWord_3704032 prefixEnd_3704032 1901948775634557191465473 := by
  unfold tailWord_3704032
  simp only [CollatzResearch.WordTrace]
  refine ⟨67548572858466068573493175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90064763811288091431324233 67548572858466068573493175)
  ·
    refine ⟨101322859287699102860239763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67548572858466068573493175 101322859287699102860239763)
    ·
      refine ⟨151984288931548654290359645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101322859287699102860239763 151984288931548654290359645)
      ·
        refine ⟨56994108349330745358884867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151984288931548654290359645 56994108349330745358884867)
        ·
          refine ⟨85491162523996118038327301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56994108349330745358884867 85491162523996118038327301)
          ·
            refine ⟨16029592973249272132186369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85491162523996118038327301 16029592973249272132186369)
            ·
              refine ⟨12022194729936954099139777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16029592973249272132186369 12022194729936954099139777)
              ·
                refine ⟨9016646047452715574354833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12022194729936954099139777 9016646047452715574354833)
                ·
                  refine ⟨6762484535589536680766125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9016646047452715574354833 6762484535589536680766125)
                  ·
                    refine ⟨2535931700846076255287297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6762484535589536680766125 2535931700846076255287297)
                    ·
                      refine ⟨1901948775634557191465473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535931700846076255287297 1901948775634557191465473)
                      ·
                        rfl

theorem cell23_3704032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_3704032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704032 prefixEnd_3704032 := by exact prefixLift 3704032
  have htrace : WordTrace (prefixWord ++ tailWord_3704032) baseStart_3704032 baseEnd_3704032 := by
    simpa [prefixWord, tailWord_3704032, baseEnd_3704032] using wordTrace_append hprefix tailTrace_3704032
  have hstable : (prefixWord ++ tailWord_3704032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704032).length < 2 ^ (prefixWord ++ tailWord_3704032).sum := by decide
  have hdescent : baseEnd_3704032 < baseStart_3704032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704062 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3704062 : Nat := 118140960795 + 3704062 * 2 ^ 59
def prefixEnd_3704062 : Nat := 4983230072969 + 3 ^ 40 * 3704062 * 2
def baseEnd_3704062 : Nat := 1901964180054192074090335

theorem tailTrace_3704062 : CollatzResearch.WordTrace tailWord_3704062 prefixEnd_3704062 1901964180054192074090335 := by
  unfold tailWord_3704062
  simp only [CollatzResearch.WordTrace]
  refine ⟨16887279988352931533822305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90065493271215634847052293 16887279988352931533822305)
  ·
    refine ⟨12665459991264698650366729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16887279988352931533822305 12665459991264698650366729)
    ·
      refine ⟨9499094993448523987775047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12665459991264698650366729 9499094993448523987775047)
      ·
        refine ⟨14248642490172785981662571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9499094993448523987775047 14248642490172785981662571)
        ·
          refine ⟨21372963735259178972493857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14248642490172785981662571 21372963735259178972493857)
          ·
            refine ⟨16029722801444384229370393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21372963735259178972493857 16029722801444384229370393)
            ·
              refine ⟨12022292101083288172027795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16029722801444384229370393 12022292101083288172027795)
              ·
                refine ⟨18033438151624932258041693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12022292101083288172027795 18033438151624932258041693)
                ·
                  refine ⟨6762539306859349596765635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18033438151624932258041693 6762539306859349596765635)
                  ·
                    refine ⟨10143808960289024395148453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6762539306859349596765635 10143808960289024395148453)
                    ·
                      refine ⟨1901964180054192074090335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10143808960289024395148453 1901964180054192074090335)
                      ·
                        rfl

theorem cell23_3704062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3704062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704062 prefixEnd_3704062 := by exact prefixLift 3704062
  have htrace : WordTrace (prefixWord ++ tailWord_3704062) baseStart_3704062 baseEnd_3704062 := by
    simpa [prefixWord, tailWord_3704062, baseEnd_3704062] using wordTrace_append hprefix tailTrace_3704062
  have hstable : (prefixWord ++ tailWord_3704062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704062).length < 2 ^ (prefixWord ++ tailWord_3704062).sum := by decide
  have hdescent : baseEnd_3704062 < baseStart_3704062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704075 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 4]
def baseStart_3704075 : Nat := 118140960795 + 3704075 * 2 ^ 59
def prefixEnd_3704075 : Nat := 4983230072969 + 3 ^ 40 * 3704075 * 2
def baseEnd_3704075 : Nat := 1901970855302700523227775

theorem tailTrace_3704075 : CollatzResearch.WordTrace tailWord_3704075 prefixEnd_3704075 1901970855302700523227775 := by
  unfold tailWord_3704075
  simp only [CollatzResearch.WordTrace]
  refine ⟨135098714055776355490801679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90065809370517570327201119 135098714055776355490801679)
  ·
    refine ⟨202648071083664533236202519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135098714055776355490801679 202648071083664533236202519)
    ·
      refine ⟨303972106625496799854303779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202648071083664533236202519 303972106625496799854303779)
      ·
        refine ⟨455958159938245199781455669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303972106625496799854303779 455958159938245199781455669)
        ·
          refine ⟨42746077494210487479511469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 455958159938245199781455669 42746077494210487479511469)
          ·
            refine ⟨16029779060328932804816801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42746077494210487479511469 16029779060328932804816801)
            ·
              refine ⟨12022334295246699603612601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16029779060328932804816801 12022334295246699603612601)
              ·
                refine ⟨9016750721435024702709451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12022334295246699603612601 9016750721435024702709451)
                ·
                  refine ⟨13525126082152537054064177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9016750721435024702709451 13525126082152537054064177)
                  ·
                    refine ⟨10143844561614402790548133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13525126082152537054064177 10143844561614402790548133)
                    ·
                      refine ⟨1901970855302700523227775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10143844561614402790548133 1901970855302700523227775)
                      ·
                        rfl

theorem cell23_3704075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 4].length) (baseStart_3704075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704075 prefixEnd_3704075 := by exact prefixLift 3704075
  have htrace : WordTrace (prefixWord ++ tailWord_3704075) baseStart_3704075 baseEnd_3704075 := by
    simpa [prefixWord, tailWord_3704075, baseEnd_3704075] using wordTrace_append hprefix tailTrace_3704075
  have hstable : (prefixWord ++ tailWord_3704075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704075).length < 2 ^ (prefixWord ++ tailWord_3704075).sum := by decide
  have hdescent : baseEnd_3704075 < baseStart_3704075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704096 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 3, 2, 2]
def baseStart_3704096 : Nat := 118140960795 + 3704096 * 2 ^ 59
def prefixEnd_3704096 : Nat := 4983230072969 + 3 ^ 40 * 3704096 * 2
def baseEnd_3704096 : Nat := 1901981638396444941065179

theorem tailTrace_3704096 : CollatzResearch.WordTrace tailWord_3704096 prefixEnd_3704096 1901981638396444941065179 := by
  unfold tailWord_3704096
  simp only [CollatzResearch.WordTrace]
  refine ⟨67549739994350138038658071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90066319992466850718210761 67549739994350138038658071)
  ·
    refine ⟨101324609991525207057987107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67549739994350138038658071 101324609991525207057987107)
    ·
      refine ⟨151986914987287810586980661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101324609991525207057987107 151986914987287810586980661)
      ·
        refine ⟨14248773280058232242529437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151986914987287810586980661 14248773280058232242529437)
        ·
          refine ⟨5343289980021837090948539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14248773280058232242529437 5343289980021837090948539)
          ·
            refine ⟨8014934970032755636422809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343289980021837090948539 8014934970032755636422809)
            ·
              refine ⟨6011201227524566727317107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8014934970032755636422809 6011201227524566727317107)
              ·
                refine ⟨9016801841286850090975661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011201227524566727317107 9016801841286850090975661)
                ·
                  refine ⟨3381300690482568784115873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9016801841286850090975661 3381300690482568784115873)
                  ·
                    refine ⟨2535975517861926588086905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3381300690482568784115873 2535975517861926588086905)
                    ·
                      refine ⟨1901981638396444941065179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2535975517861926588086905 1901981638396444941065179)
                      ·
                        rfl

theorem cell23_3704096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_3704096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704096 prefixEnd_3704096 := by exact prefixLift 3704096
  have htrace : WordTrace (prefixWord ++ tailWord_3704096) baseStart_3704096 baseEnd_3704096 := by
    simpa [prefixWord, tailWord_3704096, baseEnd_3704096] using wordTrace_append hprefix tailTrace_3704096
  have hstable : (prefixWord ++ tailWord_3704096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704096).length < 2 ^ (prefixWord ++ tailWord_3704096).sum := by decide
  have hdescent : baseEnd_3704096 < baseStart_3704096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704106 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 2, 4]
def baseStart_3704106 : Nat := 118140960795 + 3704106 * 2 ^ 59
def prefixEnd_3704106 : Nat := 4983230072969 + 3 ^ 40 * 3704106 * 2
def baseEnd_3704106 : Nat := 633995591067663300646711

theorem tailTrace_3704106 : CollatzResearch.WordTrace tailWord_3704106 prefixEnd_3704106 633995591067663300646711 := by
  unfold tailWord_3704106
  simp only [CollatzResearch.WordTrace]
  refine ⟨33774961179666011946295043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90066563145776031856786781 33774961179666011946295043)
  ·
    refine ⟨50662441769499017919442565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33774961179666011946295043 50662441769499017919442565)
    ·
      refine ⟨9499207831781065859895481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50662441769499017919442565 9499207831781065859895481)
      ·
        refine ⟨7124405873835799394921611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9499207831781065859895481 7124405873835799394921611)
        ·
          refine ⟨10686608810753699092382417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7124405873835799394921611 10686608810753699092382417)
          ·
            refine ⟨8014956608065274319286813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10686608810753699092382417 8014956608065274319286813)
            ·
              refine ⟨3005608728024477869732555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8014956608065274319286813 3005608728024477869732555)
              ·
                refine ⟨4508413092036716804598833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005608728024477869732555 4508413092036716804598833)
                ·
                  refine ⟨3381309819027537603449125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4508413092036716804598833 3381309819027537603449125)
                  ·
                    refine ⟨633995591067663300646711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3381309819027537603449125 633995591067663300646711)
                    ·
                      rfl

theorem cell23_3704106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_3704106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704106 prefixEnd_3704106 := by exact prefixLift 3704106
  have htrace : WordTrace (prefixWord ++ tailWord_3704106) baseStart_3704106 baseEnd_3704106 := by
    simpa [prefixWord, tailWord_3704106, baseEnd_3704106] using wordTrace_append hprefix tailTrace_3704106
  have hstable : (prefixWord ++ tailWord_3704106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704106).length < 2 ^ (prefixWord ++ tailWord_3704106).sum := by decide
  have hdescent : baseEnd_3704106 < baseStart_3704106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704109 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3704109 : Nat := 118140960795 + 3704109 * 2 ^ 59
def prefixEnd_3704109 : Nat := 4983230072969 + 3 ^ 40 * 3704109 * 2
def baseEnd_3704109 : Nat := 1901988313644953390202619

theorem tailTrace_3704109 : CollatzResearch.WordTrace tailWord_3704109 prefixEnd_3704109 1901988313644953390202619 := by
  unfold tailWord_3704109
  simp only [CollatzResearch.WordTrace]
  refine ⟨135099954137653179297539381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90066636091768786198359587 135099954137653179297539381)
  ·
    refine ⟨12665620700404985559144317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135099954137653179297539381 12665620700404985559144317)
    ·
      refine ⟨4749607762651869584679119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12665620700404985559144317 4749607762651869584679119)
      ·
        refine ⟨7124411643977804377018679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4749607762651869584679119 7124411643977804377018679)
        ·
          refine ⟨10686617465966706565528019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7124411643977804377018679 10686617465966706565528019)
          ·
            refine ⟨16029926198950059848292029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10686617465966706565528019 16029926198950059848292029)
            ·
              refine ⟨6011222324606272443109511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16029926198950059848292029 6011222324606272443109511)
              ·
                refine ⟨9016833486909408664664267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011222324606272443109511 9016833486909408664664267)
                ·
                  refine ⟨13525250230364112996996401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9016833486909408664664267 13525250230364112996996401)
                  ·
                    refine ⟨10143937672773084747747301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13525250230364112996996401 10143937672773084747747301)
                    ·
                      refine ⟨1901988313644953390202619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10143937672773084747747301 1901988313644953390202619)
                      ·
                        rfl

theorem cell23_3704109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3704109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704109 prefixEnd_3704109 := by exact prefixLift 3704109
  have htrace : WordTrace (prefixWord ++ tailWord_3704109) baseStart_3704109 baseEnd_3704109 := by
    simpa [prefixWord, tailWord_3704109, baseEnd_3704109] using wordTrace_append hprefix tailTrace_3704109
  have hstable : (prefixWord ++ tailWord_3704109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704109).length < 2 ^ (prefixWord ++ tailWord_3704109).sum := by decide
  have hdescent : baseEnd_3704109 < baseStart_3704109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704129 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3704129 : Nat := 118140960795 + 3704129 * 2 ^ 59
def prefixEnd_3704129 : Nat := 4983230072969 + 3 ^ 40 * 3704129 * 2
def baseEnd_3704129 : Nat := 1901998583258043311952527

theorem tailTrace_3704129 : CollatzResearch.WordTrace tailWord_3704129 prefixEnd_3704129 1901998583258043311952527 := by
  unfold tailWord_3704129
  simp only [CollatzResearch.WordTrace]
  refine ⟨135100683597580722713267441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90067122398387148475511627 135100683597580722713267441)
  ·
    refine ⟨101325512698185542034950581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135100683597580722713267441 101325512698185542034950581)
    ·
      refine ⟨9499266815454894565776617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101325512698185542034950581 9499266815454894565776617)
      ·
        refine ⟨7124450111591170924332463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9499266815454894565776617 7124450111591170924332463)
        ·
          refine ⟨10686675167386756386498695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7124450111591170924332463 10686675167386756386498695)
          ·
            refine ⟨16030012751080134579748043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10686675167386756386498695 16030012751080134579748043)
            ·
              refine ⟨24045019126620201869622065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16030012751080134579748043 24045019126620201869622065)
              ·
                refine ⟨18033764344965151402216549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24045019126620201869622065 18033764344965151402216549)
                ·
                  refine ⟨3381330814680965887915603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18033764344965151402216549 3381330814680965887915603)
                  ·
                    refine ⟨5071996222021448831873405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3381330814680965887915603 5071996222021448831873405)
                    ·
                      refine ⟨1901998583258043311952527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5071996222021448831873405 1901998583258043311952527)
                      ·
                        rfl

theorem cell23_3704129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3704129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704129 prefixEnd_3704129 := by exact prefixLift 3704129
  have htrace : WordTrace (prefixWord ++ tailWord_3704129) baseStart_3704129 baseEnd_3704129 := by
    simpa [prefixWord, tailWord_3704129, baseEnd_3704129] using wordTrace_append hprefix tailTrace_3704129
  have hstable : (prefixWord ++ tailWord_3704129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704129).length < 2 ^ (prefixWord ++ tailWord_3704129).sum := by decide
  have hdescent : baseEnd_3704129 < baseStart_3704129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704157 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3704157 : Nat := 118140960795 + 3704157 * 2 ^ 59
def prefixEnd_3704157 : Nat := 4983230072969 + 3 ^ 40 * 3704157 * 2
def baseEnd_3704157 : Nat := 634004320238789734134133

theorem tailTrace_3704157 : CollatzResearch.WordTrace tailWord_3704157 prefixEnd_3704157 634004320238789734134133 := by
  unfold tailWord_3704157
  simp only [CollatzResearch.WordTrace]
  refine ⟨135101704841479283495286725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90067803227652855663524483 135101704841479283495286725)
  ·
    refine ⟨25331569657777365655366261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135101704841479283495286725 25331569657777365655366261)
    ·
      refine ⟨2374834655416628030190587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25331569657777365655366261 2374834655416628030190587)
      ·
        refine ⟨3562251983124942045285881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374834655416628030190587 3562251983124942045285881)
        ·
          refine ⟨2671688987343706533964411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3562251983124942045285881 2671688987343706533964411)
          ·
            refine ⟨4007533481015559800946617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671688987343706533964411 4007533481015559800946617)
            ·
              refine ⟨3005650110761669850709963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4007533481015559800946617 3005650110761669850709963)
              ·
                refine ⟨4508475166142504776064945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005650110761669850709963 4508475166142504776064945)
                ·
                  refine ⟨3381356374606878582048709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4508475166142504776064945 3381356374606878582048709)
                  ·
                    refine ⟨634004320238789734134133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3381356374606878582048709 634004320238789734134133)
                    ·
                      rfl

theorem cell23_3704157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3704157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704157 prefixEnd_3704157 := by exact prefixLift 3704157
  have htrace : WordTrace (prefixWord ++ tailWord_3704157) baseStart_3704157 baseEnd_3704157 := by
    simpa [prefixWord, tailWord_3704157, baseEnd_3704157] using wordTrace_append hprefix tailTrace_3704157
  have hstable : (prefixWord ++ tailWord_3704157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704157).length < 2 ^ (prefixWord ++ tailWord_3704157).sum := by decide
  have hdescent : baseEnd_3704157 < baseStart_3704157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704165 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3704165 : Nat := 118140960795 + 3704165 * 2 ^ 59
def prefixEnd_3704165 : Nat := 4983230072969 + 3 ^ 40 * 3704165 * 2
def baseEnd_3704165 : Nat := 1902017068561605171102361

theorem tailTrace_3704165 : CollatzResearch.WordTrace tailWord_3704165 prefixEnd_3704165 1902017068561605171102361 := by
  unfold tailWord_3704165
  simp only [CollatzResearch.WordTrace]
  refine ⟨135101996625450300861577949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90067997750300200574385299 135101996625450300861577949)
  ·
    refine ⟨50663248734543862823091731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135101996625450300861577949 50663248734543862823091731)
    ·
      refine ⟨75994873101815794234637597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50663248734543862823091731 75994873101815794234637597)
      ·
        refine ⟨28498077413180922837989099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75994873101815794234637597 28498077413180922837989099)
        ·
          refine ⟨42747116119771384256983649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28498077413180922837989099 42747116119771384256983649)
          ·
            refine ⟨32060337089828538192737737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42747116119771384256983649 32060337089828538192737737)
            ·
              refine ⟨24045252817371403644553303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32060337089828538192737737 24045252817371403644553303)
              ·
                refine ⟨36067879226057105466829955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24045252817371403644553303 36067879226057105466829955)
                ·
                  refine ⟨54101818839085658200244933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36067879226057105466829955 54101818839085658200244933)
                  ·
                    refine ⟨10144091032328560912545925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54101818839085658200244933 10144091032328560912545925)
                    ·
                      refine ⟨1902017068561605171102361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10144091032328560912545925 1902017068561605171102361)
                      ·
                        rfl

theorem cell23_3704165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3704165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704165 prefixEnd_3704165 := by exact prefixLift 3704165
  have htrace : WordTrace (prefixWord ++ tailWord_3704165) baseStart_3704165 baseEnd_3704165 := by
    simpa [prefixWord, tailWord_3704165, baseEnd_3704165] using wordTrace_append hprefix tailTrace_3704165
  have hstable : (prefixWord ++ tailWord_3704165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704165).length < 2 ^ (prefixWord ++ tailWord_3704165).sum := by decide
  have hdescent : baseEnd_3704165 < baseStart_3704165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704242 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_3704242 : Nat := 118140960795 + 3704242 * 2 ^ 59
def prefixEnd_3704242 : Nat := 4983230072969 + 3 ^ 40 * 3704242 * 2
def baseEnd_3704242 : Nat := 1902056606572001369839507

theorem tailTrace_3704242 : CollatzResearch.WordTrace tailWord_3704242 prefixEnd_3704242 1902056606572001369839507 := by
  unfold tailWord_3704242
  simp only [CollatzResearch.WordTrace]
  refine ⟨33776201261542835753032745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90069870030780895341420653 33776201261542835753032745)
  ·
    refine ⟨25332150946157126814774559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33776201261542835753032745 25332150946157126814774559)
    ·
      refine ⟨37998226419235690222161839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25332150946157126814774559 37998226419235690222161839)
      ·
        refine ⟨56997339628853535333242759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37998226419235690222161839 56997339628853535333242759)
        ·
          refine ⟨85496009443280302999864139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56997339628853535333242759 85496009443280302999864139)
          ·
            refine ⟨128244014164920454499796209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85496009443280302999864139 128244014164920454499796209)
            ·
              refine ⟨96183010623690340874847157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128244014164920454499796209 96183010623690340874847157)
              ·
                refine ⟨9017157245970969457016921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96183010623690340874847157 9017157245970969457016921)
                ·
                  refine ⟨6762867934478227092762691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9017157245970969457016921 6762867934478227092762691)
                  ·
                    refine ⟨10144301901717340639144037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6762867934478227092762691 10144301901717340639144037)
                    ·
                      refine ⟨1902056606572001369839507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10144301901717340639144037 1902056606572001369839507)
                      ·
                        rfl

theorem cell23_3704242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_3704242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704242 prefixEnd_3704242 := by exact prefixLift 3704242
  have htrace : WordTrace (prefixWord ++ tailWord_3704242) baseStart_3704242 baseEnd_3704242 := by
    simpa [prefixWord, tailWord_3704242, baseEnd_3704242] using wordTrace_append hprefix tailTrace_3704242
  have hstable : (prefixWord ++ tailWord_3704242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704242).length < 2 ^ (prefixWord ++ tailWord_3704242).sum := by decide
  have hdescent : baseEnd_3704242 < baseStart_3704242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704255 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_3704255 : Nat := 118140960795 + 3704255 * 2 ^ 59
def prefixEnd_3704255 : Nat := 4983230072969 + 3 ^ 40 * 3704255 * 2
def baseEnd_3704255 : Nat := 1902063281820509818976947

theorem tailTrace_3704255 : CollatzResearch.WordTrace tailWord_3704255 prefixEnd_3704255 1902063281820509818976947 := by
  unfold tailWord_3704255
  simp only [CollatzResearch.WordTrace]
  refine ⟨135105279195124246232354219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90070186130082830821569479 135105279195124246232354219)
  ·
    refine ⟨202657918792686369348531329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135105279195124246232354219 202657918792686369348531329)
    ·
      refine ⟨151993439094514777011398497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202657918792686369348531329 151993439094514777011398497)
      ·
        refine ⟨113995079320886082758548873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151993439094514777011398497 113995079320886082758548873)
        ·
          refine ⟨85496309490664562068911655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113995079320886082758548873 85496309490664562068911655)
          ·
            refine ⟨128244464235996843103367483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85496309490664562068911655 128244464235996843103367483)
            ·
              refine ⟨192366696353995264655051225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128244464235996843103367483 192366696353995264655051225)
              ·
                refine ⟨144275022265496448491288419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192366696353995264655051225 144275022265496448491288419)
                ·
                  refine ⟨216412533398244672736932629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144275022265496448491288419 216412533398244672736932629)
                  ·
                    refine ⟨10144337503042719034543717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 216412533398244672736932629 10144337503042719034543717)
                    ·
                      refine ⟨1902063281820509818976947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10144337503042719034543717 1902063281820509818976947)
                      ·
                        rfl

theorem cell23_3704255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_3704255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704255 prefixEnd_3704255 := by exact prefixLift 3704255
  have htrace : WordTrace (prefixWord ++ tailWord_3704255) baseStart_3704255 baseEnd_3704255 := by
    simpa [prefixWord, tailWord_3704255, baseEnd_3704255] using wordTrace_append hprefix tailTrace_3704255
  have hstable : (prefixWord ++ tailWord_3704255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704255).length < 2 ^ (prefixWord ++ tailWord_3704255).sum := by decide
  have hdescent : baseEnd_3704255 < baseStart_3704255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704333 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3704333 : Nat := 118140960795 + 3704333 * 2 ^ 59
def prefixEnd_3704333 : Nat := 4983230072969 + 3 ^ 40 * 3704333 * 2
def baseEnd_3704333 : Nat := 211344814812395612644621

theorem tailTrace_3704333 : CollatzResearch.WordTrace tailWord_3704333 prefixEnd_3704333 211344814812395612644621 := by
  unfold tailWord_3704333
  simp only [CollatzResearch.WordTrace]
  refine ⟨135108124088841665553693653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90072082725894443702462435 135108124088841665553693653)
  ·
    refine ⟨3166596658332226536414695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 135108124088841665553693653 3166596658332226536414695)
    ·
      refine ⟨4749894987498339804622043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166596658332226536414695 4749894987498339804622043)
      ·
        refine ⟨7124842481247509706933065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4749894987498339804622043 7124842481247509706933065)
        ·
          refine ⟨5343631860935632280199799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7124842481247509706933065 5343631860935632280199799)
          ·
            refine ⟨8015447791403448420299699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343631860935632280199799 8015447791403448420299699)
            ·
              refine ⟨12023171687105172630449549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8015447791403448420299699 12023171687105172630449549)
              ·
                refine ⟨4508689382664439736418581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12023171687105172630449549 4508689382664439736418581)
                ·
                  refine ⟨211344814812395612644621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4508689382664439736418581 211344814812395612644621)
                  ·
                    rfl

theorem cell23_3704333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3704333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704333 prefixEnd_3704333 := by exact prefixLift 3704333
  have htrace : WordTrace (prefixWord ++ tailWord_3704333) baseStart_3704333 baseEnd_3704333 := by
    simpa [prefixWord, tailWord_3704333, baseEnd_3704333] using wordTrace_append hprefix tailTrace_3704333
  have hstable : (prefixWord ++ tailWord_3704333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704333).length < 2 ^ (prefixWord ++ tailWord_3704333).sum := by decide
  have hdescent : baseEnd_3704333 < baseStart_3704333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704349 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3704349 : Nat := 118140960795 + 3704349 * 2 ^ 59
def prefixEnd_3704349 : Nat := 4983230072969 + 3 ^ 40 * 3704349 * 2
def baseEnd_3704349 : Nat := 1902111549002032451201515

theorem tailTrace_3704349 : CollatzResearch.WordTrace tailWord_3704349 prefixEnd_3704349 1902111549002032451201515 := by
  unfold tailWord_3704349
  simp only [CollatzResearch.WordTrace]
  refine ⟨135108707656783700286276101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90072471771189133524184067 135108707656783700286276101)
  ·
    refine ⟨25332882685646943803676769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135108707656783700286276101 25332882685646943803676769)
    ·
      refine ⟨18999662014235207852757577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25332882685646943803676769 18999662014235207852757577)
      ·
        refine ⟨14249746510676405889568183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18999662014235207852757577 14249746510676405889568183)
        ·
          refine ⟨21374619766014608834352275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14249746510676405889568183 21374619766014608834352275)
          ·
            refine ⟨32061929649021913251528413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21374619766014608834352275 32061929649021913251528413)
            ·
              refine ⟨12023223618383217469323155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32061929649021913251528413 12023223618383217469323155)
              ·
                refine ⟨18034835427574826203984733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12023223618383217469323155 18034835427574826203984733)
                ·
                  refine ⟨6763063285340559826494275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18034835427574826203984733 6763063285340559826494275)
                  ·
                    refine ⟨10144594928010839739741413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6763063285340559826494275 10144594928010839739741413)
                    ·
                      refine ⟨1902111549002032451201515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10144594928010839739741413 1902111549002032451201515)
                      ·
                        rfl

theorem cell23_3704349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3704349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704349 prefixEnd_3704349 := by exact prefixLift 3704349
  have htrace : WordTrace (prefixWord ++ tailWord_3704349) baseStart_3704349 baseEnd_3704349 := by
    simpa [prefixWord, tailWord_3704349, baseEnd_3704349] using wordTrace_append hprefix tailTrace_3704349
  have hstable : (prefixWord ++ tailWord_3704349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704349).length < 2 ^ (prefixWord ++ tailWord_3704349).sum := by decide
  have hdescent : baseEnd_3704349 < baseStart_3704349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704372 : List Nat := [2, 5, 1, 15]
def baseStart_3704372 : Nat := 118140960795 + 3704372 * 2 ^ 59
def prefixEnd_3704372 : Nat := 4983230072969 + 3 ^ 40 * 3704372 * 2
def baseEnd_3704372 : Nat := 869740904918649227807

theorem tailTrace_3704372 : CollatzResearch.WordTrace tailWord_3704372 prefixEnd_3704372 869740904918649227807 := by
  unfold tailWord_3704372
  simp only [CollatzResearch.WordTrace]
  refine ⟨67554773267850187607181685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90073031023800250142908913 67554773267850187607181685)
  ·
    refine ⟨6333259993860955088173283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67554773267850187607181685 6333259993860955088173283)
    ·
      refine ⟨9499889990791432632259925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6333259993860955088173283 9499889990791432632259925)
      ·
        refine ⟨869740904918649227807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 9499889990791432632259925 869740904918649227807)
        ·
          rfl

theorem cell23_3704372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 15].length) (baseStart_3704372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704372 prefixEnd_3704372 := by exact prefixLift 3704372
  have htrace : WordTrace (prefixWord ++ tailWord_3704372) baseStart_3704372 baseEnd_3704372 := by
    simpa [prefixWord, tailWord_3704372, baseEnd_3704372] using wordTrace_append hprefix tailTrace_3704372
  have hstable : (prefixWord ++ tailWord_3704372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704372).length < 2 ^ (prefixWord ++ tailWord_3704372).sum := by decide
  have hdescent : baseEnd_3704372 < baseStart_3704372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704376 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 2, 4]
def baseStart_3704376 : Nat := 118140960795 + 3704376 * 2 ^ 59
def prefixEnd_3704376 : Nat := 4983230072969 + 3 ^ 40 * 3704376 * 2
def baseEnd_3704376 : Nat := 634041804326567948521297

theorem tailTrace_3704376 : CollatzResearch.WordTrace tailWord_3704376 prefixEnd_3704376 634041804326567948521297 := by
  unfold tailWord_3704376
  simp only [CollatzResearch.WordTrace]
  refine ⟨67554846213842941948754491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90073128285123922598339321 67554846213842941948754491)
  ·
    refine ⟨101332269320764412923131737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67554846213842941948754491 101332269320764412923131737)
    ·
      refine ⟨75999201990573309692348803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101332269320764412923131737 75999201990573309692348803)
      ·
        refine ⟨113998802985859964538523205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75999201990573309692348803 113998802985859964538523205)
        ·
          refine ⟨21374775559848743350973101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113998802985859964538523205 21374775559848743350973101)
          ·
            refine ⟨8015540834943278756614913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21374775559848743350973101 8015540834943278756614913)
            ·
              refine ⟨6011655626207459067461185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8015540834943278756614913 6011655626207459067461185)
              ·
                refine ⟨4508741719655594300595889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6011655626207459067461185 4508741719655594300595889)
                ·
                  refine ⟨3381556289741695725446917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4508741719655594300595889 3381556289741695725446917)
                  ·
                    refine ⟨634041804326567948521297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3381556289741695725446917 634041804326567948521297)
                    ·
                      rfl

theorem cell23_3704376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_3704376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704376 prefixEnd_3704376 := by exact prefixLift 3704376
  have htrace : WordTrace (prefixWord ++ tailWord_3704376) baseStart_3704376 baseEnd_3704376 := by
    simpa [prefixWord, tailWord_3704376, baseEnd_3704376] using wordTrace_append hprefix tailTrace_3704376
  have hstable : (prefixWord ++ tailWord_3704376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704376).length < 2 ^ (prefixWord ++ tailWord_3704376).sum := by decide
  have hdescent : baseEnd_3704376 < baseStart_3704376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704399 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 6, 1, 3]
def baseStart_3704399 : Nat := 118140960795 + 3704399 * 2 ^ 59
def prefixEnd_3704399 : Nat := 4983230072969 + 3 ^ 40 * 3704399 * 2
def baseEnd_3704399 : Nat := 1902137223034757255576285

theorem tailTrace_3704399 : CollatzResearch.WordTrace tailWord_3704399 prefixEnd_3704399 1902137223034757255576285 := by
  unfold tailWord_3704399
  simp only [CollatzResearch.WordTrace]
  refine ⟨135110531306602558825596251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90073687537735039217064167 135110531306602558825596251)
  ·
    refine ⟨202665796959903838238394377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135110531306602558825596251 202665796959903838238394377)
    ·
      refine ⟨151999347719927878678795783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202665796959903838238394377 151999347719927878678795783)
      ·
        refine ⟨227999021579891818018193675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151999347719927878678795783 227999021579891818018193675)
        ·
          refine ⟨341998532369837727027290513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227999021579891818018193675 341998532369837727027290513)
          ·
            refine ⟨256498899277378295270467885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341998532369837727027290513 256498899277378295270467885)
            ·
              refine ⟨96187087229016860726425457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256498899277378295270467885 96187087229016860726425457)
              ·
                refine ⟨72140315421762645544819093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96187087229016860726425457 72140315421762645544819093)
                ·
                  refine ⟨3381577285395124009913395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72140315421762645544819093 3381577285395124009913395)
                  ·
                    refine ⟨5072365928092686014870093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3381577285395124009913395 5072365928092686014870093)
                    ·
                      refine ⟨1902137223034757255576285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5072365928092686014870093 1902137223034757255576285)
                      ·
                        rfl

theorem cell23_3704399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 1, 3].length) (baseStart_3704399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704399 prefixEnd_3704399 := by exact prefixLift 3704399
  have htrace : WordTrace (prefixWord ++ tailWord_3704399) baseStart_3704399 baseEnd_3704399 := by
    simpa [prefixWord, tailWord_3704399, baseEnd_3704399] using wordTrace_append hprefix tailTrace_3704399
  have hstable : (prefixWord ++ tailWord_3704399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704399).length < 2 ^ (prefixWord ++ tailWord_3704399).sum := by decide
  have hdescent : baseEnd_3704399 < baseStart_3704399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704442 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_3704442 : Nat := 118140960795 + 3704442 * 2 ^ 59
def prefixEnd_3704442 : Nat := 4983230072969 + 3 ^ 40 * 3704442 * 2
def baseEnd_3704442 : Nat := 1902159302702900587338587

theorem tailTrace_3704442 : CollatzResearch.WordTrace tailWord_3704442 prefixEnd_3704442 1902159302702900587338587 := by
  unfold tailWord_3704442
  simp only [CollatzResearch.WordTrace]
  refine ⟨33778024911361694292352895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90074733096964518112941053 33778024911361694292352895)
  ·
    refine ⟨50667037367042541438529343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33778024911361694292352895 50667037367042541438529343)
    ·
      refine ⟨76000556050563812157794015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50667037367042541438529343 76000556050563812157794015)
      ·
        refine ⟨114000834075845718236691023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76000556050563812157794015 114000834075845718236691023)
        ·
          refine ⟨171001251113768577355036535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114000834075845718236691023 171001251113768577355036535)
          ·
            refine ⟨256501876670652866032554803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171001251113768577355036535 256501876670652866032554803)
            ·
              refine ⟨384752815005979299048832205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256501876670652866032554803 384752815005979299048832205)
              ·
                refine ⟨144282305627242237143312077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384752815005979299048832205 144282305627242237143312077)
                ·
                  refine ⟨54105864610215838928742029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144282305627242237143312077 54105864610215838928742029)
                  ·
                    refine ⟨20289699228830939598278261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54105864610215838928742029 20289699228830939598278261)
                    ·
                      refine ⟨1902159302702900587338587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20289699228830939598278261 1902159302702900587338587)
                      ·
                        rfl

theorem cell23_3704442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_3704442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704442 prefixEnd_3704442 := by exact prefixLift 3704442
  have htrace : WordTrace (prefixWord ++ tailWord_3704442) baseStart_3704442 baseEnd_3704442 := by
    simpa [prefixWord, tailWord_3704442, baseEnd_3704442] using wordTrace_append hprefix tailTrace_3704442
  have hstable : (prefixWord ++ tailWord_3704442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704442).length < 2 ^ (prefixWord ++ tailWord_3704442).sum := by decide
  have hdescent : baseEnd_3704442 < baseStart_3704442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704449 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3704449 : Nat := 118140960795 + 3704449 * 2 ^ 59
def prefixEnd_3704449 : Nat := 4983230072969 + 3 ^ 40 * 3704449 * 2
def baseEnd_3704449 : Nat := 634054299022494019983685

theorem tailTrace_3704449 : CollatzResearch.WordTrace tailWord_3704449 prefixEnd_3704449 634054299022494019983685 := by
  unfold tailWord_3704449
  simp only [CollatzResearch.WordTrace]
  refine ⟨135112354956421417364916401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90074903304280944909944267 135112354956421417364916401)
  ·
    refine ⟨101334266217316063023687301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135112354956421417364916401 101334266217316063023687301)
    ·
      refine ⟨19000174915746761816941369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101334266217316063023687301 19000174915746761816941369)
      ·
        refine ⟨14250131186810071362706027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19000174915746761816941369 14250131186810071362706027)
        ·
          refine ⟨21375196780215107044059041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14250131186810071362706027 21375196780215107044059041)
          ·
            refine ⟨16031397585161330283044281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21375196780215107044059041 16031397585161330283044281)
            ·
              refine ⟨12023548188870997712283211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16031397585161330283044281 12023548188870997712283211)
              ·
                refine ⟨18035322283306496568424817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12023548188870997712283211 18035322283306496568424817)
                ·
                  refine ⟨13526491712479872426318613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18035322283306496568424817 13526491712479872426318613)
                  ·
                    refine ⟨634054299022494019983685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13526491712479872426318613 634054299022494019983685)
                    ·
                      rfl

theorem cell23_3704449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3704449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704449 prefixEnd_3704449 := by exact prefixLift 3704449
  have htrace : WordTrace (prefixWord ++ tailWord_3704449) baseStart_3704449 baseEnd_3704449 := by
    simpa [prefixWord, tailWord_3704449, baseEnd_3704449] using wordTrace_append hprefix tailTrace_3704449
  have hstable : (prefixWord ++ tailWord_3704449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704449).length < 2 ^ (prefixWord ++ tailWord_3704449).sum := by decide
  have hdescent : baseEnd_3704449 < baseStart_3704449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704476 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3704476 : Nat := 118140960795 + 3704476 * 2 ^ 59
def prefixEnd_3704476 : Nat := 4983230072969 + 3 ^ 40 * 3704476 * 2
def baseEnd_3704476 : Nat := 1902176761045153454313431

theorem tailTrace_3704476 : CollatzResearch.WordTrace tailWord_3704476 prefixEnd_3704476 1902176761045153454313431 := by
  unfold tailWord_3704476
  simp only [CollatzResearch.WordTrace]
  refine ⟨67556669863661800488074641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90075559818215733984099521 67556669863661800488074641)
  ·
    refine ⟨50667502397746350366055981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67556669863661800488074641 50667502397746350366055981)
    ·
      refine ⟨19000313399154881387270993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50667502397746350366055981 19000313399154881387270993)
      ·
        refine ⟨14250235049366161040453245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19000313399154881387270993 14250235049366161040453245)
        ·
          refine ⟨5343838143512310390169967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14250235049366161040453245 5343838143512310390169967)
          ·
            refine ⟨8015757215268465585254951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343838143512310390169967 8015757215268465585254951)
            ·
              refine ⟨12023635822902698377882427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8015757215268465585254951 12023635822902698377882427)
              ·
                refine ⟨18035453734354047566823641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12023635822902698377882427 18035453734354047566823641)
                ·
                  refine ⟨13526590300765535675117731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18035453734354047566823641 13526590300765535675117731)
                  ·
                    refine ⟨20289885451148303512676597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13526590300765535675117731 20289885451148303512676597)
                    ·
                      refine ⟨1902176761045153454313431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20289885451148303512676597 1902176761045153454313431)
                      ·
                        rfl

theorem cell23_3704476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3704476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704476 prefixEnd_3704476 := by exact prefixLift 3704476
  have htrace : WordTrace (prefixWord ++ tailWord_3704476) baseStart_3704476 baseEnd_3704476 := by
    simpa [prefixWord, tailWord_3704476, baseEnd_3704476] using wordTrace_append hprefix tailTrace_3704476
  have hstable : (prefixWord ++ tailWord_3704476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704476).length < 2 ^ (prefixWord ++ tailWord_3704476).sum := by decide
  have hdescent : baseEnd_3704476 < baseStart_3704476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704492 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_3704492 : Nat := 118140960795 + 3704492 * 2 ^ 59
def prefixEnd_3704492 : Nat := 4983230072969 + 3 ^ 40 * 3704492 * 2
def baseEnd_3704492 : Nat := 634061658911875130571119

theorem tailTrace_3704492 : CollatzResearch.WordTrace tailWord_3704492 prefixEnd_3704492 634061658911875130571119 := by
  unfold tailWord_3704492
  simp only [CollatzResearch.WordTrace]
  refine ⟨67556961647632817854365865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90075948863510423805821153 67556961647632817854365865)
  ·
    refine ⟨50667721235724613390774399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67556961647632817854365865 50667721235724613390774399)
    ·
      refine ⟨76001581853586920086161599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50667721235724613390774399 76001581853586920086161599)
      ·
        refine ⟨114002372780380380129242399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76001581853586920086161599 114002372780380380129242399)
        ·
          refine ⟨171003559170570570193863599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114002372780380380129242399 171003559170570570193863599)
          ·
            refine ⟨256505338755855855290795399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171003559170570570193863599 256505338755855855290795399)
            ·
              refine ⟨384758008133783782936193099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256505338755855855290795399 384758008133783782936193099)
              ·
                refine ⟨577137012200675674404289649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384758008133783782936193099 577137012200675674404289649)
                ·
                  refine ⟨432852759150506755803217237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577137012200675674404289649 432852759150506755803217237)
                  ·
                    refine ⟨634061658911875130571119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 432852759150506755803217237 634061658911875130571119)
                    ·
                      rfl

theorem cell23_3704492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_3704492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704492 prefixEnd_3704492 := by exact prefixLift 3704492
  have htrace : WordTrace (prefixWord ++ tailWord_3704492) baseStart_3704492 baseEnd_3704492 := by
    simpa [prefixWord, tailWord_3704492, baseEnd_3704492] using wordTrace_append hprefix tailTrace_3704492
  have hstable : (prefixWord ++ tailWord_3704492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704492).length < 2 ^ (prefixWord ++ tailWord_3704492).sum := by decide
  have hdescent : baseEnd_3704492 < baseStart_3704492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704509 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_3704509 : Nat := 118140960795 + 3704509 * 2 ^ 59
def prefixEnd_3704509 : Nat := 4983230072969 + 3 ^ 40 * 3704509 * 2
def baseEnd_3704509 : Nat := 634064568635583941733593

theorem tailTrace_3704509 : CollatzResearch.WordTrace tailWord_3704509 prefixEnd_3704509 634064568635583941733593 := by
  unfold tailWord_3704509
  simp only [CollatzResearch.WordTrace]
  refine ⟨135114543336204047612100581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90076362224136031741400387 135114543336204047612100581)
  ·
    refine ⟨25333976875538258927268859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135114543336204047612100581 25333976875538258927268859)
    ·
      refine ⟨38000965313307388390903289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25333976875538258927268859 38000965313307388390903289)
      ·
        refine ⟨28500723984980541293177467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38000965313307388390903289 28500723984980541293177467)
        ·
          refine ⟨42751085977470811939766201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28500723984980541293177467 42751085977470811939766201)
          ·
            refine ⟨32063314483103108954824651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42751085977470811939766201 32063314483103108954824651)
            ·
              refine ⟨48094971724654663432236977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32063314483103108954824651 48094971724654663432236977)
              ·
                refine ⟨36071228793490997574177733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48094971724654663432236977 36071228793490997574177733)
                ·
                  refine ⟨6763355398779562045158325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36071228793490997574177733 6763355398779562045158325)
                  ·
                    refine ⟨634064568635583941733593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6763355398779562045158325 634064568635583941733593)
                    ·
                      rfl

theorem cell23_3704509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_3704509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704509 prefixEnd_3704509 := by exact prefixLift 3704509
  have htrace : WordTrace (prefixWord ++ tailWord_3704509) baseStart_3704509 baseEnd_3704509 := by
    simpa [prefixWord, tailWord_3704509, baseEnd_3704509] using wordTrace_append hprefix tailTrace_3704509
  have hstable : (prefixWord ++ tailWord_3704509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704509).length < 2 ^ (prefixWord ++ tailWord_3704509).sum := by decide
  have hdescent : baseEnd_3704509 < baseStart_3704509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704526 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_3704526 : Nat := 118140960795 + 3704526 * 2 ^ 59
def prefixEnd_3704526 : Nat := 4983230072969 + 3 ^ 40 * 3704526 * 2
def baseEnd_3704526 : Nat := 634067478359292752896067

theorem tailTrace_3704526 : CollatzResearch.WordTrace tailWord_3704526 prefixEnd_3704526 634067478359292752896067 := by
  unfold tailWord_3704526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16889395422142807439433679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90076775584761639676979621 16889395422142807439433679)
  ·
    refine ⟨25334093133214211159150519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16889395422142807439433679 25334093133214211159150519)
    ·
      refine ⟨38001139699821316738725779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25334093133214211159150519 38001139699821316738725779)
      ·
        refine ⟨57001709549731975108088669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38001139699821316738725779 57001709549731975108088669)
        ·
          refine ⟨21375641081149490665533251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57001709549731975108088669 21375641081149490665533251)
          ·
            refine ⟨32063461621724235998299877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21375641081149490665533251 32063461621724235998299877)
            ·
              refine ⟨6011899054073294249681227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32063461621724235998299877 6011899054073294249681227)
              ·
                refine ⟨9017848581109941374521841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011899054073294249681227 9017848581109941374521841)
                ·
                  refine ⟨6763386435832456030891381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9017848581109941374521841 6763386435832456030891381)
                  ·
                    refine ⟨634067478359292752896067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6763386435832456030891381 634067478359292752896067)
                    ·
                      rfl

theorem cell23_3704526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_3704526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704526 prefixEnd_3704526 := by exact prefixLift 3704526
  have htrace : WordTrace (prefixWord ++ tailWord_3704526) baseStart_3704526 baseEnd_3704526 := by
    simpa [prefixWord, tailWord_3704526, baseEnd_3704526] using wordTrace_append hprefix tailTrace_3704526
  have hstable : (prefixWord ++ tailWord_3704526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704526).length < 2 ^ (prefixWord ++ tailWord_3704526).sum := by decide
  have hdescent : baseEnd_3704526 < baseStart_3704526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704547 : List Nat := [1, 1, 1, 7, 3, 1, 2, 2, 5]
def baseStart_3704547 : Nat := 118140960795 + 3704547 * 2 ^ 59
def prefixEnd_3704547 : Nat := 4983230072969 + 3 ^ 40 * 3704547 * 2
def baseEnd_3704547 : Nat := 211357024241291408502845

theorem tailTrace_3704547 : CollatzResearch.WordTrace tailWord_3704547 prefixEnd_3704547 211357024241291408502845 := by
  unfold tailWord_3704547
  simp only [CollatzResearch.WordTrace]
  refine ⟨135115929310066380101983895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90077286206710920067989263 135115929310066380101983895)
  ·
    refine ⟨202673893965099570152975843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135115929310066380101983895 202673893965099570152975843)
    ·
      refine ⟨304010840947649355229463765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202673893965099570152975843 304010840947649355229463765)
      ·
        refine ⟨7125254084710531763190557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 304010840947649355229463765 7125254084710531763190557)
        ·
          refine ⟨2671970281766449411196459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7125254084710531763190557 2671970281766449411196459)
          ·
            refine ⟨4007955422649674116794689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671970281766449411196459 4007955422649674116794689)
            ·
              refine ⟨3005966566987255587596017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4007955422649674116794689 3005966566987255587596017)
              ·
                refine ⟨2254474925240441690697013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005966566987255587596017 2254474925240441690697013)
                ·
                  refine ⟨211357024241291408502845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2254474925240441690697013 211357024241291408502845)
                  ·
                    rfl

theorem cell23_3704547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 5].length) (baseStart_3704547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704547 prefixEnd_3704547 := by exact prefixLift 3704547
  have htrace : WordTrace (prefixWord ++ tailWord_3704547) baseStart_3704547 baseEnd_3704547 := by
    simpa [prefixWord, tailWord_3704547, baseEnd_3704547] using wordTrace_append hprefix tailTrace_3704547
  have hstable : (prefixWord ++ tailWord_3704547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704547).length < 2 ^ (prefixWord ++ tailWord_3704547).sum := by decide
  have hdescent : baseEnd_3704547 < baseStart_3704547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704549 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3704549 : Nat := 118140960795 + 3704549 * 2 ^ 59
def prefixEnd_3704549 : Nat := 4983230072969 + 3 ^ 40 * 3704549 * 2
def baseEnd_3704549 : Nat := 1902214245132931668700595

theorem tailTrace_3704549 : CollatzResearch.WordTrace tailWord_3704549 prefixEnd_3704549 1902214245132931668700595 := by
  unfold tailWord_3704549
  simp only [CollatzResearch.WordTrace]
  refine ⟨135116002256059134443556701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90077334837372756295704467 135116002256059134443556701)
  ·
    refine ⟨50668500846022175416333763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135116002256059134443556701 50668500846022175416333763)
    ·
      refine ⟨76002751269033263124500645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50668500846022175416333763 76002751269033263124500645)
      ·
        refine ⟨14250515862943736835843871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76002751269033263124500645 14250515862943736835843871)
        ·
          refine ⟨21375773794415605253765807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14250515862943736835843871 21375773794415605253765807)
          ·
            refine ⟨32063660691623407880648711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21375773794415605253765807 32063660691623407880648711)
            ·
              refine ⟨48095491037435111820973067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32063660691623407880648711 48095491037435111820973067)
              ·
                refine ⟨72143236556152667731459601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48095491037435111820973067 72143236556152667731459601)
                ·
                  refine ⟨54107427417114500798594701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72143236556152667731459601 54107427417114500798594701)
                  ·
                    refine ⟨20290285281417937799473013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54107427417114500798594701 20290285281417937799473013)
                    ·
                      refine ⟨1902214245132931668700595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20290285281417937799473013 1902214245132931668700595)
                      ·
                        rfl

theorem cell23_3704549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3704549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704549 prefixEnd_3704549 := by exact prefixLift 3704549
  have htrace : WordTrace (prefixWord ++ tailWord_3704549) baseStart_3704549 baseEnd_3704549 := by
    simpa [prefixWord, tailWord_3704549, baseEnd_3704549] using wordTrace_append hprefix tailTrace_3704549
  have hstable : (prefixWord ++ tailWord_3704549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704549).length < 2 ^ (prefixWord ++ tailWord_3704549).sum := by decide
  have hdescent : baseEnd_3704549 < baseStart_3704549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704583 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3704583 : Nat := 118140960795 + 3704583 * 2 ^ 59
def prefixEnd_3704583 : Nat := 4983230072969 + 3 ^ 40 * 3704583 * 2
def baseEnd_3704583 : Nat := 1902231703475184535675439

theorem tailTrace_3704583 : CollatzResearch.WordTrace tailWord_3704583 prefixEnd_3704583 1902231703475184535675439 := by
  unfold tailWord_3704583
  simp only [CollatzResearch.WordTrace]
  refine ⟨135117242337935958250294403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90078161558623972166862935 135117242337935958250294403)
  ·
    refine ⟨202675863506903937375441605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135117242337935958250294403 202675863506903937375441605)
    ·
      refine ⟨38001724407544488257895301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202675863506903937375441605 38001724407544488257895301)
      ·
        refine ⟨7125323326414591548355369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38001724407544488257895301 7125323326414591548355369)
        ·
          refine ⟨5343992494810943661266527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7125323326414591548355369 5343992494810943661266527)
          ·
            refine ⟨8015988742216415491899791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343992494810943661266527 8015988742216415491899791)
            ·
              refine ⟨12023983113324623237849687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8015988742216415491899791 12023983113324623237849687)
              ·
                refine ⟨18035974669986934856774531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12023983113324623237849687 18035974669986934856774531)
                ·
                  refine ⟨27053962004980402285161797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18035974669986934856774531 27053962004980402285161797)
                  ·
                    refine ⟨5072617875933825428467837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27053962004980402285161797 5072617875933825428467837)
                    ·
                      refine ⟨1902231703475184535675439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5072617875933825428467837 1902231703475184535675439)
                      ·
                        rfl

theorem cell23_3704583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3704583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704583 prefixEnd_3704583 := by exact prefixLift 3704583
  have htrace : WordTrace (prefixWord ++ tailWord_3704583) baseStart_3704583 baseEnd_3704583 := by
    simpa [prefixWord, tailWord_3704583, baseEnd_3704583] using wordTrace_append hprefix tailTrace_3704583
  have hstable : (prefixWord ++ tailWord_3704583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704583).length < 2 ^ (prefixWord ++ tailWord_3704583).sum := by decide
  have hdescent : baseEnd_3704583 < baseStart_3704583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704613 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 3, 1, 3]
def baseStart_3704613 : Nat := 118140960795 + 3704613 * 2 ^ 59
def prefixEnd_3704613 : Nat := 4983230072969 + 3 ^ 40 * 3704613 * 2
def baseEnd_3704613 : Nat := 1902247107894819418300301

theorem tailTrace_3704613 : CollatzResearch.WordTrace tailWord_3704613 prefixEnd_3704613 1902247107894819418300301 := by
  unfold tailWord_3704613
  simp only [CollatzResearch.WordTrace]
  refine ⟨135118336527827273373886493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90078891018551515582590995 135118336527827273373886493)
  ·
    refine ⟨50669376197935227515207435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135118336527827273373886493 50669376197935227515207435)
    ·
      refine ⟨76004064296902841272811153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50669376197935227515207435 76004064296902841272811153)
      ·
        refine ⟨57003048222677130954608365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76004064296902841272811153 57003048222677130954608365)
        ·
          refine ⟨21376143083503924107978137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57003048222677130954608365 21376143083503924107978137)
          ·
            refine ⟨16032107312627943080983603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21376143083503924107978137 16032107312627943080983603)
            ·
              refine ⟨24048160968941914621475405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16032107312627943080983603 24048160968941914621475405)
              ·
                refine ⟨9018060363353217983053277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24048160968941914621475405 9018060363353217983053277)
                ·
                  refine ⟨3381772636257456743644979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9018060363353217983053277 3381772636257456743644979)
                  ·
                    refine ⟨5072658954386185115467469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3381772636257456743644979 5072658954386185115467469)
                    ·
                      refine ⟨1902247107894819418300301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5072658954386185115467469 1902247107894819418300301)
                      ·
                        rfl

theorem cell23_3704613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_3704613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704613 prefixEnd_3704613 := by exact prefixLift 3704613
  have htrace : WordTrace (prefixWord ++ tailWord_3704613) baseStart_3704613 baseEnd_3704613 := by
    simpa [prefixWord, tailWord_3704613, baseEnd_3704613] using wordTrace_append hprefix tailTrace_3704613
  have hstable : (prefixWord ++ tailWord_3704613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704613).length < 2 ^ (prefixWord ++ tailWord_3704613).sum := by decide
  have hdescent : baseEnd_3704613 < baseStart_3704613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704636 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3704636 : Nat := 118140960795 + 3704636 * 2 ^ 59
def prefixEnd_3704636 : Nat := 4983230072969 + 3 ^ 40 * 3704636 * 2
def baseEnd_3704636 : Nat := 1902258917949872828312695

theorem tailTrace_3704636 : CollatzResearch.WordTrace tailWord_3704636 prefixEnd_3704636 1902258917949872828312695 := by
  unfold tailWord_3704636
  simp only [CollatzResearch.WordTrace]
  refine ⟨67559587703371974150986881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90079450271162632201315841 67559587703371974150986881)
  ·
    refine ⟨50669690777528980613240161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67559587703371974150986881 50669690777528980613240161)
    ·
      refine ⟨38002268083146735459930121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50669690777528980613240161 38002268083146735459930121)
      ·
        refine ⟨28501701062360051594947591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38002268083146735459930121 28501701062360051594947591)
        ·
          refine ⟨42752551593540077392421387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28501701062360051594947591 42752551593540077392421387)
          ·
            refine ⟨64128827390310116088632081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42752551593540077392421387 64128827390310116088632081)
            ·
              refine ⟨48096620542732587066474061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64128827390310116088632081 48096620542732587066474061)
              ·
                refine ⟨18036232703524720149927773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48096620542732587066474061 18036232703524720149927773)
                ·
                  refine ⟨6763587263821770056222915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18036232703524720149927773 6763587263821770056222915)
                  ·
                    refine ⟨10145380895732655084334373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6763587263821770056222915 10145380895732655084334373)
                    ·
                      refine ⟨1902258917949872828312695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10145380895732655084334373 1902258917949872828312695)
                      ·
                        rfl

theorem cell23_3704636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3704636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704636 prefixEnd_3704636 := by exact prefixLift 3704636
  have htrace : WordTrace (prefixWord ++ tailWord_3704636) baseStart_3704636 baseEnd_3704636 := by
    simpa [prefixWord, tailWord_3704636, baseEnd_3704636] using wordTrace_append hprefix tailTrace_3704636
  have hstable : (prefixWord ++ tailWord_3704636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704636).length < 2 ^ (prefixWord ++ tailWord_3704636).sum := by decide
  have hdescent : baseEnd_3704636 < baseStart_3704636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704656 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 3]
def baseStart_3704656 : Nat := 118140960795 + 3704656 * 2 ^ 59
def prefixEnd_3704656 : Nat := 4983230072969 + 3 ^ 40 * 3704656 * 2
def baseEnd_3704656 : Nat := 1902269187562962750062603

theorem tailTrace_3704656 : CollatzResearch.WordTrace tailWord_3704656 prefixEnd_3704656 1902269187562962750062603 := by
  unfold tailWord_3704656
  simp only [CollatzResearch.WordTrace]
  refine ⟨67559952433335745858850911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90079936577780994478467881 67559952433335745858850911)
  ·
    refine ⟨101339928650003618788276367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67559952433335745858850911 101339928650003618788276367)
    ·
      refine ⟨152009892975005428182414551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101339928650003618788276367 152009892975005428182414551)
      ·
        refine ⟨228014839462508142273621827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152009892975005428182414551 228014839462508142273621827)
        ·
          refine ⟨342022259193762213410432741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228014839462508142273621827 342022259193762213410432741)
          ·
            refine ⟨64129173598830415014456139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342022259193762213410432741 64129173598830415014456139)
            ·
              refine ⟨96193760398245622521684209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64129173598830415014456139 96193760398245622521684209)
              ·
                refine ⟨72145320298684216891263157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96193760398245622521684209 72145320298684216891263157)
                ·
                  refine ⟨6763623778001645333555921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72145320298684216891263157 6763623778001645333555921)
                  ·
                    refine ⟨5072717833501234000166941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6763623778001645333555921 5072717833501234000166941)
                    ·
                      refine ⟨1902269187562962750062603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5072717833501234000166941 1902269187562962750062603)
                      ·
                        rfl

theorem cell23_3704656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 3].length) (baseStart_3704656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704656 prefixEnd_3704656 := by exact prefixLift 3704656
  have htrace : WordTrace (prefixWord ++ tailWord_3704656) baseStart_3704656 baseEnd_3704656 := by
    simpa [prefixWord, tailWord_3704656, baseEnd_3704656] using wordTrace_append hprefix tailTrace_3704656
  have hstable : (prefixWord ++ tailWord_3704656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704656).length < 2 ^ (prefixWord ++ tailWord_3704656).sum := by decide
  have hdescent : baseEnd_3704656 < baseStart_3704656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704730 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2]
def baseStart_3704730 : Nat := 118140960795 + 3704730 * 2 ^ 59
def prefixEnd_3704730 : Nat := 4983230072969 + 3 ^ 40 * 3704730 * 2
def baseEnd_3704730 : Nat := 1902307185131395460537263

theorem tailTrace_3704730 : CollatzResearch.WordTrace tailWord_3704730 prefixEnd_3704730 1902307185131395460537263 := by
  unfold tailWord_3704730
  simp only [CollatzResearch.WordTrace]
  refine ⟨33780650967100850588973911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90081735912268934903930429 33780650967100850588973911)
  ·
    refine ⟨50670976450651275883460867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33780650967100850588973911 50670976450651275883460867)
    ·
      refine ⟨76006464675976913825191301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50670976450651275883460867 76006464675976913825191301)
      ·
        refine ⟨14251212126745671342223369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76006464675976913825191301 14251212126745671342223369)
        ·
          refine ⟨10688409095059253506667527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14251212126745671342223369 10688409095059253506667527)
          ·
            refine ⟨16032613642588880260001291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10688409095059253506667527 16032613642588880260001291)
            ·
              refine ⟨24048920463883320390001937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16032613642588880260001291 24048920463883320390001937)
              ·
                refine ⟨18036690347912490292501453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24048920463883320390001937 18036690347912490292501453)
                ·
                  refine ⟨6763758880467183859688045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18036690347912490292501453 6763758880467183859688045)
                  ·
                    refine ⟨2536409580175193947383017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6763758880467183859688045 2536409580175193947383017)
                    ·
                      refine ⟨1902307185131395460537263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2536409580175193947383017 1902307185131395460537263)
                      ·
                        rfl

theorem cell23_3704730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_3704730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704730 prefixEnd_3704730 := by exact prefixLift 3704730
  have htrace : WordTrace (prefixWord ++ tailWord_3704730) baseStart_3704730 baseEnd_3704730 := by
    simpa [prefixWord, tailWord_3704730, baseEnd_3704730] using wordTrace_append hprefix tailTrace_3704730
  have hstable : (prefixWord ++ tailWord_3704730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704730).length < 2 ^ (prefixWord ++ tailWord_3704730).sum := by decide
  have hdescent : baseEnd_3704730 < baseStart_3704730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704760 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 4, 2, 2]
def baseStart_3704760 : Nat := 118140960795 + 3704760 * 2 ^ 59
def prefixEnd_3704760 : Nat := 4983230072969 + 3 ^ 40 * 3704760 * 2
def baseEnd_3704760 : Nat := 1902322589551030343162125

theorem tailTrace_3704760 : CollatzResearch.WordTrace tailWord_3704760 prefixEnd_3704760 1902322589551030343162125 := by
  unfold tailWord_3704760
  simp only [CollatzResearch.WordTrace]
  refine ⟨67561849029147358739743867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90082465372196478319658489 67561849029147358739743867)
  ·
    refine ⟨101342773543721038109615801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67561849029147358739743867 101342773543721038109615801)
    ·
      refine ⟨76007080157790778582211851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101342773543721038109615801 76007080157790778582211851)
      ·
        refine ⟨114010620236686167873317777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76007080157790778582211851 114010620236686167873317777)
        ·
          refine ⟨85507965177514625904988333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114010620236686167873317777 85507965177514625904988333)
          ·
            refine ⟨32065486941567984714370625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85507965177514625904988333 32065486941567984714370625)
            ·
              refine ⟨24049115206175988535777969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32065486941567984714370625 24049115206175988535777969)
              ·
                refine ⟨18036836404631991401833477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24049115206175988535777969 18036836404631991401833477)
                ·
                  refine ⟨3381906825868498387843777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18036836404631991401833477 3381906825868498387843777)
                  ·
                    refine ⟨2536430119401373790882833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3381906825868498387843777 2536430119401373790882833)
                    ·
                      refine ⟨1902322589551030343162125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2536430119401373790882833 1902322589551030343162125)
                      ·
                        rfl

theorem cell23_3704760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_3704760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704760 prefixEnd_3704760 := by exact prefixLift 3704760
  have htrace : WordTrace (prefixWord ++ tailWord_3704760) baseStart_3704760 baseEnd_3704760 := by
    simpa [prefixWord, tailWord_3704760, baseEnd_3704760] using wordTrace_append hprefix tailTrace_3704760
  have hstable : (prefixWord ++ tailWord_3704760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704760).length < 2 ^ (prefixWord ++ tailWord_3704760).sum := by decide
  have hdescent : baseEnd_3704760 < baseStart_3704760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704764 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3704764 : Nat := 118140960795 + 3704764 * 2 ^ 59
def prefixEnd_3704764 : Nat := 4983230072969 + 3 ^ 40 * 3704764 * 2
def baseEnd_3704764 : Nat := 1902324643473648327512107

theorem tailTrace_3704764 : CollatzResearch.WordTrace tailWord_3704764 prefixEnd_3704764 1902324643473648327512107 := by
  unfold tailWord_3704764
  simp only [CollatzResearch.WordTrace]
  refine ⟨67561921975140113081316673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90082562633520150775088897 67561921975140113081316673)
  ·
    refine ⟨50671441481355084810987505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67561921975140113081316673 50671441481355084810987505)
    ·
      refine ⟨38003581111016313608240629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50671441481355084810987505 38003581111016313608240629)
      ·
        refine ⟨3562835729157779400772559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38003581111016313608240629 3562835729157779400772559)
        ·
          refine ⟨5344253593736669101158839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562835729157779400772559 5344253593736669101158839)
          ·
            refine ⟨8016380390605003651738259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344253593736669101158839 8016380390605003651738259)
            ·
              refine ⟨12024570585907505477607389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8016380390605003651738259 12024570585907505477607389)
              ·
                refine ⟨4509213969715314554102771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12024570585907505477607389 4509213969715314554102771)
                ·
                  refine ⟨6763820954572971831154157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509213969715314554102771 6763820954572971831154157)
                  ·
                    refine ⟨2536432857964864436682809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6763820954572971831154157 2536432857964864436682809)
                    ·
                      refine ⟨1902324643473648327512107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2536432857964864436682809 1902324643473648327512107)
                      ·
                        rfl

theorem cell23_3704764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3704764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704764 prefixEnd_3704764 := by exact prefixLift 3704764
  have htrace : WordTrace (prefixWord ++ tailWord_3704764) baseStart_3704764 baseEnd_3704764 := by
    simpa [prefixWord, tailWord_3704764, baseEnd_3704764] using wordTrace_append hprefix tailTrace_3704764
  have hstable : (prefixWord ++ tailWord_3704764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704764).length < 2 ^ (prefixWord ++ tailWord_3704764).sum := by decide
  have hdescent : baseEnd_3704764 < baseStart_3704764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704783 : List Nat := [1, 1, 2, 1, 1, 5, 1, 6, 5]
def baseStart_3704783 : Nat := 118140960795 + 3704783 * 2 ^ 59
def prefixEnd_3704783 : Nat := 4983230072969 + 3 ^ 40 * 3704783 * 2
def baseEnd_3704783 : Nat := 211370488845120417019391

theorem tailTrace_3704783 : CollatzResearch.WordTrace tailWord_3704783 prefixEnd_3704783 211370488845120417019391 := by
  unfold tailWord_3704783
  simp only [CollatzResearch.WordTrace]
  refine ⟨135124536937211392407575003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90083024624807594938383335 135124536937211392407575003)
  ·
    refine ⟨202686805405817088611362505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135124536937211392407575003 202686805405817088611362505)
    ·
      refine ⟨152015104054362816458521879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202686805405817088611362505 152015104054362816458521879)
      ·
        refine ⟨228022656081544224687782819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152015104054362816458521879 228022656081544224687782819)
        ·
          refine ⟨342033984122316337031674229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228022656081544224687782819 342033984122316337031674229)
          ·
            refine ⟨32065686011467156596719459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 342033984122316337031674229 32065686011467156596719459)
            ·
              refine ⟨48098529017200734895079189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32065686011467156596719459 48098529017200734895079189)
              ·
                refine ⟨2254618547681284448206837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48098529017200734895079189 2254618547681284448206837)
                ·
                  refine ⟨211370488845120417019391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2254618547681284448206837 211370488845120417019391)
                  ·
                    rfl

theorem cell23_3704783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 5].length) (baseStart_3704783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704783 prefixEnd_3704783 := by exact prefixLift 3704783
  have htrace : WordTrace (prefixWord ++ tailWord_3704783) baseStart_3704783 baseEnd_3704783 := by
    simpa [prefixWord, tailWord_3704783, baseEnd_3704783] using wordTrace_append hprefix tailTrace_3704783
  have hstable : (prefixWord ++ tailWord_3704783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704783).length < 2 ^ (prefixWord ++ tailWord_3704783).sum := by decide
  have hdescent : baseEnd_3704783 < baseStart_3704783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704794 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2]
def baseStart_3704794 : Nat := 118140960795 + 3704794 * 2 ^ 59
def prefixEnd_3704794 : Nat := 4983230072969 + 3 ^ 40 * 3704794 * 2
def baseEnd_3704794 : Nat := 1902340047893283210136969

theorem tailTrace_3704794 : CollatzResearch.WordTrace tailWord_3704794 prefixEnd_3704794 1902340047893283210136969 := by
  unfold tailWord_3704794
  simp only [CollatzResearch.WordTrace]
  refine ⟨33781234535042885321556359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90083292093447694190816957 33781234535042885321556359)
  ·
    refine ⟨50671851802564327982334539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33781234535042885321556359 50671851802564327982334539)
    ·
      refine ⟨76007777703846491973501809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50671851802564327982334539 76007777703846491973501809)
      ·
        refine ⟨57005833277884868980126357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76007777703846491973501809 57005833277884868980126357)
        ·
          refine ⟨2672148434900853233443423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57005833277884868980126357 2672148434900853233443423)
          ·
            refine ⟨4008222652351279850165135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672148434900853233443423 4008222652351279850165135)
            ·
              refine ⟨6012333978526919775247703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4008222652351279850165135 6012333978526919775247703)
              ·
                refine ⟨9018500967790379662871555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012333978526919775247703 9018500967790379662871555)
                ·
                  refine ⟨13527751451685569494307333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9018500967790379662871555 13527751451685569494307333)
                  ·
                    refine ⟨2536453397191044280182625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13527751451685569494307333 2536453397191044280182625)
                    ·
                      refine ⟨1902340047893283210136969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2536453397191044280182625 1902340047893283210136969)
                      ·
                        rfl

theorem cell23_3704794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_3704794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704794 prefixEnd_3704794 := by exact prefixLift 3704794
  have htrace : WordTrace (prefixWord ++ tailWord_3704794) baseStart_3704794 baseEnd_3704794 := by
    simpa [prefixWord, tailWord_3704794, baseEnd_3704794] using wordTrace_append hprefix tailTrace_3704794
  have hstable : (prefixWord ++ tailWord_3704794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704794).length < 2 ^ (prefixWord ++ tailWord_3704794).sum := by decide
  have hdescent : baseEnd_3704794 < baseStart_3704794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704817 : List Nat := [1, 2, 2, 2, 5, 2, 1, 3, 5]
def baseStart_3704817 : Nat := 118140960795 + 3704817 * 2 ^ 59
def prefixEnd_3704817 : Nat := 4983230072969 + 3 ^ 40 * 3704817 * 2
def baseEnd_3704817 : Nat := 211372428660926291127707

theorem tailTrace_3704817 : CollatzResearch.WordTrace tailWord_3704817 prefixEnd_3704817 211372428660926291127707 := by
  unfold tailWord_3704817
  simp only [CollatzResearch.WordTrace]
  refine ⟨135125777019088216214312705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90083851346058810809541803 135125777019088216214312705)
  ·
    refine ⟨101344332764316162160734529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135125777019088216214312705 101344332764316162160734529)
    ·
      refine ⟨76008249573237121620550897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101344332764316162160734529 76008249573237121620550897)
      ·
        refine ⟨57006187179927841215413173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76008249573237121620550897 57006187179927841215413173)
        ·
          refine ⟨5344330048118235113944985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57006187179927841215413173 5344330048118235113944985)
          ·
            refine ⟨4008247536088676335458739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5344330048118235113944985 4008247536088676335458739)
            ·
              refine ⟨6012371304133014503188109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4008247536088676335458739 6012371304133014503188109)
              ·
                refine ⟨2254639239049880438695541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6012371304133014503188109 2254639239049880438695541)
                ·
                  refine ⟨211372428660926291127707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2254639239049880438695541 211372428660926291127707)
                  ·
                    rfl

theorem cell23_3704817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 5].length) (baseStart_3704817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704817 prefixEnd_3704817 := by exact prefixLift 3704817
  have htrace : WordTrace (prefixWord ++ tailWord_3704817) baseStart_3704817 baseEnd_3704817 := by
    simpa [prefixWord, tailWord_3704817, baseEnd_3704817] using wordTrace_append hprefix tailTrace_3704817
  have hstable : (prefixWord ++ tailWord_3704817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704817).length < 2 ^ (prefixWord ++ tailWord_3704817).sum := by decide
  have hdescent : baseEnd_3704817 < baseStart_3704817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704830 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3704830 : Nat := 118140960795 + 3704830 * 2 ^ 59
def prefixEnd_3704830 : Nat := 4983230072969 + 3 ^ 40 * 3704830 * 2
def baseEnd_3704830 : Nat := 634119511065615023095601

theorem tailTrace_3704830 : CollatzResearch.WordTrace tailWord_3704830 prefixEnd_3704830 634119511065615023095601 := by
  unfold tailWord_3704830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16890781396005139929316993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90084167445360746289690629 16890781396005139929316993)
  ·
    refine ⟨12668086047003854946987745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16890781396005139929316993 12668086047003854946987745)
    ·
      refine ⟨9501064535252891210240809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12668086047003854946987745 9501064535252891210240809)
      ·
        refine ⟨7125798401439668407680607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9501064535252891210240809 7125798401439668407680607)
        ·
          refine ⟨10688697602159502611520911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7125798401439668407680607 10688697602159502611520911)
          ·
            refine ⟨16033046403239253917281367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10688697602159502611520911 16033046403239253917281367)
            ·
              refine ⟨24049569604858880875922051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16033046403239253917281367 24049569604858880875922051)
              ·
                refine ⟨36074354407288321313883077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24049569604858880875922051 36074354407288321313883077)
                ·
                  refine ⟨6763941451366560246353077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36074354407288321313883077 6763941451366560246353077)
                  ·
                    refine ⟨634119511065615023095601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6763941451366560246353077 634119511065615023095601)
                    ·
                      rfl

theorem cell23_3704830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3704830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704830 prefixEnd_3704830 := by exact prefixLift 3704830
  have htrace : WordTrace (prefixWord ++ tailWord_3704830) baseStart_3704830 baseEnd_3704830 := by
    simpa [prefixWord, tailWord_3704830, baseEnd_3704830] using wordTrace_append hprefix tailTrace_3704830
  have hstable : (prefixWord ++ tailWord_3704830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704830).length < 2 ^ (prefixWord ++ tailWord_3704830).sum := by decide
  have hdescent : baseEnd_3704830 < baseStart_3704830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704893 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3704893 : Nat := 118140960795 + 3704893 * 2 ^ 59
def prefixEnd_3704893 : Nat := 4983230072969 + 3 ^ 40 * 3704893 * 2
def baseEnd_3704893 : Nat := 1902390882478078322799013

theorem tailTrace_3704893 : CollatzResearch.WordTrace tailWord_3704893 prefixEnd_3704893 1902390882478078322799013 := by
  unfold tailWord_3704893
  simp only [CollatzResearch.WordTrace]
  refine ⟨135128548966812881194079333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90085699311208587462719555 135128548966812881194079333)
  ·
    refine ⟨25336602931277415223889875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135128548966812881194079333 25336602931277415223889875)
    ·
      refine ⟨38004904396916122835834813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25336602931277415223889875 38004904396916122835834813)
      ·
        refine ⟨14251839148843546063438055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38004904396916122835834813 14251839148843546063438055)
        ·
          refine ⟨21377758723265319095157083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14251839148843546063438055 21377758723265319095157083)
          ·
            refine ⟨32066638084897978642735625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21377758723265319095157083 32066638084897978642735625)
            ·
              refine ⟨24049978563673483982051719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32066638084897978642735625 24049978563673483982051719)
              ·
                refine ⟨36074967845510225973077579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24049978563673483982051719 36074967845510225973077579)
                ·
                  refine ⟨54112451768265338959616369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36074967845510225973077579 54112451768265338959616369)
                  ·
                    refine ⟨40584338826199004219712277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54112451768265338959616369 40584338826199004219712277)
                    ·
                      refine ⟨1902390882478078322799013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40584338826199004219712277 1902390882478078322799013)
                      ·
                        rfl

theorem cell23_3704893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3704893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704893 prefixEnd_3704893 := by exact prefixLift 3704893
  have htrace : WordTrace (prefixWord ++ tailWord_3704893) baseStart_3704893 baseEnd_3704893 := by
    simpa [prefixWord, tailWord_3704893, baseEnd_3704893] using wordTrace_append hprefix tailTrace_3704893
  have hstable : (prefixWord ++ tailWord_3704893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704893).length < 2 ^ (prefixWord ++ tailWord_3704893).sum := by decide
  have hdescent : baseEnd_3704893 < baseStart_3704893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704903 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 5, 5]
def baseStart_3704903 : Nat := 118140960795 + 3704903 * 2 ^ 59
def prefixEnd_3704903 : Nat := 4983230072969 + 3 ^ 40 * 3704903 * 2
def baseEnd_3704903 : Nat := 634132005761541094557989

theorem tailTrace_3704903 : CollatzResearch.WordTrace tailWord_3704903 prefixEnd_3704903 634132005761541094557989 := by
  unfold tailWord_3704903
  simp only [CollatzResearch.WordTrace]
  refine ⟨135128913696776652901943363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90085942464517768601295575 135128913696776652901943363)
  ·
    refine ⟨202693370545164979352915045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135128913696776652901943363 202693370545164979352915045)
    ·
      refine ⟨38005006977218433628671571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202693370545164979352915045 38005006977218433628671571)
      ·
        refine ⟨57007510465827650443007357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38005006977218433628671571 57007510465827650443007357)
        ·
          refine ⟨21377816424685368916127759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57007510465827650443007357 21377816424685368916127759)
          ·
            refine ⟨32066724637028053374191639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21377816424685368916127759 32066724637028053374191639)
            ·
              refine ⟨48100086955542080061287459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32066724637028053374191639 48100086955542080061287459)
              ·
                refine ⟨72150130433313120091931189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48100086955542080061287459 72150130433313120091931189)
                ·
                  refine ⟨6764074728123105008618549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72150130433313120091931189 6764074728123105008618549)
                  ·
                    refine ⟨634132005761541094557989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6764074728123105008618549 634132005761541094557989)
                    ·
                      rfl

theorem cell23_3704903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_3704903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704903 prefixEnd_3704903 := by exact prefixLift 3704903
  have htrace : WordTrace (prefixWord ++ tailWord_3704903) baseStart_3704903 baseEnd_3704903 := by
    simpa [prefixWord, tailWord_3704903, baseEnd_3704903] using wordTrace_append hprefix tailTrace_3704903
  have hstable : (prefixWord ++ tailWord_3704903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704903).length < 2 ^ (prefixWord ++ tailWord_3704903).sum := by decide
  have hdescent : baseEnd_3704903 < baseStart_3704903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704917 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_3704917 : Nat := 118140960795 + 3704917 * 2 ^ 59
def prefixEnd_3704917 : Nat := 4983230072969 + 3 ^ 40 * 3704917 * 2
def baseEnd_3704917 : Nat := 1902403206013786228898903

theorem tailTrace_3704917 : CollatzResearch.WordTrace tailWord_3704917 prefixEnd_3704917 1902403206013786228898903 := by
  unfold tailWord_3704917
  simp only [CollatzResearch.WordTrace]
  refine ⟨135129424318725933292953005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90086282879150622195302003 135129424318725933292953005)
  ·
    refine ⟨50673534119522224984857377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135129424318725933292953005 50673534119522224984857377)
    ·
      refine ⟨38005150589641668738643033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50673534119522224984857377 38005150589641668738643033)
      ·
        refine ⟨28503862942231251553982275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38005150589641668738643033 28503862942231251553982275)
        ·
          refine ⟨42755794413346877330973413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28503862942231251553982275 42755794413346877330973413)
          ·
            refine ⟨8016711452502539499557515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42755794413346877330973413 8016711452502539499557515)
            ·
              refine ⟨12025067178753809249336273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8016711452502539499557515 12025067178753809249336273)
              ·
                refine ⟨9018800384065356937002205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12025067178753809249336273 9018800384065356937002205)
                ·
                  refine ⟨3382050144024508851375827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9018800384065356937002205 3382050144024508851375827)
                  ·
                    refine ⟨5073075216036763277063741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382050144024508851375827 5073075216036763277063741)
                    ·
                      refine ⟨1902403206013786228898903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5073075216036763277063741 1902403206013786228898903)
                      ·
                        rfl

theorem cell23_3704917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_3704917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704917 prefixEnd_3704917 := by exact prefixLift 3704917
  have htrace : WordTrace (prefixWord ++ tailWord_3704917) baseStart_3704917 baseEnd_3704917 := by
    simpa [prefixWord, tailWord_3704917, baseEnd_3704917] using wordTrace_append hprefix tailTrace_3704917
  have hstable : (prefixWord ++ tailWord_3704917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704917).length < 2 ^ (prefixWord ++ tailWord_3704917).sum := by decide
  have hdescent : baseEnd_3704917 < baseStart_3704917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704970 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3704970 : Nat := 118140960795 + 3704970 * 2 ^ 59
def prefixEnd_3704970 : Nat := 4983230072969 + 3 ^ 40 * 3704970 * 2
def baseEnd_3704970 : Nat := 1902430420488474521536159

theorem tailTrace_3704970 : CollatzResearch.WordTrace tailWord_3704970 prefixEnd_3704970 1902430420488474521536159 := by
  unfold tailWord_3704970
  simp only [CollatzResearch.WordTrace]
  refine ⟨33782839346883480836158091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90087571591689282229754909 33782839346883480836158091)
  ·
    refine ⟨50674259020325221254237137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33782839346883480836158091 50674259020325221254237137)
    ·
      refine ⟨38005694265243915940677853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50674259020325221254237137 38005694265243915940677853)
      ·
        refine ⟨14252135349466468477754195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38005694265243915940677853 14252135349466468477754195)
        ·
          refine ⟨21378203024199702716631293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14252135349466468477754195 21378203024199702716631293)
          ·
            refine ⟨8016826134074888518736735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21378203024199702716631293 8016826134074888518736735)
            ·
              refine ⟨12025239201112332778105103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8016826134074888518736735 12025239201112332778105103)
              ·
                refine ⟨18037858801668499167157655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12025239201112332778105103 18037858801668499167157655)
                ·
                  refine ⟨27056788202502748750736483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18037858801668499167157655 27056788202502748750736483)
                  ·
                    refine ⟨40585182303754123126104725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27056788202502748750736483 40585182303754123126104725)
                    ·
                      refine ⟨1902430420488474521536159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40585182303754123126104725 1902430420488474521536159)
                      ·
                        rfl

theorem cell23_3704970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3704970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704970 prefixEnd_3704970 := by exact prefixLift 3704970
  have htrace : WordTrace (prefixWord ++ tailWord_3704970) baseStart_3704970 baseEnd_3704970 := by
    simpa [prefixWord, tailWord_3704970, baseEnd_3704970] using wordTrace_append hprefix tailTrace_3704970
  have hstable : (prefixWord ++ tailWord_3704970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704970).length < 2 ^ (prefixWord ++ tailWord_3704970).sum := by decide
  have hdescent : baseEnd_3704970 < baseStart_3704970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704974 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3704974 : Nat := 118140960795 + 3704974 * 2 ^ 59
def prefixEnd_3704974 : Nat := 4983230072969 + 3 ^ 40 * 3704974 * 2
def baseEnd_3704974 : Nat := 1902432474411092505886141

theorem tailTrace_3704974 : CollatzResearch.WordTrace tailWord_3704974 prefixEnd_3704974 1902432474411092505886141 := by
  unfold tailWord_3704974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891437909939929003472247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90087668853012954685185317 16891437909939929003472247)
  ·
    refine ⟨25337156864909893505208371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16891437909939929003472247 25337156864909893505208371)
    ·
      refine ⟨38005735297364840257812557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25337156864909893505208371 38005735297364840257812557)
      ·
        refine ⟨14252150736511815096679709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38005735297364840257812557 14252150736511815096679709)
        ·
          refine ⟨5344556526191930661254891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14252150736511815096679709 5344556526191930661254891)
          ·
            refine ⟨8016834789287895991882337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344556526191930661254891 8016834789287895991882337)
            ·
              refine ⟨6012626091965921993911753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8016834789287895991882337 6012626091965921993911753)
              ·
                refine ⟨4509469568974441495433815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6012626091965921993911753 4509469568974441495433815)
                ·
                  refine ⟨6764204353461662243150723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509469568974441495433815 6764204353461662243150723)
                  ·
                    refine ⟨10146306530192493364726085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6764204353461662243150723 10146306530192493364726085)
                    ·
                      refine ⟨1902432474411092505886141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10146306530192493364726085 1902432474411092505886141)
                      ·
                        rfl

theorem cell23_3704974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3704974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704974 prefixEnd_3704974 := by exact prefixLift 3704974
  have htrace : WordTrace (prefixWord ++ tailWord_3704974) baseStart_3704974 baseEnd_3704974 := by
    simpa [prefixWord, tailWord_3704974, baseEnd_3704974] using wordTrace_append hprefix tailTrace_3704974
  have hstable : (prefixWord ++ tailWord_3704974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704974).length < 2 ^ (prefixWord ++ tailWord_3704974).sum := by decide
  have hdescent : baseEnd_3704974 < baseStart_3704974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704994 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3704994 : Nat := 118140960795 + 3704994 * 2 ^ 59
def prefixEnd_3704994 : Nat := 4983230072969 + 3 ^ 40 * 3704994 * 2
def baseEnd_3704994 : Nat := 1902442744024182427636049

theorem tailTrace_3704994 : CollatzResearch.WordTrace tailWord_3704994 prefixEnd_3704994 1902442744024182427636049 := by
  unfold tailWord_3704994
  simp only [CollatzResearch.WordTrace]
  refine ⟨33783058184861743860876509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90088155159631316962337357 33783058184861743860876509)
  ·
    refine ⟨12668646819323153947828691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33783058184861743860876509 12668646819323153947828691)
    ·
      refine ⟨19002970228984730921743037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12668646819323153947828691 19002970228984730921743037)
      ·
        refine ⟨7126113835869274095653639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19002970228984730921743037 7126113835869274095653639)
        ·
          refine ⟨10689170753803911143480459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7126113835869274095653639 10689170753803911143480459)
          ·
            refine ⟨16033756130705866715220689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10689170753803911143480459 16033756130705866715220689)
            ·
              refine ⟨12025317098029400036415517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16033756130705866715220689 12025317098029400036415517)
              ·
                refine ⟨4509493911761025013655819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12025317098029400036415517 4509493911761025013655819)
                ·
                  refine ⟨6764240867641537520483729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509493911761025013655819 6764240867641537520483729)
                  ·
                    refine ⟨5073180650731153140362797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6764240867641537520483729 5073180650731153140362797)
                    ·
                      refine ⟨1902442744024182427636049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5073180650731153140362797 1902442744024182427636049)
                      ·
                        rfl

theorem cell23_3704994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3704994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3704994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3704994 prefixEnd_3704994 := by exact prefixLift 3704994
  have htrace : WordTrace (prefixWord ++ tailWord_3704994) baseStart_3704994 baseEnd_3704994 := by
    simpa [prefixWord, tailWord_3704994, baseEnd_3704994] using wordTrace_append hprefix tailTrace_3704994
  have hstable : (prefixWord ++ tailWord_3704994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704994).length < 2 ^ (prefixWord ++ tailWord_3704994).sum := by decide
  have hdescent : baseEnd_3704994 < baseStart_3704994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705007 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 2, 1, 3]
def baseStart_3705007 : Nat := 118140960795 + 3705007 * 2 ^ 59
def prefixEnd_3705007 : Nat := 4983230072969 + 3 ^ 40 * 3705007 * 2
def baseEnd_3705007 : Nat := 1902449419272690876773489

theorem tailTrace_3705007 : CollatzResearch.WordTrace tailWord_3705007 prefixEnd_3705007 1902449419272690876773489 := by
  unfold tailWord_3705007
  simp only [CollatzResearch.WordTrace]
  refine ⟨135132706888399878663729275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90088471258933252442486183 135132706888399878663729275)
  ·
    refine ⟨202699060332599817995593913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135132706888399878663729275 202699060332599817995593913)
    ·
      refine ⟨152024295249449863496695435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202699060332599817995593913 152024295249449863496695435)
      ·
        refine ⟨228036442874174795245043153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152024295249449863496695435 228036442874174795245043153)
        ·
          refine ⟨171027332155631096433782365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228036442874174795245043153 171027332155631096433782365)
          ·
            refine ⟨64135249558361661162668387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171027332155631096433782365 64135249558361661162668387)
            ·
              refine ⟨96202874337542491744002581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64135249558361661162668387 96202874337542491744002581)
              ·
                refine ⟨4509509734572304300500121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96202874337542491744002581 4509509734572304300500121)
                ·
                  refine ⟨3382132300929228225375091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4509509734572304300500121 3382132300929228225375091)
                  ·
                    refine ⟨5073198451393842338062637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382132300929228225375091 5073198451393842338062637)
                    ·
                      refine ⟨1902449419272690876773489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5073198451393842338062637 1902449419272690876773489)
                      ·
                        rfl

theorem cell23_3705007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 1, 3].length) (baseStart_3705007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705007 prefixEnd_3705007 := by exact prefixLift 3705007
  have htrace : WordTrace (prefixWord ++ tailWord_3705007) baseStart_3705007 baseEnd_3705007 := by
    simpa [prefixWord, tailWord_3705007, baseEnd_3705007] using wordTrace_append hprefix tailTrace_3705007
  have hstable : (prefixWord ++ tailWord_3705007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705007).length < 2 ^ (prefixWord ++ tailWord_3705007).sum := by decide
  have hdescent : baseEnd_3705007 < baseStart_3705007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705017 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 3, 3, 2]
def baseStart_3705017 : Nat := 118140960795 + 3705017 * 2 ^ 59
def prefixEnd_3705017 : Nat := 4983230072969 + 3 ^ 40 * 3705017 * 2
def baseEnd_3705017 : Nat := 1902454554079235837648443

theorem tailTrace_3705017 : CollatzResearch.WordTrace tailWord_3705017 prefixEnd_3705017 1902454554079235837648443 := by
  unfold tailWord_3705017
  simp only [CollatzResearch.WordTrace]
  refine ⟨135133071618363650371593305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90088714412242433581062203 135133071618363650371593305)
  ·
    refine ⟨101349803713772737778694979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135133071618363650371593305 101349803713772737778694979)
    ·
      refine ⟨152024705570659106668042469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101349803713772737778694979 152024705570659106668042469)
      ·
        refine ⟨28504632294498582500257963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152024705570659106668042469 28504632294498582500257963)
        ·
          refine ⟨42756948441747873750386945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28504632294498582500257963 42756948441747873750386945)
          ·
            refine ⟨32067711331310905312790209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42756948441747873750386945 32067711331310905312790209)
            ·
              refine ⟨24050783498483178984592657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32067711331310905312790209 24050783498483178984592657)
              ·
                refine ⟨18038087623862384238444493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24050783498483178984592657 18038087623862384238444493)
                ·
                  refine ⟨6764282858948394089416685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18038087623862384238444493 6764282858948394089416685)
                  ·
                    refine ⟨2536606072105647783531257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6764282858948394089416685 2536606072105647783531257)
                    ·
                      refine ⟨1902454554079235837648443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2536606072105647783531257 1902454554079235837648443)
                      ·
                        rfl

theorem cell23_3705017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_3705017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705017 prefixEnd_3705017 := by exact prefixLift 3705017
  have htrace : WordTrace (prefixWord ++ tailWord_3705017) baseStart_3705017 baseEnd_3705017 := by
    simpa [prefixWord, tailWord_3705017, baseEnd_3705017] using wordTrace_append hprefix tailTrace_3705017
  have hstable : (prefixWord ++ tailWord_3705017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705017).length < 2 ^ (prefixWord ++ tailWord_3705017).sum := by decide
  have hdescent : baseEnd_3705017 < baseStart_3705017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705023 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 1, 8]
def baseStart_3705023 : Nat := 118140960795 + 3705023 * 2 ^ 59
def prefixEnd_3705023 : Nat := 4983230072969 + 3 ^ 40 * 3705023 * 2
def baseEnd_3705023 : Nat := 634152544987720938057805

theorem tailTrace_3705023 : CollatzResearch.WordTrace tailWord_3705023 prefixEnd_3705023 634152544987720938057805 := by
  unfold tailWord_3705023
  simp only [CollatzResearch.WordTrace]
  refine ⟨135133290456341913396311723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90088860304227942264207815 135133290456341913396311723)
  ·
    refine ⟨202699935684512870094467585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135133290456341913396311723 202699935684512870094467585)
    ·
      refine ⟨152024951763384652570850689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202699935684512870094467585 152024951763384652570850689)
      ·
        refine ⟨114018713822538489428138017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152024951763384652570850689 114018713822538489428138017)
        ·
          refine ⟨85514035366903867071103513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114018713822538489428138017 85514035366903867071103513)
          ·
            refine ⟨64135526525177900303327635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85514035366903867071103513 64135526525177900303327635)
            ·
              refine ⟨96203289787766850454991453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64135526525177900303327635 96203289787766850454991453)
              ·
                refine ⟨36076233670412568920621795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96203289787766850454991453 36076233670412568920621795)
                ·
                  refine ⟨54114350505618853380932693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36076233670412568920621795 54114350505618853380932693)
                  ·
                    refine ⟨634152544987720938057805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54114350505618853380932693 634152544987720938057805)
                    ·
                      rfl

theorem cell23_3705023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_3705023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705023 prefixEnd_3705023 := by exact prefixLift 3705023
  have htrace : WordTrace (prefixWord ++ tailWord_3705023) baseStart_3705023 baseEnd_3705023 := by
    simpa [prefixWord, tailWord_3705023, baseEnd_3705023] using wordTrace_append hprefix tailTrace_3705023
  have hstable : (prefixWord ++ tailWord_3705023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705023).length < 2 ^ (prefixWord ++ tailWord_3705023).sum := by decide
  have hdescent : baseEnd_3705023 < baseStart_3705023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705024 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 2, 1, 3]
def baseStart_3705024 : Nat := 118140960795 + 3705024 * 2 ^ 59
def prefixEnd_3705024 : Nat := 4983230072969 + 3 ^ 40 * 3705024 * 2
def baseEnd_3705024 : Nat := 1902458148443817310260911

theorem tailTrace_3705024 : CollatzResearch.WordTrace tailWord_3705024 prefixEnd_3705024 1902458148443817310260911 := by
  unfold tailWord_3705024
  simp only [CollatzResearch.WordTrace]
  refine ⟨67566663464669145283549063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90088884619558860378065417 67566663464669145283549063)
  ·
    refine ⟨101349995197003717925323595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67566663464669145283549063 101349995197003717925323595)
    ·
      refine ⟨152024992795505576887985393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101349995197003717925323595 152024992795505576887985393)
      ·
        refine ⟨114018744596629182665989045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152024992795505576887985393 114018744596629182665989045)
        ·
          refine ⟨10689257305933985874936473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114018744596629182665989045 10689257305933985874936473)
          ·
            refine ⟨8016942979450489406202355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10689257305933985874936473 8016942979450489406202355)
            ·
              refine ⟨12025414469175734109303533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8016942979450489406202355 12025414469175734109303533)
              ·
                refine ⟨4509530425940900290988825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12025414469175734109303533 4509530425940900290988825)
                ·
                  refine ⟨3382147819455675218241619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4509530425940900290988825 3382147819455675218241619)
                  ·
                    refine ⟨5073221729183512827362429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382147819455675218241619 5073221729183512827362429)
                    ·
                      refine ⟨1902458148443817310260911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5073221729183512827362429 1902458148443817310260911)
                      ·
                        rfl

theorem cell23_3705024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_3705024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705024 prefixEnd_3705024 := by exact prefixLift 3705024
  have htrace : WordTrace (prefixWord ++ tailWord_3705024) baseStart_3705024 baseEnd_3705024 := by
    simpa [prefixWord, tailWord_3705024, baseEnd_3705024] using wordTrace_append hprefix tailTrace_3705024
  have hstable : (prefixWord ++ tailWord_3705024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705024).length < 2 ^ (prefixWord ++ tailWord_3705024).sum := by decide
  have hdescent : baseEnd_3705024 < baseStart_3705024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705050 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_3705050 : Nat := 118140960795 + 3705050 * 2 ^ 59
def prefixEnd_3705050 : Nat := 4983230072969 + 3 ^ 40 * 3705050 * 2
def baseEnd_3705050 : Nat := 1902471498940834208535791

theorem tailTrace_3705050 : CollatzResearch.WordTrace tailWord_3705050 prefixEnd_3705050 1902471498940834208535791 := by
  unfold tailWord_3705050
  simp only [CollatzResearch.WordTrace]
  refine ⟨33783568806811024251886151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90089516818162731338363069 33783568806811024251886151)
  ·
    refine ⟨50675353210216536377829227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33783568806811024251886151 50675353210216536377829227)
    ·
      refine ⟨76013029815324804566743841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50675353210216536377829227 76013029815324804566743841)
      ·
        refine ⟨57009772361493603425057881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76013029815324804566743841 57009772361493603425057881)
        ·
          refine ⟨42757329271120202568793411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57009772361493603425057881 42757329271120202568793411)
          ·
            refine ⟨64135993906680303853190117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42757329271120202568793411 64135993906680303853190117)
            ·
              refine ⟨12025498857502556972473147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64135993906680303853190117 12025498857502556972473147)
              ·
                refine ⟨18038248286253835458709721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12025498857502556972473147 18038248286253835458709721)
                ·
                  refine ⟨13528686214690376594032291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18038248286253835458709721 13528686214690376594032291)
                  ·
                    refine ⟨20293029322035564891048437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13528686214690376594032291 20293029322035564891048437)
                    ·
                      refine ⟨1902471498940834208535791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20293029322035564891048437 1902471498940834208535791)
                      ·
                        rfl

theorem cell23_3705050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_3705050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705050 prefixEnd_3705050 := by exact prefixLift 3705050
  have htrace : WordTrace (prefixWord ++ tailWord_3705050) baseStart_3705050 baseEnd_3705050 := by
    simpa [prefixWord, tailWord_3705050, baseEnd_3705050] using wordTrace_append hprefix tailTrace_3705050
  have hstable : (prefixWord ++ tailWord_3705050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705050).length < 2 ^ (prefixWord ++ tailWord_3705050).sum := by decide
  have hdescent : baseEnd_3705050 < baseStart_3705050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705060 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3705060 : Nat := 118140960795 + 3705060 * 2 ^ 59
def prefixEnd_3705060 : Nat := 4983230072969 + 3 ^ 40 * 3705060 * 2
def baseEnd_3705060 : Nat := 1902476633747379169410745

theorem tailTrace_3705060 : CollatzResearch.WordTrace tailWord_3705060 prefixEnd_3705060 1902476633747379169410745 := by
  unfold tailWord_3705060
  simp only [CollatzResearch.WordTrace]
  refine ⟨67567319978603934357704317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90089759971471912476939089 67567319978603934357704317)
  ·
    refine ⟨25337744991976475384139119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67567319978603934357704317 25337744991976475384139119)
    ·
      refine ⟨38006617487964713076208679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25337744991976475384139119 38006617487964713076208679)
      ·
        refine ⟨57009926231947069614313019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38006617487964713076208679 57009926231947069614313019)
        ·
          refine ⟨85514889347920604421469529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57009926231947069614313019 85514889347920604421469529)
          ·
            refine ⟨64136167010940453316102147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85514889347920604421469529 64136167010940453316102147)
            ·
              refine ⟨96204250516410679974153221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64136167010940453316102147 96204250516410679974153221)
              ·
                refine ⟨18038296971827002495153729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96204250516410679974153221 18038296971827002495153729)
                ·
                  refine ⟨13528722728870251871365297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18038296971827002495153729 13528722728870251871365297)
                  ·
                    refine ⟨10146542046652688903523973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13528722728870251871365297 10146542046652688903523973)
                    ·
                      refine ⟨1902476633747379169410745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10146542046652688903523973 1902476633747379169410745)
                      ·
                        rfl

theorem cell23_3705060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3705060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705060 prefixEnd_3705060 := by exact prefixLift 3705060
  have htrace : WordTrace (prefixWord ++ tailWord_3705060) baseStart_3705060 baseEnd_3705060 := by
    simpa [prefixWord, tailWord_3705060, baseEnd_3705060] using wordTrace_append hprefix tailTrace_3705060
  have hstable : (prefixWord ++ tailWord_3705060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705060).length < 2 ^ (prefixWord ++ tailWord_3705060).sum := by decide
  have hdescent : baseEnd_3705060 < baseStart_3705060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705070 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_3705070 : Nat := 118140960795 + 3705070 * 2 ^ 59
def prefixEnd_3705070 : Nat := 4983230072969 + 3 ^ 40 * 3705070 * 2
def baseEnd_3705070 : Nat := 211386863172658236698411

theorem tailTrace_3705070 : CollatzResearch.WordTrace tailWord_3705070 prefixEnd_3705070 211386863172658236698411 := by
  unfold tailWord_3705070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891875585896455052909083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90090003124781093615515109 16891875585896455052909083)
  ·
    refine ⟨25337813378844682579363625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16891875585896455052909083 25337813378844682579363625)
    ·
      refine ⟨19003360034133511934522719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25337813378844682579363625 19003360034133511934522719)
      ·
        refine ⟨28505040051200267901784079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19003360034133511934522719 28505040051200267901784079)
        ·
          refine ⟨42757560076800401852676119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28505040051200267901784079 42757560076800401852676119)
          ·
            refine ⟨64136340115200602779014179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42757560076800401852676119 64136340115200602779014179)
            ·
              refine ⟨96204510172800904168521269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64136340115200602779014179 96204510172800904168521269)
              ·
                refine ⟨9019172828700084765798869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96204510172800904168521269 9019172828700084765798869)
                ·
                  refine ⟨211386863172658236698411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9019172828700084765798869 211386863172658236698411)
                  ·
                    rfl

theorem cell23_3705070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_3705070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705070 prefixEnd_3705070 := by exact prefixLift 3705070
  have htrace : WordTrace (prefixWord ++ tailWord_3705070) baseStart_3705070 baseEnd_3705070 := by
    simpa [prefixWord, tailWord_3705070, baseEnd_3705070] using wordTrace_append hprefix tailTrace_3705070
  have hstable : (prefixWord ++ tailWord_3705070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705070).length < 2 ^ (prefixWord ++ tailWord_3705070).sum := by decide
  have hdescent : baseEnd_3705070 < baseStart_3705070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705100 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_3705100 : Nat := 118140960795 + 3705100 * 2 ^ 59
def prefixEnd_3705100 : Nat := 4983230072969 + 3 ^ 40 * 3705100 * 2
def baseEnd_3705100 : Nat := 634165724324519670970187

theorem tailTrace_3705100 : CollatzResearch.WordTrace tailWord_3705100 prefixEnd_3705100 634165724324519670970187 := by
  unfold tailWord_3705100
  simp only [CollatzResearch.WordTrace]
  refine ⟨67568049438531477773432377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90090732584708637031243169 67568049438531477773432377)
  ·
    refine ⟨50676037078898608330074283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67568049438531477773432377 50676037078898608330074283)
    ·
      refine ⟨76014055618347912495111425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50676037078898608330074283 76014055618347912495111425)
      ·
        refine ⟨57010541713760934371333569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76014055618347912495111425 57010541713760934371333569)
        ·
          refine ⟨42757906285320700778500177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57010541713760934371333569 42757906285320700778500177)
          ·
            refine ⟨32068429713990525583875133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42757906285320700778500177 32068429713990525583875133)
            ·
              refine ⟨12025661142746447093953175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32068429713990525583875133 12025661142746447093953175)
              ·
                refine ⟨18038491714119670640929763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12025661142746447093953175 18038491714119670640929763)
                ·
                  refine ⟨27057737571179505961394645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18038491714119670640929763 27057737571179505961394645)
                  ·
                    refine ⟨634165724324519670970187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27057737571179505961394645 634165724324519670970187)
                    ·
                      rfl

theorem cell23_3705100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_3705100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705100 prefixEnd_3705100 := by exact prefixLift 3705100
  have htrace : WordTrace (prefixWord ++ tailWord_3705100) baseStart_3705100 baseEnd_3705100 := by
    simpa [prefixWord, tailWord_3705100, baseEnd_3705100] using wordTrace_append hprefix tailTrace_3705100
  have hstable : (prefixWord ++ tailWord_3705100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705100).length < 2 ^ (prefixWord ++ tailWord_3705100).sum := by decide
  have hdescent : baseEnd_3705100 < baseStart_3705100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705160 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 8]
def baseStart_3705160 : Nat := 118140960795 + 3705160 * 2 ^ 59
def prefixEnd_3705160 : Nat := 4983230072969 + 3 ^ 40 * 3705160 * 2
def baseEnd_3705160 : Nat := 211391997979203197573365

theorem tailTrace_3705160 : CollatzResearch.WordTrace tailWord_3705160 prefixEnd_3705160 211391997979203197573365 := by
  unfold tailWord_3705160
  simp only [CollatzResearch.WordTrace]
  refine ⟨67569143628422792897024467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90092191504563723862699289 67569143628422792897024467)
  ·
    refine ⟨101353715442634189345536701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67569143628422792897024467 101353715442634189345536701)
    ·
      refine ⟨38007643290987821004576263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101353715442634189345536701 38007643290987821004576263)
      ·
        refine ⟨57011464936481731506864395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38007643290987821004576263 57011464936481731506864395)
        ·
          refine ⟨85517197404722597260296593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57011464936481731506864395 85517197404722597260296593)
          ·
            refine ⟨64137898053541947945222445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85517197404722597260296593 64137898053541947945222445)
            ·
              refine ⟨24051711770078230479458417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64137898053541947945222445 24051711770078230479458417)
              ·
                refine ⟨18038783827558672859593813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24051711770078230479458417 18038783827558672859593813)
                ·
                  refine ⟨211391997979203197573365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18038783827558672859593813 211391997979203197573365)
                  ·
                    rfl

theorem cell23_3705160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 8].length) (baseStart_3705160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705160 prefixEnd_3705160 := by exact prefixLift 3705160
  have htrace : WordTrace (prefixWord ++ tailWord_3705160) baseStart_3705160 baseEnd_3705160 := by
    simpa [prefixWord, tailWord_3705160, baseEnd_3705160] using wordTrace_append hprefix tailTrace_3705160
  have hstable : (prefixWord ++ tailWord_3705160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705160).length < 2 ^ (prefixWord ++ tailWord_3705160).sum := by decide
  have hdescent : baseEnd_3705160 < baseStart_3705160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705194 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 6]
def baseStart_3705194 : Nat := 118140960795 + 3705194 * 2 ^ 59
def prefixEnd_3705194 : Nat := 4983230072969 + 3 ^ 40 * 3705194 * 2
def baseEnd_3705194 : Nat := 211393937795009071681681

theorem tailTrace_3705194 : CollatzResearch.WordTrace tailWord_3705194 prefixEnd_3705194 211393937795009071681681 := by
  unfold tailWord_3705194
  simp only [CollatzResearch.WordTrace]
  refine ⟨33784881834680602400196659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90093018225814939733857757 33784881834680602400196659)
  ·
    refine ⟨50677322752020903600294989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33784881834680602400196659 50677322752020903600294989)
    ·
      refine ⟨19003996032007838850110621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50677322752020903600294989 19003996032007838850110621)
      ·
        refine ⟨7126498512002939568791483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19003996032007838850110621 7126498512002939568791483)
        ·
          refine ⟨10689747768004409353187225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7126498512002939568791483 10689747768004409353187225)
          ·
            refine ⟨8017310826003307014890419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10689747768004409353187225 8017310826003307014890419)
            ·
              refine ⟨12025966239004960522335629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8017310826003307014890419 12025966239004960522335629)
              ·
                refine ⟨4509737339626860195875861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12025966239004960522335629 4509737339626860195875861)
                ·
                  refine ⟨211393937795009071681681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4509737339626860195875861 211393937795009071681681)
                  ·
                    rfl

theorem cell23_3705194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_3705194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705194 prefixEnd_3705194 := by exact prefixLift 3705194
  have htrace : WordTrace (prefixWord ++ tailWord_3705194) baseStart_3705194 baseEnd_3705194 := by
    simpa [prefixWord, tailWord_3705194, baseEnd_3705194] using wordTrace_append hprefix tailTrace_3705194
  have hstable : (prefixWord ++ tailWord_3705194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705194).length < 2 ^ (prefixWord ++ tailWord_3705194).sum := by decide
  have hdescent : baseEnd_3705194 < baseStart_3705194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705207 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 1, 5]
def baseStart_3705207 : Nat := 118140960795 + 3705207 * 2 ^ 59
def prefixEnd_3705207 : Nat := 4983230072969 + 3 ^ 40 * 3705207 * 2
def baseEnd_3705207 : Nat := 634184038467863364757523

theorem tailTrace_3705207 : CollatzResearch.WordTrace tailWord_3705207 prefixEnd_3705207 634184038467863364757523 := by
  unfold tailWord_3705207
  simp only [CollatzResearch.WordTrace]
  refine ⟨135140001487675312821009875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90093334325116875214006583 135140001487675312821009875)
  ·
    refine ⟨202710002231512969231514813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135140001487675312821009875 202710002231512969231514813)
    ·
      refine ⟨76016250836817363461818055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202710002231512969231514813 76016250836817363461818055)
      ·
        refine ⟨114024376255226045192727083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76016250836817363461818055 114024376255226045192727083)
        ·
          refine ⟨171036564382839067789090625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114024376255226045192727083 171036564382839067789090625)
          ·
            refine ⟨128277423287129300841817969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171036564382839067789090625 128277423287129300841817969)
            ·
              refine ⟨96208067465346975631363477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128277423287129300841817969 96208067465346975631363477)
              ·
                refine ⟨4509753162438139482720163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96208067465346975631363477 4509753162438139482720163)
                ·
                  refine ⟨6764629743657209224080245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509753162438139482720163 6764629743657209224080245)
                  ·
                    refine ⟨634184038467863364757523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6764629743657209224080245 634184038467863364757523)
                    ·
                      rfl

theorem cell23_3705207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_3705207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705207 prefixEnd_3705207 := by exact prefixLift 3705207
  have htrace : WordTrace (prefixWord ++ tailWord_3705207) baseStart_3705207 baseEnd_3705207 := by
    simpa [prefixWord, tailWord_3705207, baseEnd_3705207] using wordTrace_append hprefix tailTrace_3705207
  have hstable : (prefixWord ++ tailWord_3705207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705207).length < 2 ^ (prefixWord ++ tailWord_3705207).sum := by decide
  have hdescent : baseEnd_3705207 < baseStart_3705207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705221 : List Nat := [1, 3, 1, 1, 3, 1, 1, 7, 1, 1, 3]
def baseStart_3705221 : Nat := 118140960795 + 3705221 * 2 ^ 59
def prefixEnd_3705221 : Nat := 4983230072969 + 3 ^ 40 * 3705221 * 2
def baseEnd_3705221 : Nat := 1902559304132753039497505

theorem tailTrace_3705221 : CollatzResearch.WordTrace tailWord_3705221 prefixEnd_3705221 1902559304132753039497505 := by
  unfold tailWord_3705221
  simp only [CollatzResearch.WordTrace]
  refine ⟨135140512109624593212019517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90093674739749728808013011 135140512109624593212019517)
  ·
    refine ⟨50677692041109222454507319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135140512109624593212019517 50677692041109222454507319)
    ·
      refine ⟨76016538061663833681760979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50677692041109222454507319 76016538061663833681760979)
      ·
        refine ⟨114024807092495750522641469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76016538061663833681760979 114024807092495750522641469)
        ·
          refine ⟨42759302659685906445990551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114024807092495750522641469 42759302659685906445990551)
          ·
            refine ⟨64138953989528859668985827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42759302659685906445990551 64138953989528859668985827)
            ·
              refine ⟨96208430984293289503478741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64138953989528859668985827 96208430984293289503478741)
              ·
                refine ⟨2254885101194373972737783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96208430984293289503478741 2254885101194373972737783)
                ·
                  refine ⟨3382327651791560959106675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254885101194373972737783 3382327651791560959106675)
                  ·
                    refine ⟨5073491477687341438660013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382327651791560959106675 5073491477687341438660013)
                    ·
                      refine ⟨1902559304132753039497505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5073491477687341438660013 1902559304132753039497505)
                      ·
                        rfl

theorem cell23_3705221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 1, 1, 3].length) (baseStart_3705221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705221 prefixEnd_3705221 := by exact prefixLift 3705221
  have htrace : WordTrace (prefixWord ++ tailWord_3705221) baseStart_3705221 baseEnd_3705221 := by
    simpa [prefixWord, tailWord_3705221, baseEnd_3705221] using wordTrace_append hprefix tailTrace_3705221
  have hstable : (prefixWord ++ tailWord_3705221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705221).length < 2 ^ (prefixWord ++ tailWord_3705221).sum := by decide
  have hdescent : baseEnd_3705221 < baseStart_3705221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705247 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3705247 : Nat := 118140960795 + 3705247 * 2 ^ 59
def prefixEnd_3705247 : Nat := 4983230072969 + 3 ^ 40 * 3705247 * 2
def baseEnd_3705247 : Nat := 1902572654629769937772385

theorem tailTrace_3705247 : CollatzResearch.WordTrace tailWord_3705247 prefixEnd_3705247 1902572654629769937772385 := by
  unfold tailWord_3705247
  simp only [CollatzResearch.WordTrace]
  refine ⟨135141460407530399652465995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90094306938353599768310663 135141460407530399652465995)
  ·
    refine ⟨202712190611295599478698993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135141460407530399652465995 202712190611295599478698993)
    ·
      refine ⟨152034142958471699609024245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202712190611295599478698993 152034142958471699609024245)
      ·
        refine ⟨14253200902356721838346023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152034142958471699609024245 14253200902356721838346023)
        ·
          refine ⟨21379801353535082757519035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14253200902356721838346023 21379801353535082757519035)
          ·
            refine ⟨32069702030302624136278553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21379801353535082757519035 32069702030302624136278553)
            ·
              refine ⟨24052276522726968102208915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32069702030302624136278553 24052276522726968102208915)
              ·
                refine ⟨36078414784090452153313373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24052276522726968102208915 36078414784090452153313373)
                ·
                  refine ⟨13529405544033919557492515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36078414784090452153313373 13529405544033919557492515)
                  ·
                    refine ⟨20294108316050879336238773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13529405544033919557492515 20294108316050879336238773)
                    ·
                      refine ⟨1902572654629769937772385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20294108316050879336238773 1902572654629769937772385)
                      ·
                        rfl

theorem cell23_3705247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3705247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705247 prefixEnd_3705247 := by exact prefixLift 3705247
  have htrace : WordTrace (prefixWord ++ tailWord_3705247) baseStart_3705247 baseEnd_3705247 := by
    simpa [prefixWord, tailWord_3705247, baseEnd_3705247] using wordTrace_append hprefix tailTrace_3705247
  have hstable : (prefixWord ++ tailWord_3705247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705247).length < 2 ^ (prefixWord ++ tailWord_3705247).sum := by decide
  have hdescent : baseEnd_3705247 < baseStart_3705247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705284 : List Nat := [2, 3, 3, 2, 2, 1, 10]
def baseStart_3705284 : Nat := 118140960795 + 3705284 * 2 ^ 59
def prefixEnd_3705284 : Nat := 4983230072969 + 3 ^ 40 * 3705284 * 2
def baseEnd_3705284 : Nat := 23488785844617114728515

theorem tailTrace_3705284 : CollatzResearch.WordTrace tailWord_3705284 prefixEnd_3705284 23488785844617114728515 := by
  unfold tailWord_3705284
  simp only [CollatzResearch.WordTrace]
  refine ⟨67571404954198177485781453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90095206605597569981041937 67571404954198177485781453)
  ·
    refine ⟨25339276857824316557168045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67571404954198177485781453 25339276857824316557168045)
    ·
      refine ⟨9502228821684118708938017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25339276857824316557168045 9502228821684118708938017)
      ·
        refine ⟨7126671616263089031703513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9502228821684118708938017 7126671616263089031703513)
        ·
          refine ⟨5345003712197316773777635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7126671616263089031703513 5345003712197316773777635)
          ·
            refine ⟨8017505568295975160666453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345003712197316773777635 8017505568295975160666453)
            ·
              refine ⟨23488785844617114728515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8017505568295975160666453 23488785844617114728515)
              ·
                rfl

theorem cell23_3705284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 10].length) (baseStart_3705284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705284 prefixEnd_3705284 := by exact prefixLift 3705284
  have htrace : WordTrace (prefixWord ++ tailWord_3705284) baseStart_3705284 baseEnd_3705284 := by
    simpa [prefixWord, tailWord_3705284, baseEnd_3705284] using wordTrace_append hprefix tailTrace_3705284
  have hstable : (prefixWord ++ tailWord_3705284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705284).length < 2 ^ (prefixWord ++ tailWord_3705284).sum := by decide
  have hdescent : baseEnd_3705284 < baseStart_3705284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705311 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 1, 3, 3]
def baseStart_3705311 : Nat := 118140960795 + 3705311 * 2 ^ 59
def prefixEnd_3705311 : Nat := 4983230072969 + 3 ^ 40 * 3705311 * 2
def baseEnd_3705311 : Nat := 1902605517391657687372091

theorem tailTrace_3705311 : CollatzResearch.WordTrace tailWord_3705311 prefixEnd_3705311 1902605517391657687372091 := by
  unfold tailWord_3705311
  simp only [CollatzResearch.WordTrace]
  refine ⟨135143794679298538582795787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90095863119532359055197191 135143794679298538582795787)
  ·
    refine ⟨202715692018947807874193681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135143794679298538582795787 202715692018947807874193681)
    ·
      refine ⟨152036769014210855905645261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202715692018947807874193681 152036769014210855905645261)
      ·
        refine ⟨57013788380329070964616973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152036769014210855905645261 57013788380329070964616973)
        ·
          refine ⟨21380170642623401611731365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57013788380329070964616973 21380170642623401611731365)
          ·
            refine ⟨4008781995491887802199631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21380170642623401611731365 4008781995491887802199631)
            ·
              refine ⟨6013172993237831703299447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4008781995491887802199631 6013172993237831703299447)
              ·
                refine ⟨9019759489856747554949171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6013172993237831703299447 9019759489856747554949171)
                ·
                  refine ⟨13529639234785121332423757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9019759489856747554949171 13529639234785121332423757)
                  ·
                    refine ⟨5073614713044420499658909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13529639234785121332423757 5073614713044420499658909)
                    ·
                      refine ⟨1902605517391657687372091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5073614713044420499658909 1902605517391657687372091)
                      ·
                        rfl

theorem cell23_3705311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_3705311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705311 prefixEnd_3705311 := by exact prefixLift 3705311
  have htrace : WordTrace (prefixWord ++ tailWord_3705311) baseStart_3705311 baseEnd_3705311 := by
    simpa [prefixWord, tailWord_3705311, baseEnd_3705311] using wordTrace_append hprefix tailTrace_3705311
  have hstable : (prefixWord ++ tailWord_3705311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705311).length < 2 ^ (prefixWord ++ tailWord_3705311).sum := by decide
  have hdescent : baseEnd_3705311 < baseStart_3705311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705337 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_3705337 : Nat := 118140960795 + 3705337 * 2 ^ 59
def prefixEnd_3705337 : Nat := 4983230072969 + 3 ^ 40 * 3705337 * 2
def baseEnd_3705337 : Nat := 1902618867888674585646971

theorem tailTrace_3705337 : CollatzResearch.WordTrace tailWord_3705337 prefixEnd_3705337 1902618867888674585646971 := by
  unfold tailWord_3705337
  simp only [CollatzResearch.WordTrace]
  refine ⟨135144742977204345023242265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90096495318136230015494843 135144742977204345023242265)
  ·
    refine ⟨101358557232903258767431699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135144742977204345023242265 101358557232903258767431699)
    ·
      refine ⟨152037835849354888151147549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101358557232903258767431699 152037835849354888151147549)
      ·
        refine ⟨57014188443508083056680331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152037835849354888151147549 57014188443508083056680331)
        ·
          refine ⟨85521282665262124585020497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57014188443508083056680331 85521282665262124585020497)
          ·
            refine ⟨64140961998946593438765373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85521282665262124585020497 64140961998946593438765373)
            ·
              refine ⟨24052860749604972539537015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64140961998946593438765373 24052860749604972539537015)
              ·
                refine ⟨36079291124407458809305523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24052860749604972539537015 36079291124407458809305523)
                ·
                  refine ⟨54118936686611188213958285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36079291124407458809305523 54118936686611188213958285)
                  ·
                    refine ⟨20294601257479195580234357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54118936686611188213958285 20294601257479195580234357)
                    ·
                      refine ⟨1902618867888674585646971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20294601257479195580234357 1902618867888674585646971)
                      ·
                        rfl

theorem cell23_3705337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_3705337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705337 prefixEnd_3705337 := by exact prefixLift 3705337
  have htrace : WordTrace (prefixWord ++ tailWord_3705337) baseStart_3705337 baseEnd_3705337 := by
    simpa [prefixWord, tailWord_3705337, baseEnd_3705337] using wordTrace_append hprefix tailTrace_3705337
  have hstable : (prefixWord ++ tailWord_3705337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705337).length < 2 ^ (prefixWord ++ tailWord_3705337).sum := by decide
  have hdescent : baseEnd_3705337 < baseStart_3705337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705354 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_3705354 : Nat := 118140960795 + 3705354 * 2 ^ 59
def prefixEnd_3705354 : Nat := 4983230072969 + 3 ^ 40 * 3705354 * 2
def baseEnd_3705354 : Nat := 1902627597059801019134393

theorem tailTrace_3705354 : CollatzResearch.WordTrace tailWord_3705354 prefixEnd_3705354 1902627597059801019134393 := by
  unfold tailWord_3705354
  simp only [CollatzResearch.WordTrace]
  refine ⟨33786340754535689231652779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90096908678761837951074077 33786340754535689231652779)
  ·
    refine ⟨50679511131803533847479169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33786340754535689231652779 50679511131803533847479169)
    ·
      refine ⟨38009633348852650385609377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50679511131803533847479169 38009633348852650385609377)
      ·
        refine ⟨28507225011639487789207033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38009633348852650385609377 28507225011639487789207033)
        ·
          refine ⟨21380418758729615841905275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28507225011639487789207033 21380418758729615841905275)
          ·
            refine ⟨32070628138094423762857913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21380418758729615841905275 32070628138094423762857913)
            ·
              refine ⟨24052971103570817822143435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32070628138094423762857913 24052971103570817822143435)
              ·
                refine ⟨36079456655356226733215153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24052971103570817822143435 36079456655356226733215153)
                ·
                  refine ⟨27059592491517170049911365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36079456655356226733215153 27059592491517170049911365)
                  ·
                    refine ⟨5073673592159469384358381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27059592491517170049911365 5073673592159469384358381)
                    ·
                      refine ⟨1902627597059801019134393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5073673592159469384358381 1902627597059801019134393)
                      ·
                        rfl

theorem cell23_3705354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_3705354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705354 prefixEnd_3705354 := by exact prefixLift 3705354
  have htrace : WordTrace (prefixWord ++ tailWord_3705354) baseStart_3705354 baseEnd_3705354 := by
    simpa [prefixWord, tailWord_3705354, baseEnd_3705354] using wordTrace_append hprefix tailTrace_3705354
  have hstable : (prefixWord ++ tailWord_3705354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705354).length < 2 ^ (prefixWord ++ tailWord_3705354).sum := by decide
  have hdescent : baseEnd_3705354 < baseStart_3705354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705387 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 1, 7]
def baseStart_3705387 : Nat := 118140960795 + 3705387 * 2 ^ 59
def prefixEnd_3705387 : Nat := 4983230072969 + 3 ^ 40 * 3705387 * 2
def baseEnd_3705387 : Nat := 634214847307133130007247

theorem tailTrace_3705387 : CollatzResearch.WordTrace tailWord_3705387 prefixEnd_3705387 634214847307133130007247 := by
  unfold tailWord_3705387
  simp only [CollatzResearch.WordTrace]
  refine ⟨135146566627023203562562415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90097711084682135708374943 135146566627023203562562415)
  ·
    refine ⟨202719849940534805343843623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135146566627023203562562415 202719849940534805343843623)
    ·
      refine ⟨304079774910802208015765435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202719849940534805343843623 304079774910802208015765435)
      ·
        refine ⟨456119662366203312023648153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304079774910802208015765435 456119662366203312023648153)
        ·
          refine ⟨342089746774652484017736115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456119662366203312023648153 342089746774652484017736115)
          ·
            refine ⟨513134620161978726026604173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342089746774652484017736115 513134620161978726026604173)
            ·
              refine ⟨192425482560742022259976565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 513134620161978726026604173 192425482560742022259976565)
              ·
                refine ⟨18039888990069564586872803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192425482560742022259976565 18039888990069564586872803)
                ·
                  refine ⟨27059833485104346880309205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18039888990069564586872803 27059833485104346880309205)
                  ·
                    refine ⟨634214847307133130007247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27059833485104346880309205 634214847307133130007247)
                    ·
                      rfl

theorem cell23_3705387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 7].length) (baseStart_3705387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705387 prefixEnd_3705387 := by exact prefixLift 3705387
  have htrace : WordTrace (prefixWord ++ tailWord_3705387) baseStart_3705387 baseEnd_3705387 := by
    simpa [prefixWord, tailWord_3705387, baseEnd_3705387] using wordTrace_append hprefix tailTrace_3705387
  have hstable : (prefixWord ++ tailWord_3705387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705387).length < 2 ^ (prefixWord ++ tailWord_3705387).sum := by decide
  have hdescent : baseEnd_3705387 < baseStart_3705387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705417 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 4, 8]
def baseStart_3705417 : Nat := 118140960795 + 3705417 * 2 ^ 59
def prefixEnd_3705417 : Nat := 4983230072969 + 3 ^ 40 * 3705417 * 2
def baseEnd_3705417 : Nat := 634219982113678090882201

theorem tailTrace_3705417 : CollatzResearch.WordTrace tailWord_3705417 prefixEnd_3705417 634219982113678090882201 := by
  unfold tailWord_3705417
  simp only [CollatzResearch.WordTrace]
  refine ⟨135147660816914518686154505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90098440544609679124103003 135147660816914518686154505)
  ·
    refine ⟨101360745612685889014615879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135147660816914518686154505 101360745612685889014615879)
    ·
      refine ⟨152041118419028833521923819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101360745612685889014615879 152041118419028833521923819)
      ·
        refine ⟨228061677628543250282885729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152041118419028833521923819 228061677628543250282885729)
        ·
          refine ⟨171046258221407437712164297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228061677628543250282885729 171046258221407437712164297)
          ·
            refine ⟨128284693666055578284123223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171046258221407437712164297 128284693666055578284123223)
            ·
              refine ⟨192427040499083367426184835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128284693666055578284123223 192427040499083367426184835)
              ·
                refine ⟨288640560748625051139277253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192427040499083367426184835 288640560748625051139277253)
                ·
                  refine ⟨54120105140367197088614485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288640560748625051139277253 54120105140367197088614485)
                  ·
                    refine ⟨634219982113678090882201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54120105140367197088614485 634219982113678090882201)
                    ·
                      rfl

theorem cell23_3705417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_3705417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705417 prefixEnd_3705417 := by exact prefixLift 3705417
  have htrace : WordTrace (prefixWord ++ tailWord_3705417) baseStart_3705417 baseEnd_3705417 := by
    simpa [prefixWord, tailWord_3705417, baseEnd_3705417] using wordTrace_append hprefix tailTrace_3705417
  have hstable : (prefixWord ++ tailWord_3705417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705417).length < 2 ^ (prefixWord ++ tailWord_3705417).sum := by decide
  have hdescent : baseEnd_3705417 < baseStart_3705417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705441 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_3705441 : Nat := 118140960795 + 3705441 * 2 ^ 59
def prefixEnd_3705441 : Nat := 4983230072969 + 3 ^ 40 * 3705441 * 2
def baseEnd_3705441 : Nat := 1902672269876742178746493

theorem tailTrace_3705441 : CollatzResearch.WordTrace tailWord_3705441 prefixEnd_3705441 1902672269876742178746493 := by
  unfold tailWord_3705441
  simp only [CollatzResearch.WordTrace]
  refine ⟨135148536168827570785028177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90099024112551713856685451 135148536168827570785028177)
  ·
    refine ⟨101361402126620678088771133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135148536168827570785028177 101361402126620678088771133)
    ·
      refine ⟨38010525797482754283289175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101361402126620678088771133 38010525797482754283289175)
      ·
        refine ⟨57015788696224131424933763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38010525797482754283289175 57015788696224131424933763)
        ·
          refine ⟨85523683044336197137400645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57015788696224131424933763 85523683044336197137400645)
          ·
            refine ⟨16035690570813036963262621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85523683044336197137400645 16035690570813036963262621)
            ·
              refine ⟨6013383964054888861223483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16035690570813036963262621 6013383964054888861223483)
              ·
                refine ⟨9020075946082333291835225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6013383964054888861223483 9020075946082333291835225)
                ·
                  refine ⟨6765056959561749968876419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9020075946082333291835225 6765056959561749968876419)
                  ·
                    refine ⟨10147585439342624953314629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6765056959561749968876419 10147585439342624953314629)
                    ·
                      refine ⟨1902672269876742178746493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10147585439342624953314629 1902672269876742178746493)
                      ·
                        rfl

theorem cell23_3705441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_3705441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705441 prefixEnd_3705441 := by exact prefixLift 3705441
  have htrace : WordTrace (prefixWord ++ tailWord_3705441) baseStart_3705441 baseEnd_3705441 := by
    simpa [prefixWord, tailWord_3705441, baseEnd_3705441] using wordTrace_append hprefix tailTrace_3705441
  have hstable : (prefixWord ++ tailWord_3705441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705441).length < 2 ^ (prefixWord ++ tailWord_3705441).sum := by decide
  have hdescent : baseEnd_3705441 < baseStart_3705441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705468 : List Nat := [2, 2, 2, 1, 1, 2, 4, 4, 1, 4]
def baseStart_3705468 : Nat := 118140960795 + 3705468 * 2 ^ 59
def prefixEnd_3705468 : Nat := 4983230072969 + 3 ^ 40 * 3705468 * 2
def baseEnd_3705468 : Nat := 634228711284804524369623

theorem tailTrace_3705468 : CollatzResearch.WordTrace tailWord_3705468 prefixEnd_3705468 634228711284804524369623 := by
  unfold tailWord_3705468
  simp only [CollatzResearch.WordTrace]
  refine ⟨67574760469864877198130529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90099680626486502930840705 67574760469864877198130529)
  ·
    refine ⟨50681070352398657898597897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67574760469864877198130529 50681070352398657898597897)
    ·
      refine ⟨38010802764298993423948423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50681070352398657898597897 38010802764298993423948423)
      ·
        refine ⟨57016204146448490135922635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38010802764298993423948423 57016204146448490135922635)
        ·
          refine ⟨85524306219672735203883953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57016204146448490135922635 85524306219672735203883953)
          ·
            refine ⟨64143229664754551402912965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85524306219672735203883953 64143229664754551402912965)
            ·
              refine ⟨12026855562141478388046181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64143229664754551402912965 12026855562141478388046181)
              ·
                refine ⟨2255035417901527197758659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12026855562141478388046181 2255035417901527197758659)
                ·
                  refine ⟨3382553126852290796637989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255035417901527197758659 3382553126852290796637989)
                  ·
                    refine ⟨634228711284804524369623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3382553126852290796637989 634228711284804524369623)
                    ·
                      rfl

theorem cell23_3705468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_3705468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705468 prefixEnd_3705468 := by exact prefixLift 3705468
  have htrace : WordTrace (prefixWord ++ tailWord_3705468) baseStart_3705468 baseEnd_3705468 := by
    simpa [prefixWord, tailWord_3705468, baseEnd_3705468] using wordTrace_append hprefix tailTrace_3705468
  have hstable : (prefixWord ++ tailWord_3705468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705468).length < 2 ^ (prefixWord ++ tailWord_3705468).sum := by decide
  have hdescent : baseEnd_3705468 < baseStart_3705468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705525 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3705525 : Nat := 118140960795 + 3705525 * 2 ^ 59
def prefixEnd_3705525 : Nat := 4983230072969 + 3 ^ 40 * 3705525 * 2
def baseEnd_3705525 : Nat := 1902715402251719850096107

theorem tailTrace_3705525 : CollatzResearch.WordTrace tailWord_3705525 prefixEnd_3705525 1902715402251719850096107 := by
  unfold tailWord_3705525
  simp only [CollatzResearch.WordTrace]
  refine ⟨135151599900523253131086029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90101066600348835420724019 135151599900523253131086029)
  ·
    refine ⟨50681849962696219924157261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135151599900523253131086029 50681849962696219924157261)
    ·
      refine ⟨19005693736011082471558973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50681849962696219924157261 19005693736011082471558973)
      ·
        refine ⟨7127135151004155926834615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19005693736011082471558973 7127135151004155926834615)
        ·
          refine ⟨10690702726506233890251923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127135151004155926834615 10690702726506233890251923)
          ·
            refine ⟨16036054089759350835377885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10690702726506233890251923 16036054089759350835377885)
            ·
              refine ⟨6013520283659756563266707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16036054089759350835377885 6013520283659756563266707)
              ·
                refine ⟨9020280425489634844900061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6013520283659756563266707 9020280425489634844900061)
                ·
                  refine ⟨3382605159558613066837523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9020280425489634844900061 3382605159558613066837523)
                  ·
                    refine ⟨5073907739337919600256285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382605159558613066837523 5073907739337919600256285)
                    ·
                      refine ⟨1902715402251719850096107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5073907739337919600256285 1902715402251719850096107)
                      ·
                        rfl

theorem cell23_3705525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3705525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705525 prefixEnd_3705525 := by exact prefixLift 3705525
  have htrace : WordTrace (prefixWord ++ tailWord_3705525) baseStart_3705525 baseEnd_3705525 := by
    simpa [prefixWord, tailWord_3705525, baseEnd_3705525] using wordTrace_append hprefix tailTrace_3705525
  have hstable : (prefixWord ++ tailWord_3705525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705525).length < 2 ^ (prefixWord ++ tailWord_3705525).sum := by decide
  have hdescent : baseEnd_3705525 < baseStart_3705525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705548 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3705548 : Nat := 118140960795 + 3705548 * 2 ^ 59
def prefixEnd_3705548 : Nat := 4983230072969 + 3 ^ 40 * 3705548 * 2
def baseEnd_3705548 : Nat := 1902727212306773260108501

theorem tailTrace_3705548 : CollatzResearch.WordTrace tailWord_3705548 prefixEnd_3705548 1902727212306773260108501 := by
  unfold tailWord_3705548
  simp only [CollatzResearch.WordTrace]
  refine ⟨67576219389719964029586649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90101625852959952039448865 67576219389719964029586649)
  ·
    refine ⟨50682164542289973022189987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67576219389719964029586649 50682164542289973022189987)
    ·
      refine ⟨76023246813434959533284981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50682164542289973022189987 76023246813434959533284981)
      ·
        refine ⟨7127179388759527456245467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76023246813434959533284981 7127179388759527456245467)
        ·
          refine ⟨10690769083139291184368201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127179388759527456245467 10690769083139291184368201)
          ·
            refine ⟨8018076812354468388276151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10690769083139291184368201 8018076812354468388276151)
            ·
              refine ⟨12027115218531702582414227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018076812354468388276151 12027115218531702582414227)
              ·
                refine ⟨18040672827797553873621341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12027115218531702582414227 18040672827797553873621341)
                ·
                  refine ⟨6765252310424082702608003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18040672827797553873621341 6765252310424082702608003)
                  ·
                    refine ⟨10147878465636124053912005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6765252310424082702608003 10147878465636124053912005)
                    ·
                      refine ⟨1902727212306773260108501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10147878465636124053912005 1902727212306773260108501)
                      ·
                        rfl

theorem cell23_3705548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3705548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705548 prefixEnd_3705548 := by exact prefixLift 3705548
  have htrace : WordTrace (prefixWord ++ tailWord_3705548) baseStart_3705548 baseEnd_3705548 := by
    simpa [prefixWord, tailWord_3705548, baseEnd_3705548] using wordTrace_append hprefix tailTrace_3705548
  have hstable : (prefixWord ++ tailWord_3705548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705548).length < 2 ^ (prefixWord ++ tailWord_3705548).sum := by decide
  have hdescent : baseEnd_3705548 < baseStart_3705548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705561 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 4]
def baseStart_3705561 : Nat := 118140960795 + 3705561 * 2 ^ 59
def prefixEnd_3705561 : Nat := 4983230072969 + 3 ^ 40 * 3705561 * 2
def baseEnd_3705561 : Nat := 1902733887555281709245941

theorem tailTrace_3705561 : CollatzResearch.WordTrace tailWord_3705561 prefixEnd_3705561 1902733887555281709245941 := by
  unfold tailWord_3705561
  simp only [CollatzResearch.WordTrace]
  refine ⟨135152912928392831279396537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90101941952261887519597691 135152912928392831279396537)
  ·
    refine ⟨101364684696294623459547403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135152912928392831279396537 101364684696294623459547403)
    ·
      refine ⟨152047027044441935189321105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101364684696294623459547403 152047027044441935189321105)
      ·
        refine ⟨114035270283331451391990829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152047027044441935189321105 114035270283331451391990829)
        ·
          refine ⟨42763226356249294271996561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114035270283331451391990829 42763226356249294271996561)
          ·
            refine ⟨32072419767186970703997421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42763226356249294271996561 32072419767186970703997421)
            ·
              refine ⟨12027157412695114013999033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32072419767186970703997421 12027157412695114013999033)
              ·
                refine ⟨9020368059521335510499275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12027157412695114013999033 9020368059521335510499275)
                ·
                  refine ⟨13530552089282003265748913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9020368059521335510499275 13530552089282003265748913)
                  ·
                    refine ⟨10147914066961502449311685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13530552089282003265748913 10147914066961502449311685)
                    ·
                      refine ⟨1902733887555281709245941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10147914066961502449311685 1902733887555281709245941)
                      ·
                        rfl

theorem cell23_3705561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_3705561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705561 prefixEnd_3705561 := by exact prefixLift 3705561
  have htrace : WordTrace (prefixWord ++ tailWord_3705561) baseStart_3705561 baseEnd_3705561 := by
    simpa [prefixWord, tailWord_3705561, baseEnd_3705561] using wordTrace_append hprefix tailTrace_3705561
  have hstable : (prefixWord ++ tailWord_3705561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705561).length < 2 ^ (prefixWord ++ tailWord_3705561).sum := by decide
  have hdescent : baseEnd_3705561 < baseStart_3705561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705576 : List Nat := [2, 1, 4, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_3705576 : Nat := 118140960795 + 3705576 * 2 ^ 59
def prefixEnd_3705576 : Nat := 4983230072969 + 3 ^ 40 * 3705576 * 2
def baseEnd_3705576 : Nat := 1902741589765099150558373

theorem tailTrace_3705576 : CollatzResearch.WordTrace tailWord_3705576 prefixEnd_3705576 1902741589765099150558373 := by
  unfold tailWord_3705576
  simp only [CollatzResearch.WordTrace]
  refine ⟨67576730011669244420596291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90102306682225659227461721 67576730011669244420596291)
  ·
    refine ⟨101365095017503866630894437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67576730011669244420596291 101365095017503866630894437)
    ·
      refine ⟨19005955315781974993292707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101365095017503866630894437 19005955315781974993292707)
      ·
        refine ⟨28508932973672962489939061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19005955315781974993292707 28508932973672962489939061)
        ·
          refine ⟨2672712466281840233431787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28508932973672962489939061 2672712466281840233431787)
          ·
            refine ⟨4009068699422760350147681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672712466281840233431787 4009068699422760350147681)
            ·
              refine ⟨3006801524567070262610761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4009068699422760350147681 3006801524567070262610761)
              ·
                refine ⟨2255101143425302696958071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006801524567070262610761 2255101143425302696958071)
                ·
                  refine ⟨3382651715137954045437107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255101143425302696958071 3382651715137954045437107)
                  ·
                    refine ⟨5073977572706931068155661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382651715137954045437107 5073977572706931068155661)
                    ·
                      refine ⟨1902741589765099150558373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5073977572706931068155661 1902741589765099150558373)
                      ·
                        rfl

theorem cell23_3705576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_3705576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705576 prefixEnd_3705576 := by exact prefixLift 3705576
  have htrace : WordTrace (prefixWord ++ tailWord_3705576) baseStart_3705576 baseEnd_3705576 := by
    simpa [prefixWord, tailWord_3705576, baseEnd_3705576] using wordTrace_append hprefix tailTrace_3705576
  have hstable : (prefixWord ++ tailWord_3705576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705576).length < 2 ^ (prefixWord ++ tailWord_3705576).sum := by decide
  have hdescent : baseEnd_3705576 < baseStart_3705576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705584 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 1, 9]
def baseStart_3705584 : Nat := 118140960795 + 3705584 * 2 ^ 59
def prefixEnd_3705584 : Nat := 4983230072969 + 3 ^ 40 * 3705584 * 2
def baseEnd_3705584 : Nat := 634248565870111706419445

theorem tailTrace_3705584 : CollatzResearch.WordTrace tailWord_3705584 prefixEnd_3705584 634248565870111706419445 := by
  unfold tailWord_3705584
  simp only [CollatzResearch.WordTrace]
  refine ⟨67576875903654753103741903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90102501204873004138322537 67576875903654753103741903)
  ·
    refine ⟨101365313855482129655612855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67576875903654753103741903 101365313855482129655612855)
    ·
      refine ⟨152047970783223194483419283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101365313855482129655612855 152047970783223194483419283)
      ·
        refine ⟨228071956174834791725128925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152047970783223194483419283 228071956174834791725128925)
        ·
          refine ⟨85526983565563046896923347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228071956174834791725128925 85526983565563046896923347)
          ·
            refine ⟨128290475348344570345385021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85526983565563046896923347 128290475348344570345385021)
            ·
              refine ⟨48108928255629213879519383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128290475348344570345385021 48108928255629213879519383)
              ·
                refine ⟨72163392383443820819279075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48108928255629213879519383 72163392383443820819279075)
                ·
                  refine ⟨108245088575165731228918613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72163392383443820819279075 108245088575165731228918613)
                  ·
                    refine ⟨634248565870111706419445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 108245088575165731228918613 634248565870111706419445)
                    ·
                      rfl

theorem cell23_3705584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_3705584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705584 prefixEnd_3705584 := by exact prefixLift 3705584
  have htrace : WordTrace (prefixWord ++ tailWord_3705584) baseStart_3705584 baseEnd_3705584 := by
    simpa [prefixWord, tailWord_3705584, baseEnd_3705584] using wordTrace_append hprefix tailTrace_3705584
  have hstable : (prefixWord ++ tailWord_3705584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705584).length < 2 ^ (prefixWord ++ tailWord_3705584).sum := by decide
  have hdescent : baseEnd_3705584 < baseStart_3705584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705631 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 2, 6]
def baseStart_3705631 : Nat := 118140960795 + 3705631 * 2 ^ 59
def prefixEnd_3705631 : Nat := 4983230072969 + 3 ^ 40 * 3705631 * 2
def baseEnd_3705631 : Nat := 634256610400365478456873

theorem tailTrace_3705631 : CollatzResearch.WordTrace tailWord_3705631 prefixEnd_3705631 634256610400365478456873 := by
  unfold tailWord_3705631
  simp only [CollatzResearch.WordTrace]
  refine ⟨135155466038139233234444747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90103644025426155489629831 135155466038139233234444747)
  ·
    refine ⟨202733199057208849851667121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135155466038139233234444747 202733199057208849851667121)
    ·
      refine ⟨152049899292906637388750341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202733199057208849851667121 152049899292906637388750341)
      ·
        refine ⟨28509356117419994510390689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152049899292906637388750341 28509356117419994510390689)
        ·
          refine ⟨21382017088064995882793017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28509356117419994510390689 21382017088064995882793017)
          ·
            refine ⟨16036512816048746912094763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21382017088064995882793017 16036512816048746912094763)
            ·
              refine ⟨24054769224073120368142145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16036512816048746912094763 24054769224073120368142145)
              ·
                refine ⟨18041076918054840276106609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24054769224073120368142145 18041076918054840276106609)
                ·
                  refine ⟨13530807688541130207079957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18041076918054840276106609 13530807688541130207079957)
                  ·
                    refine ⟨634256610400365478456873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13530807688541130207079957 634256610400365478456873)
                    ·
                      rfl

theorem cell23_3705631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_3705631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705631 prefixEnd_3705631 := by exact prefixLift 3705631
  have htrace : WordTrace (prefixWord ++ tailWord_3705631) baseStart_3705631 baseEnd_3705631 := by
    simpa [prefixWord, tailWord_3705631, baseEnd_3705631] using wordTrace_append hprefix tailTrace_3705631
  have hstable : (prefixWord ++ tailWord_3705631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705631).length < 2 ^ (prefixWord ++ tailWord_3705631).sum := by decide
  have hdescent : baseEnd_3705631 < baseStart_3705631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705632 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3705632 : Nat := 118140960795 + 3705632 * 2 ^ 59
def prefixEnd_3705632 : Nat := 4983230072969 + 3 ^ 40 * 3705632 * 2
def baseEnd_3705632 : Nat := 1902770344681750931458115

theorem tailTrace_3705632 : CollatzResearch.WordTrace tailWord_3705632 prefixEnd_3705632 1902770344681750931458115 := by
  unfold tailWord_3705632
  simp only [CollatzResearch.WordTrace]
  refine ⟨67577751255567805202615575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90103668340757073603487433 67577751255567805202615575)
  ·
    refine ⟨101366626883351707803923363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67577751255567805202615575 101366626883351707803923363)
    ·
      refine ⟨152049940325027561705885045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101366626883351707803923363 152049940325027561705885045)
      ·
        refine ⟨14254681905471333909926723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152049940325027561705885045 14254681905471333909926723)
        ·
          refine ⟨21382022858207000864890085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14254681905471333909926723 21382022858207000864890085)
          ·
            refine ⟨4009129285913812662166891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21382022858207000864890085 4009129285913812662166891)
            ·
              refine ⟨6013693928870718993250337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009129285913812662166891 6013693928870718993250337)
              ·
                refine ⟨4510270446653039244937753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6013693928870718993250337 4510270446653039244937753)
                ·
                  refine ⟨3382702834989779433703315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4510270446653039244937753 3382702834989779433703315)
                  ·
                    refine ⟨5074054252484669150554973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382702834989779433703315 5074054252484669150554973)
                    ·
                      refine ⟨1902770344681750931458115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5074054252484669150554973 1902770344681750931458115)
                      ·
                        rfl

theorem cell23_3705632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3705632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705632 prefixEnd_3705632 := by exact prefixLift 3705632
  have htrace : WordTrace (prefixWord ++ tailWord_3705632) baseStart_3705632 baseEnd_3705632 := by
    simpa [prefixWord, tailWord_3705632, baseEnd_3705632] using wordTrace_append hprefix tailTrace_3705632
  have hstable : (prefixWord ++ tailWord_3705632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705632).length < 2 ^ (prefixWord ++ tailWord_3705632).sum := by decide
  have hdescent : baseEnd_3705632 < baseStart_3705632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705695 : List Nat := [1, 1, 2, 3, 1, 3, 5, 2, 5]
def baseStart_3705695 : Nat := 118140960795 + 3705695 * 2 ^ 59
def prefixEnd_3705695 : Nat := 4983230072969 + 3 ^ 40 * 3705695 * 2
def baseEnd_3705695 : Nat := 211422521551442687218925

theorem tailTrace_3705695 : CollatzResearch.WordTrace tailWord_3705695 prefixEnd_3705695 211422521551442687218925 := by
  unfold tailWord_3705695
  simp only [CollatzResearch.WordTrace]
  refine ⟨135157800309907372164774539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90105200206604914776516359 135157800309907372164774539)
  ·
    refine ⟨202736700464861058247161809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135157800309907372164774539 202736700464861058247161809)
    ·
      refine ⟨152052525348645793685371357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202736700464861058247161809 152052525348645793685371357)
      ·
        refine ⟨57019697005742172632014259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152052525348645793685371357 57019697005742172632014259)
        ·
          refine ⟨85529545508613258948021389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57019697005742172632014259 85529545508613258948021389)
          ·
            refine ⟨32073579565729972105508021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85529545508613258948021389 32073579565729972105508021)
            ·
              refine ⟨3006898084287184884891377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32073579565729972105508021 3006898084287184884891377)
              ·
                refine ⟨2255173563215388663668533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006898084287184884891377 2255173563215388663668533)
                ·
                  refine ⟨211422521551442687218925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2255173563215388663668533 211422521551442687218925)
                  ·
                    rfl

theorem cell23_3705695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 5].length) (baseStart_3705695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705695 prefixEnd_3705695 := by exact prefixLift 3705695
  have htrace : WordTrace (prefixWord ++ tailWord_3705695) baseStart_3705695 baseEnd_3705695 := by
    simpa [prefixWord, tailWord_3705695, baseEnd_3705695] using wordTrace_append hprefix tailTrace_3705695
  have hstable : (prefixWord ++ tailWord_3705695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705695).length < 2 ^ (prefixWord ++ tailWord_3705695).sum := by decide
  have hdescent : baseEnd_3705695 < baseStart_3705695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705701 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3705701 : Nat := 118140960795 + 3705701 * 2 ^ 59
def prefixEnd_3705701 : Nat := 4983230072969 + 3 ^ 40 * 3705701 * 2
def baseEnd_3705701 : Nat := 1902805774846911161495297

theorem tailTrace_3705701 : CollatzResearch.WordTrace tailWord_3705701 prefixEnd_3705701 1902805774846911161495297 := by
  unfold tailWord_3705701
  simp only [CollatzResearch.WordTrace]
  refine ⟨135158019147885635189492957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90105346098590423459661971 135158019147885635189492957)
  ·
    refine ⟨50684257180457113196059859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135158019147885635189492957 50684257180457113196059859)
    ·
      refine ⟨76026385770685669794089789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50684257180457113196059859 76026385770685669794089789)
      ·
        refine ⟨28509894664007126172783671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76026385770685669794089789 28509894664007126172783671)
        ·
          refine ⟨42764841996010689259175507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28509894664007126172783671 42764841996010689259175507)
          ·
            refine ⟨64147262994016033888763261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42764841996010689259175507 64147262994016033888763261)
            ·
              refine ⟨24055223622756012708286223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64147262994016033888763261 24055223622756012708286223)
              ·
                refine ⟨36082835434134019062429335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24055223622756012708286223 36082835434134019062429335)
                ·
                  refine ⟨54124253151201028593644003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36082835434134019062429335 54124253151201028593644003)
                  ·
                    refine ⟨81186379726801542890466005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54124253151201028593644003 81186379726801542890466005)
                    ·
                      refine ⟨1902805774846911161495297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81186379726801542890466005 1902805774846911161495297)
                      ·
                        rfl

theorem cell23_3705701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3705701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705701 prefixEnd_3705701 := by exact prefixLift 3705701
  have htrace : WordTrace (prefixWord ++ tailWord_3705701) baseStart_3705701 baseEnd_3705701 := by
    simpa [prefixWord, tailWord_3705701, baseEnd_3705701] using wordTrace_append hprefix tailTrace_3705701
  have hstable : (prefixWord ++ tailWord_3705701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705701).length < 2 ^ (prefixWord ++ tailWord_3705701).sum := by decide
  have hdescent : baseEnd_3705701 < baseStart_3705701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705711 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_3705711 : Nat := 118140960795 + 3705711 * 2 ^ 59
def prefixEnd_3705711 : Nat := 4983230072969 + 3 ^ 40 * 3705711 * 2
def baseEnd_3705711 : Nat := 1902810909653456122370251

theorem tailTrace_3705711 : CollatzResearch.WordTrace tailWord_3705711 prefixEnd_3705711 1902810909653456122370251 := by
  unfold tailWord_3705711
  simp only [CollatzResearch.WordTrace]
  refine ⟨135158383877849406897356987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90105589251899604598237991 135158383877849406897356987)
  ·
    refine ⟨202737575816774110346035481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135158383877849406897356987 202737575816774110346035481)
    ·
      refine ⟨152053181862580582759526611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202737575816774110346035481 152053181862580582759526611)
      ·
        refine ⟨228079772793870874139289917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152053181862580582759526611 228079772793870874139289917)
        ·
          refine ⟨85529914797701577802233719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228079772793870874139289917 85529914797701577802233719)
          ·
            refine ⟨128294872196552366703350579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85529914797701577802233719 128294872196552366703350579)
            ·
              refine ⟨192442308294828550055025869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128294872196552366703350579 192442308294828550055025869)
              ·
                refine ⟨72165865610560706270634701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192442308294828550055025869 72165865610560706270634701)
                ·
                  refine ⟨27062199603960264851488013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72165865610560706270634701 27062199603960264851488013)
                  ·
                    refine ⟨10148324851485099319308005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27062199603960264851488013 10148324851485099319308005)
                    ·
                      refine ⟨1902810909653456122370251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10148324851485099319308005 1902810909653456122370251)
                      ·
                        rfl

theorem cell23_3705711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_3705711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705711 prefixEnd_3705711 := by exact prefixLift 3705711
  have htrace : WordTrace (prefixWord ++ tailWord_3705711) baseStart_3705711 baseEnd_3705711 := by
    simpa [prefixWord, tailWord_3705711, baseEnd_3705711] using wordTrace_append hprefix tailTrace_3705711
  have hstable : (prefixWord ++ tailWord_3705711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705711).length < 2 ^ (prefixWord ++ tailWord_3705711).sum := by decide
  have hdescent : baseEnd_3705711 < baseStart_3705711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705728 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 3, 6, 2]
def baseStart_3705728 : Nat := 118140960795 + 3705728 * 2 ^ 59
def prefixEnd_3705728 : Nat := 4983230072969 + 3 ^ 40 * 3705728 * 2
def baseEnd_3705728 : Nat := 1902819638824582555857673

theorem tailTrace_3705728 : CollatzResearch.WordTrace tailWord_3705728 prefixEnd_3705728 1902819638824582555857673 := by
  unfold tailWord_3705728
  simp only [CollatzResearch.WordTrace]
  refine ⟨67579501959393909400362919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90106002612525212533817225 67579501959393909400362919)
  ·
    refine ⟨101369252939090864100544379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67579501959393909400362919 101369252939090864100544379)
    ·
      refine ⟨152053879408636296150816569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101369252939090864100544379 152053879408636296150816569)
      ·
        refine ⟨114040409556477222113112427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152053879408636296150816569 114040409556477222113112427)
        ·
          refine ⟨171060614334715833169668641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114040409556477222113112427 171060614334715833169668641)
          ·
            refine ⟨128295460751036874877251481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171060614334715833169668641 128295460751036874877251481)
            ·
              refine ⟨96221595563277656157938611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128295460751036874877251481 96221595563277656157938611)
              ·
                refine ⟨144332393344916484236907917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96221595563277656157938611 144332393344916484236907917)
                ·
                  refine ⟨54124647504343681588840469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144332393344916484236907917 54124647504343681588840469)
                  ·
                    refine ⟨2537092851766110074476897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54124647504343681588840469 2537092851766110074476897)
                    ·
                      refine ⟨1902819638824582555857673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537092851766110074476897 1902819638824582555857673)
                      ·
                        rfl

theorem cell23_3705728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_3705728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705728 prefixEnd_3705728 := by exact prefixLift 3705728
  have htrace : WordTrace (prefixWord ++ tailWord_3705728) baseStart_3705728 baseEnd_3705728 := by
    simpa [prefixWord, tailWord_3705728, baseEnd_3705728] using wordTrace_append hprefix tailTrace_3705728
  have hstable : (prefixWord ++ tailWord_3705728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705728).length < 2 ^ (prefixWord ++ tailWord_3705728).sum := by decide
  have hdescent : baseEnd_3705728 < baseStart_3705728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705746 : List Nat := [3, 2, 3, 2, 3, 1, 2, 2, 5]
def baseStart_3705746 : Nat := 118140960795 + 3705746 * 2 ^ 59
def prefixEnd_3705746 : Nat := 4983230072969 + 3 ^ 40 * 3705746 * 2
def baseEnd_3705746 : Nat := 211425431275151498381399

theorem tailTrace_3705746 : CollatzResearch.WordTrace tailWord_3705746 prefixEnd_3705746 211425431275151498381399 := by
  unfold tailWord_3705746
  simp only [CollatzResearch.WordTrace]
  refine ⟨33789915108180651968720273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90106440288481738583254061 33789915108180651968720273)
  ·
    refine ⟨25342436331135488976540205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33789915108180651968720273 25342436331135488976540205)
    ·
      refine ⟨9503413624175808366202577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25342436331135488976540205 9503413624175808366202577)
      ·
        refine ⟨7127560218131856274651933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9503413624175808366202577 7127560218131856274651933)
        ·
          refine ⟨2672835081799446102994475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7127560218131856274651933 2672835081799446102994475)
          ·
            refine ⟨4009252622699169154491713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672835081799446102994475 4009252622699169154491713)
            ·
              refine ⟨3006939467024376865868785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4009252622699169154491713 3006939467024376865868785)
              ·
                refine ⟨2255204600268282649401589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006939467024376865868785 2255204600268282649401589)
                ·
                  refine ⟨211425431275151498381399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2255204600268282649401589 211425431275151498381399)
                  ·
                    rfl

theorem cell23_3705746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_3705746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705746 prefixEnd_3705746 := by exact prefixLift 3705746
  have htrace : WordTrace (prefixWord ++ tailWord_3705746) baseStart_3705746 baseEnd_3705746 := by
    simpa [prefixWord, tailWord_3705746, baseEnd_3705746] using wordTrace_append hprefix tailTrace_3705746
  have hstable : (prefixWord ++ tailWord_3705746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705746).length < 2 ^ (prefixWord ++ tailWord_3705746).sum := by decide
  have hdescent : baseEnd_3705746 < baseStart_3705746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705748 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3705748 : Nat := 118140960795 + 3705748 * 2 ^ 59
def prefixEnd_3705748 : Nat := 4983230072969 + 3 ^ 40 * 3705748 * 2
def baseEnd_3705748 : Nat := 1902829908437672477607581

theorem tailTrace_3705748 : CollatzResearch.WordTrace tailWord_3705748 prefixEnd_3705748 1902829908437672477607581 := by
  unfold tailWord_3705748
  simp only [CollatzResearch.WordTrace]
  refine ⟨67579866689357681108226949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90106488919143574810969265 67579866689357681108226949)
  ·
    refine ⟨12671225004254565207792553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67579866689357681108226949 12671225004254565207792553)
    ·
      refine ⟨9503418753190923905844415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12671225004254565207792553 9503418753190923905844415)
      ·
        refine ⟨14255128129786385858766623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9503418753190923905844415 14255128129786385858766623)
        ·
          refine ⟨21382692194679578788149935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14255128129786385858766623 21382692194679578788149935)
          ·
            refine ⟨32074038292019368182224903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21382692194679578788149935 32074038292019368182224903)
            ·
              refine ⟨48111057438029052273337355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32074038292019368182224903 48111057438029052273337355)
              ·
                refine ⟨72166586157043578410006033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48111057438029052273337355 72166586157043578410006033)
                ·
                  refine ⟨54124939617782683807504525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72166586157043578410006033 54124939617782683807504525)
                  ·
                    refine ⟨20296852356668506427814197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54124939617782683807504525 20296852356668506427814197)
                    ·
                      refine ⟨1902829908437672477607581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20296852356668506427814197 1902829908437672477607581)
                      ·
                        rfl

theorem cell23_3705748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3705748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705748 prefixEnd_3705748 := by exact prefixLift 3705748
  have htrace : WordTrace (prefixWord ++ tailWord_3705748) baseStart_3705748 baseEnd_3705748 := by
    simpa [prefixWord, tailWord_3705748, baseEnd_3705748] using wordTrace_append hprefix tailTrace_3705748
  have hstable : (prefixWord ++ tailWord_3705748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705748).length < 2 ^ (prefixWord ++ tailWord_3705748).sum := by decide
  have hdescent : baseEnd_3705748 < baseStart_3705748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705762 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_3705762 : Nat := 118140960795 + 3705762 * 2 ^ 59
def prefixEnd_3705762 : Nat := 4983230072969 + 3 ^ 40 * 3705762 * 2
def baseEnd_3705762 : Nat := 1902837097166835422832517

theorem tailTrace_3705762 : CollatzResearch.WordTrace tailWord_3705762 prefixEnd_3705762 1902837097166835422832517 := by
  unfold tailWord_3705762
  simp only [CollatzResearch.WordTrace]
  refine ⟨33790061000166160651865885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90106829333776428404975693 33790061000166160651865885)
  ·
    refine ⟨12671272875062310244449707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33790061000166160651865885 12671272875062310244449707)
    ·
      refine ⟨19006909312593465366674561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12671272875062310244449707 19006909312593465366674561)
      ·
        refine ⟨14255181984445099025005921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19006909312593465366674561 14255181984445099025005921)
        ·
          refine ⟨10691386488333824268754441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14255181984445099025005921 10691386488333824268754441)
          ·
            refine ⟨8018539866250368201565831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10691386488333824268754441 8018539866250368201565831)
            ·
              refine ⟨12027809799375552302348747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018539866250368201565831 12027809799375552302348747)
              ·
                refine ⟨18041714699063328453523121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12027809799375552302348747 18041714699063328453523121)
                ·
                  refine ⟨13531286024297496340142341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18041714699063328453523121 13531286024297496340142341)
                  ·
                    refine ⟨2537116129555780563776689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13531286024297496340142341 2537116129555780563776689)
                    ·
                      refine ⟨1902837097166835422832517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537116129555780563776689 1902837097166835422832517)
                      ·
                        rfl

theorem cell23_3705762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_3705762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705762 prefixEnd_3705762 := by exact prefixLift 3705762
  have htrace : WordTrace (prefixWord ++ tailWord_3705762) baseStart_3705762 baseEnd_3705762 := by
    simpa [prefixWord, tailWord_3705762, baseEnd_3705762] using wordTrace_append hprefix tailTrace_3705762
  have hstable : (prefixWord ++ tailWord_3705762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705762).length < 2 ^ (prefixWord ++ tailWord_3705762).sum := by decide
  have hdescent : baseEnd_3705762 < baseStart_3705762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705771 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 6]
def baseStart_3705771 : Nat := 118140960795 + 3705771 * 2 ^ 59
def prefixEnd_3705771 : Nat := 4983230072969 + 3 ^ 40 * 3705771 * 2
def baseEnd_3705771 : Nat := 1902841718492725887619975

theorem tailTrace_3705771 : CollatzResearch.WordTrace tailWord_3705771 prefixEnd_3705771 1902841718492725887619975 := by
  unfold tailWord_3705771
  simp only [CollatzResearch.WordTrace]
  refine ⟨135160572257632037144541167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90107048171754691429694111 135160572257632037144541167)
  ·
    refine ⟨202740858386448055716811751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135160572257632037144541167 202740858386448055716811751)
    ·
      refine ⟨304111287579672083575217627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202740858386448055716811751 304111287579672083575217627)
      ·
        refine ⟨456166931369508125362826441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304111287579672083575217627 456166931369508125362826441)
        ·
          refine ⟨342125198527131094022119831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456166931369508125362826441 342125198527131094022119831)
          ·
            refine ⟨513187797790696641033179747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342125198527131094022119831 513187797790696641033179747)
            ·
              refine ⟨769781696686044961549769621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513187797790696641033179747 769781696686044961549769621)
              ·
                refine ⟨36083517032158357572645451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 769781696686044961549769621 36083517032158357572645451)
                ·
                  refine ⟨54125275548237536358968177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36083517032158357572645451 54125275548237536358968177)
                  ·
                    refine ⟨40593956661178152269226133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54125275548237536358968177 40593956661178152269226133)
                    ·
                      refine ⟨1902841718492725887619975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40593956661178152269226133 1902841718492725887619975)
                      ·
                        rfl

theorem cell23_3705771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_3705771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705771 prefixEnd_3705771 := by exact prefixLift 3705771
  have htrace : WordTrace (prefixWord ++ tailWord_3705771) baseStart_3705771 baseEnd_3705771 := by
    simpa [prefixWord, tailWord_3705771, baseEnd_3705771] using wordTrace_append hprefix tailTrace_3705771
  have hstable : (prefixWord ++ tailWord_3705771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705771).length < 2 ^ (prefixWord ++ tailWord_3705771).sum := by decide
  have hdescent : baseEnd_3705771 < baseStart_3705771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705789 : List Nat := [1, 4, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_3705789 : Nat := 118140960795 + 3705789 * 2 ^ 59
def prefixEnd_3705789 : Nat := 4983230072969 + 3 ^ 40 * 3705789 * 2
def baseEnd_3705789 : Nat := 634283653714835605731631

theorem tailTrace_3705789 : CollatzResearch.WordTrace tailWord_3705789 prefixEnd_3705789 634283653714835605731631 := by
  unfold tailWord_3705789
  simp only [CollatzResearch.WordTrace]
  refine ⟨135161228771566826218696421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90107485847711217479130947 135161228771566826218696421)
  ·
    refine ⟨25342730394668779916005579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135161228771566826218696421 25342730394668779916005579)
    ·
      refine ⟨38014095592003169874008369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25342730394668779916005579 38014095592003169874008369)
      ·
        refine ⟨28510571694002377405506277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38014095592003169874008369 28510571694002377405506277)
        ·
          refine ⟨5345732192625445763532427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28510571694002377405506277 5345732192625445763532427)
          ·
            refine ⟨8018598288938168645298641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345732192625445763532427 8018598288938168645298641)
            ·
              refine ⟨6013948716703626483973981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8018598288938168645298641 6013948716703626483973981)
              ·
                refine ⟨2255230768763859931490243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6013948716703626483973981 2255230768763859931490243)
                ·
                  refine ⟨3382846153145789897235365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255230768763859931490243 3382846153145789897235365)
                  ·
                    refine ⟨634283653714835605731631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3382846153145789897235365 634283653714835605731631)
                    ·
                      rfl

theorem cell23_3705789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_3705789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705789 prefixEnd_3705789 := by exact prefixLift 3705789
  have htrace : WordTrace (prefixWord ++ tailWord_3705789) baseStart_3705789 baseEnd_3705789 := by
    simpa [prefixWord, tailWord_3705789, baseEnd_3705789] using wordTrace_append hprefix tailTrace_3705789
  have hstable : (prefixWord ++ tailWord_3705789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705789).length < 2 ^ (prefixWord ++ tailWord_3705789).sum := by decide
  have hdescent : baseEnd_3705789 < baseStart_3705789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705812 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_3705812 : Nat := 118140960795 + 3705812 * 2 ^ 59
def prefixEnd_3705812 : Nat := 4983230072969 + 3 ^ 40 * 3705812 * 2
def baseEnd_3705812 : Nat := 1902862771199560227207287

theorem tailTrace_3705812 : CollatzResearch.WordTrace tailWord_3705812 prefixEnd_3705812 1902862771199560227207287 := by
  unfold tailWord_3705812
  simp only [CollatzResearch.WordTrace]
  refine ⟨67581033825241750573391845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90108045100322334097855793 67581033825241750573391845)
  ·
    refine ⟨12671443842232828232510971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67581033825241750573391845 12671443842232828232510971)
    ·
      refine ⟨19007165763349242348766457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12671443842232828232510971 19007165763349242348766457)
      ·
        refine ⟨14255374322511931761574843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19007165763349242348766457 14255374322511931761574843)
        ·
          refine ⟨21383061483767897642362265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14255374322511931761574843 21383061483767897642362265)
          ·
            refine ⟨16037296112825923231771699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21383061483767897642362265 16037296112825923231771699)
            ·
              refine ⟨24055944169238884847657549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16037296112825923231771699 24055944169238884847657549)
              ·
                refine ⟨9020979063464581817871581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24055944169238884847657549 9020979063464581817871581)
                ·
                  refine ⟨3382867148799218181701843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9020979063464581817871581 3382867148799218181701843)
                  ·
                    refine ⟨5074300723198827272552765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382867148799218181701843 5074300723198827272552765)
                    ·
                      refine ⟨1902862771199560227207287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5074300723198827272552765 1902862771199560227207287)
                      ·
                        rfl

theorem cell23_3705812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_3705812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705812 prefixEnd_3705812 := by exact prefixLift 3705812
  have htrace : WordTrace (prefixWord ++ tailWord_3705812) baseStart_3705812 baseEnd_3705812 := by
    simpa [prefixWord, tailWord_3705812, baseEnd_3705812] using wordTrace_append hprefix tailTrace_3705812
  have hstable : (prefixWord ++ tailWord_3705812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705812).length < 2 ^ (prefixWord ++ tailWord_3705812).sum := by decide
  have hdescent : baseEnd_3705812 < baseStart_3705812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705828 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_3705828 : Nat := 118140960795 + 3705828 * 2 ^ 59
def prefixEnd_3705828 : Nat := 4983230072969 + 3 ^ 40 * 3705828 * 2
def baseEnd_3705828 : Nat := 634290328963344054869071

theorem tailTrace_3705828 : CollatzResearch.WordTrace tailWord_3705828 prefixEnd_3705828 634290328963344054869071 := by
  unfold tailWord_3705828
  simp only [CollatzResearch.WordTrace]
  refine ⟨67581325609212767939683069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90108434145617023919577425 67581325609212767939683069)
  ·
    refine ⟨25342997103454787977381151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67581325609212767939683069 25342997103454787977381151)
    ·
      refine ⟨38014495655182181966071727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25342997103454787977381151 38014495655182181966071727)
      ·
        refine ⟨57021743482773272949107591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38014495655182181966071727 57021743482773272949107591)
        ·
          refine ⟨85532615224159909423661387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57021743482773272949107591 85532615224159909423661387)
          ·
            refine ⟨128298922836239864135492081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85532615224159909423661387 128298922836239864135492081)
            ·
              refine ⟨96224192127179898101619061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128298922836239864135492081 96224192127179898101619061)
              ·
                refine ⟨9021018011923115447026787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96224192127179898101619061 9021018011923115447026787)
                ·
                  refine ⟨13531527017884673170540181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9021018011923115447026787 13531527017884673170540181)
                  ·
                    refine ⟨634290328963344054869071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13531527017884673170540181 634290328963344054869071)
                    ·
                      rfl

theorem cell23_3705828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_3705828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705828 prefixEnd_3705828 := by exact prefixLift 3705828
  have htrace : WordTrace (prefixWord ++ tailWord_3705828) baseStart_3705828 baseEnd_3705828 := by
    simpa [prefixWord, tailWord_3705828, baseEnd_3705828] using wordTrace_append hprefix tailTrace_3705828
  have hstable : (prefixWord ++ tailWord_3705828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705828).length < 2 ^ (prefixWord ++ tailWord_3705828).sum := by decide
  have hdescent : baseEnd_3705828 < baseStart_3705828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705846 : List Nat := [5, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_3705846 : Nat := 118140960795 + 3705846 * 2 ^ 59
def prefixEnd_3705846 : Nat := 4983230072969 + 3 ^ 40 * 3705846 * 2
def baseEnd_3705846 : Nat := 1902880229541813094182131

theorem tailTrace_3705846 : CollatzResearch.WordTrace tailWord_3705846 prefixEnd_3705846 1902880229541813094182131 := by
  unfold tailWord_3705846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8447706733272520309595087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90108871821573549969014261 8447706733272520309595087)
  ·
    refine ⟨12671560099908780464392631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8447706733272520309595087 12671560099908780464392631)
    ·
      refine ⟨19007340149863170696588947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12671560099908780464392631 19007340149863170696588947)
      ·
        refine ⟨28511010224794756044883421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19007340149863170696588947 28511010224794756044883421)
        ·
          refine ⟨10691628834298033516831283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28511010224794756044883421 10691628834298033516831283)
          ·
            refine ⟨16037443251447050275246925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10691628834298033516831283 16037443251447050275246925)
            ·
              refine ⟨6014041219292643853217597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16037443251447050275246925 6014041219292643853217597)
              ·
                refine ⟨2255265457234741444956599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6014041219292643853217597 2255265457234741444956599)
                ·
                  refine ⟨3382898185852112167434899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255265457234741444956599 3382898185852112167434899)
                  ·
                    refine ⟨5074347278778168251152349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382898185852112167434899 5074347278778168251152349)
                    ·
                      refine ⟨1902880229541813094182131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5074347278778168251152349 1902880229541813094182131)
                      ·
                        rfl

theorem cell23_3705846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_3705846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705846 prefixEnd_3705846 := by exact prefixLift 3705846
  have htrace : WordTrace (prefixWord ++ tailWord_3705846) baseStart_3705846 baseEnd_3705846 := by
    simpa [prefixWord, tailWord_3705846, baseEnd_3705846] using wordTrace_append hprefix tailTrace_3705846
  have hstable : (prefixWord ++ tailWord_3705846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705846).length < 2 ^ (prefixWord ++ tailWord_3705846).sum := by decide
  have hdescent : baseEnd_3705846 < baseStart_3705846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705848 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_3705848 : Nat := 118140960795 + 3705848 * 2 ^ 59
def prefixEnd_3705848 : Nat := 4983230072969 + 3 ^ 40 * 3705848 * 2
def baseEnd_3705848 : Nat := 1902881256503122086357121

theorem tailTrace_3705848 : CollatzResearch.WordTrace tailWord_3705848 prefixEnd_3705848 1902881256503122086357121 := by
  unfold tailWord_3705848
  simp only [CollatzResearch.WordTrace]
  refine ⟨67581690339176539647547099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90108920452235386196729465 67581690339176539647547099)
  ·
    refine ⟨101372535508764809471320649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67581690339176539647547099 101372535508764809471320649)
    ·
      refine ⟨76029401631573607103490487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101372535508764809471320649 76029401631573607103490487)
      ·
        refine ⟨114044102447360410655235731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76029401631573607103490487 114044102447360410655235731)
        ·
          refine ⟨171066153671040615982853597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114044102447360410655235731 171066153671040615982853597)
          ·
            refine ⟨64149807626640230993570099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171066153671040615982853597 64149807626640230993570099)
            ·
              refine ⟨96224711439960346490355149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64149807626640230993570099 96224711439960346490355149)
              ·
                refine ⟨36084266789985129933883181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96224711439960346490355149 36084266789985129933883181)
                ·
                  refine ⟨13531600046244423725206193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36084266789985129933883181 13531600046244423725206193)
                  ·
                    refine ⟨10148700034683317793904645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13531600046244423725206193 10148700034683317793904645)
                    ·
                      refine ⟨1902881256503122086357121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10148700034683317793904645 1902881256503122086357121)
                      ·
                        rfl

theorem cell23_3705848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_3705848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705848 prefixEnd_3705848 := by exact prefixLift 3705848
  have htrace : WordTrace (prefixWord ++ tailWord_3705848) baseStart_3705848 baseEnd_3705848 := by
    simpa [prefixWord, tailWord_3705848, baseEnd_3705848] using wordTrace_append hprefix tailTrace_3705848
  have hstable : (prefixWord ++ tailWord_3705848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705848).length < 2 ^ (prefixWord ++ tailWord_3705848).sum := by decide
  have hdescent : baseEnd_3705848 < baseStart_3705848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705879 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 2, 4]
def baseStart_3705879 : Nat := 118140960795 + 3705879 * 2 ^ 59
def prefixEnd_3705879 : Nat := 4983230072969 + 3 ^ 40 * 3705879 * 2
def baseEnd_3705879 : Nat := 634299058134470488356493

theorem tailTrace_3705879 : CollatzResearch.WordTrace tailWord_3705879 prefixEnd_3705879 634299058134470488356493 := by
  unfold tailWord_3705879
  simp only [CollatzResearch.WordTrace]
  refine ⟨135164511341240771589472691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90109674227493847726315127 135164511341240771589472691)
  ·
    refine ⟨202746767011861157384209037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135164511341240771589472691 202746767011861157384209037)
    ·
      refine ⟨76030037629447934019078389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202746767011861157384209037 76030037629447934019078389)
      ·
        refine ⟨7127816027760743814288599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76030037629447934019078389 7127816027760743814288599)
        ·
          refine ⟨10691724041641115721432899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127816027760743814288599 10691724041641115721432899)
          ·
            refine ⟨16037586062461673582149349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10691724041641115721432899 16037586062461673582149349)
            ·
              refine ⟨3007047386711563796653003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16037586062461673582149349 3007047386711563796653003)
              ·
                refine ⟨4510571080067345694979505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007047386711563796653003 4510571080067345694979505)
                ·
                  refine ⟨3382928310050509271234629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4510571080067345694979505 3382928310050509271234629)
                  ·
                    refine ⟨634299058134470488356493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3382928310050509271234629 634299058134470488356493)
                    ·
                      rfl

theorem cell23_3705879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_3705879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705879 prefixEnd_3705879 := by exact prefixLift 3705879
  have htrace : WordTrace (prefixWord ++ tailWord_3705879) baseStart_3705879 baseEnd_3705879 := by
    simpa [prefixWord, tailWord_3705879, baseEnd_3705879] using wordTrace_append hprefix tailTrace_3705879
  have hstable : (prefixWord ++ tailWord_3705879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705879).length < 2 ^ (prefixWord ++ tailWord_3705879).sum := by decide
  have hdescent : baseEnd_3705879 < baseStart_3705879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705889 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3705889 : Nat := 118140960795 + 3705889 * 2 ^ 59
def prefixEnd_3705889 : Nat := 4983230072969 + 3 ^ 40 * 3705889 * 2
def baseEnd_3705889 : Nat := 1902902309209956425944433

theorem tailTrace_3705889 : CollatzResearch.WordTrace tailWord_3705889 prefixEnd_3705889 1902902309209956425944433 := by
  unfold tailWord_3705889
  simp only [CollatzResearch.WordTrace]
  refine ⟨135164876071204543297336721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90109917380803028864891147 135164876071204543297336721)
  ·
    refine ⟨101373657053403407473002541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135164876071204543297336721 101373657053403407473002541)
    ·
      refine ⟨38015121395026277802375953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101373657053403407473002541 38015121395026277802375953)
      ·
        refine ⟨28511341046269708351781965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38015121395026277802375953 28511341046269708351781965)
        ·
          refine ⟨10691752892351140631918237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28511341046269708351781965 10691752892351140631918237)
          ·
            refine ⟨4009407334631677736969339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10691752892351140631918237 4009407334631677736969339)
            ·
              refine ⟨6014111001947516605454009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009407334631677736969339 6014111001947516605454009)
              ·
                refine ⟨4510583251460637454090507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6014111001947516605454009 4510583251460637454090507)
                ·
                  refine ⟨6765874877190956181135761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510583251460637454090507 6765874877190956181135761)
                  ·
                    refine ⟨5074406157893217135851821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6765874877190956181135761 5074406157893217135851821)
                    ·
                      refine ⟨1902902309209956425944433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5074406157893217135851821 1902902309209956425944433)
                      ·
                        rfl

theorem cell23_3705889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3705889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705889 prefixEnd_3705889 := by exact prefixLift 3705889
  have htrace : WordTrace (prefixWord ++ tailWord_3705889) baseStart_3705889 baseEnd_3705889 := by
    simpa [prefixWord, tailWord_3705889, baseEnd_3705889] using wordTrace_append hprefix tailTrace_3705889
  have hstable : (prefixWord ++ tailWord_3705889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705889).length < 2 ^ (prefixWord ++ tailWord_3705889).sum := by decide
  have hdescent : baseEnd_3705889 < baseStart_3705889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705902 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_3705902 : Nat := 118140960795 + 3705902 * 2 ^ 59
def prefixEnd_3705902 : Nat := 4983230072969 + 3 ^ 40 * 3705902 * 2
def baseEnd_3705902 : Nat := 1902908984458464875081873

theorem tailTrace_3705902 : CollatzResearch.WordTrace tailWord_3705902 prefixEnd_3705902 1902908984458464875081873 := by
  unfold tailWord_3705902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16895668777519680814694995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90110233480104964345039973 16895668777519680814694995)
  ·
    refine ⟨25343503166279521222042493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16895668777519680814694995 25343503166279521222042493)
    ·
      refine ⟨9503813687354820458265935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25343503166279521222042493 9503813687354820458265935)
      ·
        refine ⟨14255720531032230687398903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9503813687354820458265935 14255720531032230687398903)
        ·
          refine ⟨21383580796548346031098355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14255720531032230687398903 21383580796548346031098355)
          ·
            refine ⟨32075371194822519046647533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21383580796548346031098355 32075371194822519046647533)
            ·
              refine ⟨12028264198058444642492825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32075371194822519046647533 12028264198058444642492825)
              ·
                refine ⟨9021198148543833481869619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12028264198058444642492825 9021198148543833481869619)
                ·
                  refine ⟨13531797222815750222804429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9021198148543833481869619 13531797222815750222804429)
                  ·
                    refine ⟨5074423958555906333551661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13531797222815750222804429 5074423958555906333551661)
                    ·
                      refine ⟨1902908984458464875081873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5074423958555906333551661 1902908984458464875081873)
                      ·
                        rfl

theorem cell23_3705902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_3705902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705902 prefixEnd_3705902 := by exact prefixLift 3705902
  have htrace : WordTrace (prefixWord ++ tailWord_3705902) baseStart_3705902 baseEnd_3705902 := by
    simpa [prefixWord, tailWord_3705902, baseEnd_3705902] using wordTrace_append hprefix tailTrace_3705902
  have hstable : (prefixWord ++ tailWord_3705902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705902).length < 2 ^ (prefixWord ++ tailWord_3705902).sum := by decide
  have hdescent : baseEnd_3705902 < baseStart_3705902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705975 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 3]
def baseStart_3705975 : Nat := 118140960795 + 3705975 * 2 ^ 59
def prefixEnd_3705975 : Nat := 4983230072969 + 3 ^ 40 * 3705975 * 2
def baseEnd_3705975 : Nat := 1902946468546243089469037

theorem tailTrace_3705975 : CollatzResearch.WordTrace tailWord_3705975 prefixEnd_3705975 1902946468546243089469037 := by
  unfold tailWord_3705975
  simp only [CollatzResearch.WordTrace]
  refine ⟨135168012748892979984967379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90112008499261986656644919 135168012748892979984967379)
  ·
    refine ⟨202752019123339469977451069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135168012748892979984967379 202752019123339469977451069)
    ·
      refine ⟨76032007171252301241544151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202752019123339469977451069 76032007171252301241544151)
      ·
        refine ⟨114048010756878451862316227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76032007171252301241544151 114048010756878451862316227)
        ·
          refine ⟨171072016135317677793474341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114048010756878451862316227 171072016135317677793474341)
          ·
            refine ⟨32076003025372064586276439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171072016135317677793474341 32076003025372064586276439)
            ·
              refine ⟨48114004538058096879414659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32076003025372064586276439 48114004538058096879414659)
              ·
                refine ⟨72171006807087145319121989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48114004538058096879414659 72171006807087145319121989)
                ·
                  refine ⟨13532063776328839747335373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72171006807087145319121989 13532063776328839747335373)
                  ·
                    refine ⟨5074523916123314905250765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13532063776328839747335373 5074523916123314905250765)
                    ·
                      refine ⟨1902946468546243089469037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5074523916123314905250765 1902946468546243089469037)
                      ·
                        rfl

theorem cell23_3705975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_3705975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3705975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3705975 prefixEnd_3705975 := by exact prefixLift 3705975
  have htrace : WordTrace (prefixWord ++ tailWord_3705975) baseStart_3705975 baseEnd_3705975 := by
    simpa [prefixWord, tailWord_3705975, baseEnd_3705975] using wordTrace_append hprefix tailTrace_3705975
  have hstable : (prefixWord ++ tailWord_3705975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705975).length < 2 ^ (prefixWord ++ tailWord_3705975).sum := by decide
  have hdescent : baseEnd_3705975 < baseStart_3705975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706029 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3706029 : Nat := 118140960795 + 3706029 * 2 ^ 59
def prefixEnd_3706029 : Nat := 4983230072969 + 3 ^ 40 * 3706029 * 2
def baseEnd_3706029 : Nat := 634324732167195292731263

theorem tailTrace_3706029 : CollatzResearch.WordTrace tailWord_3706029 prefixEnd_3706029 634324732167195292731263 := by
  unfold tailWord_3706029
  simp only [CollatzResearch.WordTrace]
  refine ⟨135169982290697347207433141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90113321527131564804955427 135169982290697347207433141)
  ·
    refine ⟨12672185839752876300696857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135169982290697347207433141 12672185839752876300696857)
    ·
      refine ⟨9504139379814657225522643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12672185839752876300696857 9504139379814657225522643)
      ·
        refine ⟨14256209069721985838283965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9504139379814657225522643 14256209069721985838283965)
        ·
          refine ⟨5346078401145744689356487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14256209069721985838283965 5346078401145744689356487)
          ·
            refine ⟨8019117601718617034034731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346078401145744689356487 8019117601718617034034731)
            ·
              refine ⟨12028676402577925551052097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019117601718617034034731 12028676402577925551052097)
              ·
                refine ⟨9021507301933444163289073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12028676402577925551052097 9021507301933444163289073)
                ·
                  refine ⟨6766130476450083122466805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9021507301933444163289073 6766130476450083122466805)
                  ·
                    refine ⟨634324732167195292731263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6766130476450083122466805 634324732167195292731263)
                    ·
                      rfl

theorem cell23_3706029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3706029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706029 prefixEnd_3706029 := by exact prefixLift 3706029
  have htrace : WordTrace (prefixWord ++ tailWord_3706029) baseStart_3706029 baseEnd_3706029 := by
    simpa [prefixWord, tailWord_3706029, baseEnd_3706029] using wordTrace_append hprefix tailTrace_3706029
  have hstable : (prefixWord ++ tailWord_3706029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706029).length < 2 ^ (prefixWord ++ tailWord_3706029).sum := by decide
  have hdescent : baseEnd_3706029 < baseStart_3706029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706045 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3706045 : Nat := 118140960795 + 3706045 * 2 ^ 59
def prefixEnd_3706045 : Nat := 4983230072969 + 3 ^ 40 * 3706045 * 2
def baseEnd_3706045 : Nat := 1902982412192057815593715

theorem tailTrace_3706045 : CollatzResearch.WordTrace tailWord_3706045 prefixEnd_3706045 1902982412192057815593715 := by
  unfold tailWord_3706045
  simp only [CollatzResearch.WordTrace]
  refine ⟨135170565858639381940015589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90113710572426254626677059 135170565858639381940015589)
  ·
    refine ⟨25344481098494884113752923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135170565858639381940015589 25344481098494884113752923)
    ·
      refine ⟨38016721647742326170629385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25344481098494884113752923 38016721647742326170629385)
      ·
        refine ⟨28512541235806744627972039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38016721647742326170629385 28512541235806744627972039)
        ·
          refine ⟨42768811853710116941958059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28512541235806744627972039 42768811853710116941958059)
          ·
            refine ⟨64153217780565175412937089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42768811853710116941958059 64153217780565175412937089)
            ·
              refine ⟨48114913335423881559702817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64153217780565175412937089 48114913335423881559702817)
              ·
                refine ⟨36086185001567911169777113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48114913335423881559702817 36086185001567911169777113)
                ·
                  refine ⟨27064638751175933377332835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36086185001567911169777113 27064638751175933377332835)
                  ·
                    refine ⟨40596958126763900065999253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27064638751175933377332835 40596958126763900065999253)
                    ·
                      refine ⟨1902982412192057815593715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40596958126763900065999253 1902982412192057815593715)
                      ·
                        rfl

theorem cell23_3706045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3706045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706045 prefixEnd_3706045 := by exact prefixLift 3706045
  have htrace : WordTrace (prefixWord ++ tailWord_3706045) baseStart_3706045 baseEnd_3706045 := by
    simpa [prefixWord, tailWord_3706045, baseEnd_3706045] using wordTrace_append hprefix tailTrace_3706045
  have hstable : (prefixWord ++ tailWord_3706045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706045).length < 2 ^ (prefixWord ++ tailWord_3706045).sum := by decide
  have hdescent : baseEnd_3706045 < baseStart_3706045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706069 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3706069 : Nat := 118140960795 + 3706069 * 2 ^ 59
def prefixEnd_3706069 : Nat := 4983230072969 + 3 ^ 40 * 3706069 * 2
def baseEnd_3706069 : Nat := 1902994735727765721693605

theorem tailTrace_3706069 : CollatzResearch.WordTrace tailWord_3706069 prefixEnd_3706069 1902994735727765721693605 := by
  unfold tailWord_3706069
  simp only [CollatzResearch.WordTrace]
  refine ⟨135171441210552434038889261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90114294140368289359259507 135171441210552434038889261)
  ·
    refine ⟨50689290453957162764583473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135171441210552434038889261 50689290453957162764583473)
    ·
      refine ⟨38016967840467872073437605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50689290453957162764583473 38016967840467872073437605)
      ·
        refine ⟨7128181470087726013769551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38016967840467872073437605 7128181470087726013769551)
        ·
          refine ⟨10692272205131589020654327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7128181470087726013769551 10692272205131589020654327)
          ·
            refine ⟨16038408307697383530981491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10692272205131589020654327 16038408307697383530981491)
            ·
              refine ⟨24057612461546075296472237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16038408307697383530981491 24057612461546075296472237)
              ·
                refine ⟨9021604673079778236177089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24057612461546075296472237 9021604673079778236177089)
                ·
                  refine ⟨6766203504809833677132817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9021604673079778236177089 6766203504809833677132817)
                  ·
                    refine ⟨5074652628607375257849613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6766203504809833677132817 5074652628607375257849613)
                    ·
                      refine ⟨1902994735727765721693605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5074652628607375257849613 1902994735727765721693605)
                      ·
                        rfl

theorem cell23_3706069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3706069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706069 prefixEnd_3706069 := by exact prefixLift 3706069
  have htrace : WordTrace (prefixWord ++ tailWord_3706069) baseStart_3706069 baseEnd_3706069 := by
    simpa [prefixWord, tailWord_3706069, baseEnd_3706069] using wordTrace_append hprefix tailTrace_3706069
  have hstable : (prefixWord ++ tailWord_3706069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706069).length < 2 ^ (prefixWord ++ tailWord_3706069).sum := by decide
  have hdescent : baseEnd_3706069 < baseStart_3706069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706093 : List Nat := [1, 5, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_3706093 : Nat := 118140960795 + 3706093 * 2 ^ 59
def prefixEnd_3706093 : Nat := 4983230072969 + 3 ^ 40 * 3706093 * 2
def baseEnd_3706093 : Nat := 634335686421157875931165

theorem tailTrace_3706093 : CollatzResearch.WordTrace tailWord_3706093 prefixEnd_3706093 634335686421157875931165 := by
  unfold tailWord_3706093
  simp only [CollatzResearch.WordTrace]
  refine ⟨135172316562465486137762933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90114877708310324091841955 135172316562465486137762933)
  ·
    refine ⟨12672404677731139325415275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135172316562465486137762933 12672404677731139325415275)
    ·
      refine ⟨19008607016596708988122913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12672404677731139325415275 19008607016596708988122913)
      ·
        refine ⟨14256455262447531741092185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19008607016596708988122913 14256455262447531741092185)
        ·
          refine ⟨10692341446835648805819139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14256455262447531741092185 10692341446835648805819139)
          ·
            refine ⟨16038512170253473208728709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10692341446835648805819139 16038512170253473208728709)
            ·
              refine ⟨3007221031922526226636633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16038512170253473208728709 3007221031922526226636633)
              ·
                refine ⟨2255415773941894669977475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3007221031922526226636633 2255415773941894669977475)
                ·
                  refine ⟨3383123660912842004966213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255415773941894669977475 3383123660912842004966213)
                  ·
                    refine ⟨634335686421157875931165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3383123660912842004966213 634335686421157875931165)
                    ·
                      rfl

theorem cell23_3706093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_3706093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706093 prefixEnd_3706093 := by exact prefixLift 3706093
  have htrace : WordTrace (prefixWord ++ tailWord_3706093) baseStart_3706093 baseEnd_3706093 := by
    simpa [prefixWord, tailWord_3706093, baseEnd_3706093] using wordTrace_append hprefix tailTrace_3706093
  have hstable : (prefixWord ++ tailWord_3706093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706093).length < 2 ^ (prefixWord ++ tailWord_3706093).sum := by decide
  have hdescent : baseEnd_3706093 < baseStart_3706093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706100 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3706100 : Nat := 118140960795 + 3706100 * 2 ^ 59
def prefixEnd_3706100 : Nat := 4983230072969 + 3 ^ 40 * 3706100 * 2
def baseEnd_3706100 : Nat := 1903010653628055100405963

theorem tailTrace_3706100 : CollatzResearch.WordTrace tailWord_3706100 prefixEnd_3706100 1903010653628055100405963 := by
  unfold tailWord_3706100
  simp only [CollatzResearch.WordTrace]
  refine ⟨67586285936720063166633877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90115047915626750888845169 67586285936720063166633877)
  ·
    refine ⟨3168107153283752960935963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67586285936720063166633877 3168107153283752960935963)
    ·
      refine ⟨4752160729925629441403945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3168107153283752960935963 4752160729925629441403945)
      ·
        refine ⟨3564120547444222081052959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4752160729925629441403945 3564120547444222081052959)
        ·
          refine ⟨5346180821166333121579439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3564120547444222081052959 5346180821166333121579439)
          ·
            refine ⟨8019271231749499682369159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346180821166333121579439 8019271231749499682369159)
            ·
              refine ⟨12028906847624249523553739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019271231749499682369159 12028906847624249523553739)
              ·
                refine ⟨18043360271436374285330609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12028906847624249523553739 18043360271436374285330609)
                ·
                  refine ⟨13532520203577280713997957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18043360271436374285330609 13532520203577280713997957)
                  ·
                    refine ⟨2537347538170740133874617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13532520203577280713997957 2537347538170740133874617)
                    ·
                      refine ⟨1903010653628055100405963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537347538170740133874617 1903010653628055100405963)
                      ·
                        rfl

theorem cell23_3706100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3706100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706100 prefixEnd_3706100 := by exact prefixLift 3706100
  have htrace : WordTrace (prefixWord ++ tailWord_3706100) baseStart_3706100 baseEnd_3706100 := by
    simpa [prefixWord, tailWord_3706100, baseEnd_3706100] using wordTrace_append hprefix tailTrace_3706100
  have hstable : (prefixWord ++ tailWord_3706100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706100).length < 2 ^ (prefixWord ++ tailWord_3706100).sum := by decide
  have hdescent : baseEnd_3706100 < baseStart_3706100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706116 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3706116 : Nat := 118140960795 + 3706116 * 2 ^ 59
def prefixEnd_3706116 : Nat := 4983230072969 + 3 ^ 40 * 3706116 * 2
def baseEnd_3706116 : Nat := 1903018869318527037805889

theorem tailTrace_3706116 : CollatzResearch.WordTrace tailWord_3706116 prefixEnd_3706116 1903018869318527037805889 := by
  unfold tailWord_3706116
  simp only [CollatzResearch.WordTrace]
  refine ⟨67586577720691080532925101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90115436960921440710566801 67586577720691080532925101)
  ·
    refine ⟨25344966645259155199846913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67586577720691080532925101 25344966645259155199846913)
    ·
      refine ⟨19008724983944366399885185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25344966645259155199846913 19008724983944366399885185)
      ·
        refine ⟨14256543737958274799913889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19008724983944366399885185 14256543737958274799913889)
        ·
          refine ⟨10692407803468706099935417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14256543737958274799913889 10692407803468706099935417)
          ·
            refine ⟨8019305852601529574951563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10692407803468706099935417 8019305852601529574951563)
            ·
              refine ⟨12028958778902294362427345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019305852601529574951563 12028958778902294362427345)
              ·
                refine ⟨9021719084176720771820509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12028958778902294362427345 9021719084176720771820509)
                ·
                  refine ⟨3383144656566270289432691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9021719084176720771820509 3383144656566270289432691)
                  ·
                    refine ⟨5074716984849405434149037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3383144656566270289432691 5074716984849405434149037)
                    ·
                      refine ⟨1903018869318527037805889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5074716984849405434149037 1903018869318527037805889)
                      ·
                        rfl

theorem cell23_3706116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3706116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706116 prefixEnd_3706116 := by exact prefixLift 3706116
  have htrace : WordTrace (prefixWord ++ tailWord_3706116) baseStart_3706116 baseEnd_3706116 := by
    simpa [prefixWord, tailWord_3706116, baseEnd_3706116] using wordTrace_append hprefix tailTrace_3706116
  have hstable : (prefixWord ++ tailWord_3706116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706116).length < 2 ^ (prefixWord ++ tailWord_3706116).sum := by decide
  have hdescent : baseEnd_3706116 < baseStart_3706116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706126 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2]
def baseStart_3706126 : Nat := 118140960795 + 3706126 * 2 ^ 59
def prefixEnd_3706126 : Nat := 4983230072969 + 3 ^ 40 * 3706126 * 2
def baseEnd_3706126 : Nat := 1903024004125071998680843

theorem tailTrace_3706126 : CollatzResearch.WordTrace tailWord_3706126 prefixEnd_3706126 1903024004125071998680843 := by
  unfold tailWord_3706126
  simp only [CollatzResearch.WordTrace]
  refine ⟨16896690021418241596714279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90115680114230621849142821 16896690021418241596714279)
  ·
    refine ⟨25345035032127362395071419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16896690021418241596714279 25345035032127362395071419)
    ·
      refine ⟨38017552548191043592607129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25345035032127362395071419 38017552548191043592607129)
      ·
        refine ⟨28513164411143282694455347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38017552548191043592607129 28513164411143282694455347)
        ·
          refine ⟨42769746616714924041683021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28513164411143282694455347 42769746616714924041683021)
          ·
            refine ⟨16038654981268096515631133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42769746616714924041683021 16038654981268096515631133)
            ·
              refine ⟨6014495617975536193361675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16038654981268096515631133 6014495617975536193361675)
              ·
                refine ⟨9021743426963304290042513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014495617975536193361675 9021743426963304290042513)
                ·
                  refine ⟨6766307570222478217531885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9021743426963304290042513 6766307570222478217531885)
                  ·
                    refine ⟨2537365338833429331574457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6766307570222478217531885 2537365338833429331574457)
                    ·
                      refine ⟨1903024004125071998680843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537365338833429331574457 1903024004125071998680843)
                      ·
                        rfl

theorem cell23_3706126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_3706126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706126 prefixEnd_3706126 := by exact prefixLift 3706126
  have htrace : WordTrace (prefixWord ++ tailWord_3706126) baseStart_3706126 baseEnd_3706126 := by
    simpa [prefixWord, tailWord_3706126, baseEnd_3706126] using wordTrace_append hprefix tailTrace_3706126
  have hstable : (prefixWord ++ tailWord_3706126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706126).length < 2 ^ (prefixWord ++ tailWord_3706126).sum := by decide
  have hdescent : baseEnd_3706126 < baseStart_3706126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706136 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 1, 5]
def baseStart_3706136 : Nat := 118140960795 + 3706136 * 2 ^ 59
def prefixEnd_3706136 : Nat := 4983230072969 + 3 ^ 40 * 3706136 * 2
def baseEnd_3706136 : Nat := 634343046310538986518599

theorem tailTrace_3706136 : CollatzResearch.WordTrace tailWord_3706136 prefixEnd_3706136 634343046310538986518599 := by
  unfold tailWord_3706136
  simp only [CollatzResearch.WordTrace]
  refine ⟨67586942450654852240789131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90115923267539802987718841 67586942450654852240789131)
  ·
    refine ⟨101380413675982278361183697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67586942450654852240789131 101380413675982278361183697)
    ·
      refine ⟨76035310256986708770887773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101380413675982278361183697 76035310256986708770887773)
      ·
        refine ⟨28513241346370015789082915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76035310256986708770887773 28513241346370015789082915)
        ·
          refine ⟨42769862019555023683624373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28513241346370015789082915 42769862019555023683624373)
          ·
            refine ⟨4009674564333283470339785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42769862019555023683624373 4009674564333283470339785)
            ·
              refine ⟨3007255923249962602754839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4009674564333283470339785 3007255923249962602754839)
              ·
                refine ⟨4510883884874943904132259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007255923249962602754839 4510883884874943904132259)
                ·
                  refine ⟨6766325827312415856198389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510883884874943904132259 6766325827312415856198389)
                  ·
                    refine ⟨634343046310538986518599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6766325827312415856198389 634343046310538986518599)
                    ·
                      rfl

theorem cell23_3706136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_3706136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706136 prefixEnd_3706136 := by exact prefixLift 3706136
  have htrace : WordTrace (prefixWord ++ tailWord_3706136) baseStart_3706136 baseEnd_3706136 := by
    simpa [prefixWord, tailWord_3706136, baseEnd_3706136] using wordTrace_append hprefix tailTrace_3706136
  have hstable : (prefixWord ++ tailWord_3706136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706136).length < 2 ^ (prefixWord ++ tailWord_3706136).sum := by decide
  have hdescent : baseEnd_3706136 < baseStart_3706136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706139 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 7, 2, 2]
def baseStart_3706139 : Nat := 118140960795 + 3706139 * 2 ^ 59
def prefixEnd_3706139 : Nat := 4983230072969 + 3 ^ 40 * 3706139 * 2
def baseEnd_3706139 : Nat := 1903030679373580447818283

theorem tailTrace_3706139 : CollatzResearch.WordTrace tailWord_3706139 prefixEnd_3706139 1903030679373580447818283 := by
  unfold tailWord_3706139
  simp only [CollatzResearch.WordTrace]
  refine ⟨135173994320298835993937471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90115996213532557329291647 135173994320298835993937471)
  ·
    refine ⟨202760991480448253990906207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135173994320298835993937471 202760991480448253990906207)
    ·
      refine ⟨304141487220672380986359311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202760991480448253990906207 304141487220672380986359311)
      ·
        refine ⟨456212230831008571479538967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304141487220672380986359311 456212230831008571479538967)
        ·
          refine ⟨684318346246512857219308451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456212230831008571479538967 684318346246512857219308451)
          ·
            refine ⟨1026477519369769285828962677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684318346246512857219308451 1026477519369769285828962677)
            ·
              refine ⟨96232267440915870546465251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1026477519369769285828962677 96232267440915870546465251)
              ·
                refine ⟨144348401161373805819697877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96232267440915870546465251 144348401161373805819697877)
                ·
                  refine ⟨3383165652219698573899169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 144348401161373805819697877 3383165652219698573899169)
                  ·
                    refine ⟨2537374239164773930424377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3383165652219698573899169 2537374239164773930424377)
                    ·
                      refine ⟨1903030679373580447818283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537374239164773930424377 1903030679373580447818283)
                      ·
                        rfl

theorem cell23_3706139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 2, 2].length) (baseStart_3706139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706139 prefixEnd_3706139 := by exact prefixLift 3706139
  have htrace : WordTrace (prefixWord ++ tailWord_3706139) baseStart_3706139 baseEnd_3706139 := by
    simpa [prefixWord, tailWord_3706139, baseEnd_3706139] using wordTrace_append hprefix tailTrace_3706139
  have hstable : (prefixWord ++ tailWord_3706139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706139).length < 2 ^ (prefixWord ++ tailWord_3706139).sum := by decide
  have hdescent : baseEnd_3706139 < baseStart_3706139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706149 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_3706149 : Nat := 118140960795 + 3706149 * 2 ^ 59
def prefixEnd_3706149 : Nat := 4983230072969 + 3 ^ 40 * 3706149 * 2
def baseEnd_3706149 : Nat := 634345271393375136231079

theorem tailTrace_3706149 : CollatzResearch.WordTrace tailWord_3706149 prefixEnd_3706149 634345271393375136231079 := by
  unfold tailWord_3706149
  simp only [CollatzResearch.WordTrace]
  refine ⟨135174359050262607701801501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90116239366841738467867667 135174359050262607701801501)
  ·
    refine ⟨50690384643848477888175563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135174359050262607701801501 50690384643848477888175563)
    ·
      refine ⟨76035576965772716832263345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50690384643848477888175563 76035576965772716832263345)
      ·
        refine ⟨57026682724329537624197509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76035576965772716832263345 57026682724329537624197509)
        ·
          refine ⟨10692503010811788304537033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57026682724329537624197509 10692503010811788304537033)
          ·
            refine ⟨8019377258108841228402775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10692503010811788304537033 8019377258108841228402775)
            ·
              refine ⟨12029065887163261842604163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019377258108841228402775 12029065887163261842604163)
              ·
                refine ⟨18043598830744892763906245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12029065887163261842604163 18043598830744892763906245)
                ·
                  refine ⟨3383174780764667393232421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18043598830744892763906245 3383174780764667393232421)
                  ·
                    refine ⟨634345271393375136231079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3383174780764667393232421 634345271393375136231079)
                    ·
                      rfl

theorem cell23_3706149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_3706149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706149 prefixEnd_3706149 := by exact prefixLift 3706149
  have htrace : WordTrace (prefixWord ++ tailWord_3706149) baseStart_3706149 baseEnd_3706149 := by
    simpa [prefixWord, tailWord_3706149, baseEnd_3706149] using wordTrace_append hprefix tailTrace_3706149
  have hstable : (prefixWord ++ tailWord_3706149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706149).length < 2 ^ (prefixWord ++ tailWord_3706149).sum := by decide
  have hdescent : baseEnd_3706149 < baseStart_3706149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706169 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3706169 : Nat := 118140960795 + 3706169 * 2 ^ 59
def prefixEnd_3706169 : Nat := 4983230072969 + 3 ^ 40 * 3706169 * 2
def baseEnd_3706169 : Nat := 1903046083793215330443145

theorem tailTrace_3706169 : CollatzResearch.WordTrace tailWord_3706169 prefixEnd_3706169 1903046083793215330443145 := by
  unfold tailWord_3706169
  simp only [CollatzResearch.WordTrace]
  refine ⟨135175088510190151117529561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90116725673460100745019707 135175088510190151117529561)
  ·
    refine ⟨101381316382642613338147171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135175088510190151117529561 101381316382642613338147171)
    ·
      refine ⟨152071974573963920007220757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101381316382642613338147171 152071974573963920007220757)
      ·
        refine ⟨7128373808154558750338473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152071974573963920007220757 7128373808154558750338473)
        ·
          refine ⟨5346280356115919062753855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7128373808154558750338473 5346280356115919062753855)
          ·
            refine ⟨8019420534173878594130783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346280356115919062753855 8019420534173878594130783)
            ·
              refine ⟨12029130801260817891196175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019420534173878594130783 12029130801260817891196175)
              ·
                refine ⟨18043696201891226836794263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12029130801260817891196175 18043696201891226836794263)
                ·
                  refine ⟨27065544302836840255191395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18043696201891226836794263 27065544302836840255191395)
                  ·
                    refine ⟨40598316454255260382787093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27065544302836840255191395 40598316454255260382787093)
                    ·
                      refine ⟨1903046083793215330443145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40598316454255260382787093 1903046083793215330443145)
                      ·
                        rfl

theorem cell23_3706169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3706169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706169 prefixEnd_3706169 := by exact prefixLift 3706169
  have htrace : WordTrace (prefixWord ++ tailWord_3706169) baseStart_3706169 baseEnd_3706169 := by
    simpa [prefixWord, tailWord_3706169, baseEnd_3706169] using wordTrace_append hprefix tailTrace_3706169
  have hstable : (prefixWord ++ tailWord_3706169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706169).length < 2 ^ (prefixWord ++ tailWord_3706169).sum := by decide
  have hdescent : baseEnd_3706169 < baseStart_3706169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706173 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3706173 : Nat := 118140960795 + 3706173 * 2 ^ 59
def prefixEnd_3706173 : Nat := 4983230072969 + 3 ^ 40 * 3706173 * 2
def baseEnd_3706173 : Nat := 1903048137715833314793127

theorem tailTrace_3706173 : CollatzResearch.WordTrace tailWord_3706173 prefixEnd_3706173 1903048137715833314793127 := by
  unfold tailWord_3706173
  simp only [CollatzResearch.WordTrace]
  refine ⟨135175234402175659800675173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90116822934783773200450115 135175234402175659800675173)
  ·
    refine ⟨25345356450407936212626595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135175234402175659800675173 25345356450407936212626595)
    ·
      refine ⟨38018034675611904318939893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25345356450407936212626595 38018034675611904318939893)
      ·
        refine ⟨3564190750838616029900615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38018034675611904318939893 3564190750838616029900615)
        ·
          refine ⟨5346286126257924044850923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3564190750838616029900615 5346286126257924044850923)
          ·
            refine ⟨8019429189386886067276385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346286126257924044850923 8019429189386886067276385)
            ·
              refine ⟨6014571892040164550457289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8019429189386886067276385 6014571892040164550457289)
              ·
                refine ⟨4510928919030123412842967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6014571892040164550457289 4510928919030123412842967)
                ·
                  refine ⟨6766393378545185119264451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510928919030123412842967 6766393378545185119264451)
                  ·
                    refine ⟨10149590067817777678896677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6766393378545185119264451 10149590067817777678896677)
                    ·
                      refine ⟨1903048137715833314793127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10149590067817777678896677 1903048137715833314793127)
                      ·
                        rfl

theorem cell23_3706173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3706173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706173 prefixEnd_3706173 := by exact prefixLift 3706173
  have htrace : WordTrace (prefixWord ++ tailWord_3706173) baseStart_3706173 baseEnd_3706173 := by
    simpa [prefixWord, tailWord_3706173, baseEnd_3706173] using wordTrace_append hprefix tailTrace_3706173
  have hstable : (prefixWord ++ tailWord_3706173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706173).length < 2 ^ (prefixWord ++ tailWord_3706173).sum := by decide
  have hdescent : baseEnd_3706173 < baseStart_3706173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706280 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_3706280 : Nat := 118140960795 + 3706280 * 2 ^ 59
def prefixEnd_3706280 : Nat := 4983230072969 + 3 ^ 40 * 3706280 * 2
def baseEnd_3706280 : Nat := 1903103080145864396155135

theorem tailTrace_3706280 : CollatzResearch.WordTrace tailWord_3706280 prefixEnd_3706280 1903103080145864396155135 := by
  unfold tailWord_3706280
  simp only [CollatzResearch.WordTrace]
  refine ⟨67589568506394008537410147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90119424675192011383213529 67589568506394008537410147)
  ·
    refine ⟨101384352759591012806115221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67589568506394008537410147 101384352759591012806115221)
    ·
      refine ⟨4752391535605828725286651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101384352759591012806115221 4752391535605828725286651)
      ·
        refine ⟨7128587303408743087929977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4752391535605828725286651 7128587303408743087929977)
        ·
          refine ⟨5346440477556557315947483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7128587303408743087929977 5346440477556557315947483)
          ·
            refine ⟨8019660716334835973921225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346440477556557315947483 8019660716334835973921225)
            ·
              refine ⟨6014745537251126980440919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8019660716334835973921225 6014745537251126980440919)
              ·
                refine ⟨9022118305876690470661379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014745537251126980440919 9022118305876690470661379)
                ·
                  refine ⟨13533177458815035705992069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9022118305876690470661379 13533177458815035705992069)
                  ·
                    refine ⟨2537470773527819194873513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13533177458815035705992069 2537470773527819194873513)
                    ·
                      refine ⟨1903103080145864396155135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537470773527819194873513 1903103080145864396155135)
                      ·
                        rfl

theorem cell23_3706280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_3706280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706280 prefixEnd_3706280 := by exact prefixLift 3706280
  have htrace : WordTrace (prefixWord ++ tailWord_3706280) baseStart_3706280 baseEnd_3706280 := by
    simpa [prefixWord, tailWord_3706280, baseEnd_3706280] using wordTrace_append hprefix tailTrace_3706280
  have hstable : (prefixWord ++ tailWord_3706280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706280).length < 2 ^ (prefixWord ++ tailWord_3706280).sum := by decide
  have hdescent : baseEnd_3706280 < baseStart_3706280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706319 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 4]
def baseStart_3706319 : Nat := 118140960795 + 3706319 * 2 ^ 59
def prefixEnd_3706319 : Nat := 4983230072969 + 3 ^ 40 * 3706319 * 2
def baseEnd_3706319 : Nat := 1903123105891389743567455

theorem tailTrace_3706319 : CollatzResearch.WordTrace tailWord_3706319 prefixEnd_3706319 1903123105891389743567455 := by
  unfold tailWord_3706319
  simp only [CollatzResearch.WordTrace]
  refine ⟨135180559459646726735490011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90120372973097817823660007 135180559459646726735490011)
  ·
    refine ⟨202770839189470090103235017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135180559459646726735490011 202770839189470090103235017)
    ·
      refine ⟨152078129392102567577426263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202770839189470090103235017 152078129392102567577426263)
      ·
        refine ⟨228117194088153851366139395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152078129392102567577426263 228117194088153851366139395)
        ·
          refine ⟨342175791132230777049209093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228117194088153851366139395 342175791132230777049209093)
          ·
            refine ⟨64157960837293270696726705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342175791132230777049209093 64157960837293270696726705)
            ·
              refine ⟨48118470627969953022545029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64157960837293270696726705 48118470627969953022545029)
              ·
                refine ⟨9022213242744366191727193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48118470627969953022545029 9022213242744366191727193)
                ·
                  refine ⟨6766659932058274643795395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9022213242744366191727193 6766659932058274643795395)
                  ·
                    refine ⟨10149989898087411965693093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6766659932058274643795395 10149989898087411965693093)
                    ·
                      refine ⟨1903123105891389743567455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10149989898087411965693093 1903123105891389743567455)
                      ·
                        rfl

theorem cell23_3706319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_3706319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706319 prefixEnd_3706319 := by exact prefixLift 3706319
  have htrace : WordTrace (prefixWord ++ tailWord_3706319) baseStart_3706319 baseEnd_3706319 := by
    simpa [prefixWord, tailWord_3706319, baseEnd_3706319] using wordTrace_append hprefix tailTrace_3706319
  have hstable : (prefixWord ++ tailWord_3706319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706319).length < 2 ^ (prefixWord ++ tailWord_3706319).sum := by decide
  have hdescent : baseEnd_3706319 < baseStart_3706319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706380 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 3, 4]
def baseStart_3706380 : Nat := 118140960795 + 3706380 * 2 ^ 59
def prefixEnd_3706380 : Nat := 4983230072969 + 3 ^ 40 * 3706380 * 2
def baseEnd_3706380 : Nat := 634384809403771334968225

theorem tailTrace_3706380 : CollatzResearch.WordTrace tailWord_3706380 prefixEnd_3706380 634384809403771334968225 := by
  unfold tailWord_3706380
  simp only [CollatzResearch.WordTrace]
  refine ⟨67591392156212867076730297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90121856208283822768973729 67591392156212867076730297)
  ·
    refine ⟨50693544117159650307547723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67591392156212867076730297 50693544117159650307547723)
    ·
      refine ⟨76040316175739475461321585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50693544117159650307547723 76040316175739475461321585)
      ·
        refine ⟨57030237131804606595991189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76040316175739475461321585 57030237131804606595991189)
        ·
          refine ⟨2673292365553340934187087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57030237131804606595991189 2673292365553340934187087)
          ·
            refine ⟨4009938548330011401280631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673292365553340934187087 4009938548330011401280631)
            ·
              refine ⟨6014907822495017101920947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009938548330011401280631 6014907822495017101920947)
              ·
                refine ⟨9022361733742525652881421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014907822495017101920947 9022361733742525652881421)
                ·
                  refine ⟨3383385650153447119830533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9022361733742525652881421 3383385650153447119830533)
                  ·
                    refine ⟨634384809403771334968225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3383385650153447119830533 634384809403771334968225)
                    ·
                      rfl

theorem cell23_3706380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_3706380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706380 prefixEnd_3706380 := by exact prefixLift 3706380
  have htrace : WordTrace (prefixWord ++ tailWord_3706380) baseStart_3706380 baseEnd_3706380 := by
    simpa [prefixWord, tailWord_3706380, baseEnd_3706380] using wordTrace_append hprefix tailTrace_3706380
  have hstable : (prefixWord ++ tailWord_3706380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706380).length < 2 ^ (prefixWord ++ tailWord_3706380).sum := by decide
  have hdescent : baseEnd_3706380 < baseStart_3706380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706419 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 3, 6]
def baseStart_3706419 : Nat := 118140960795 + 3706419 * 2 ^ 59
def prefixEnd_3706419 : Nat := 4983230072969 + 3 ^ 40 * 3706419 * 2
def baseEnd_3706419 : Nat := 634391484652279784105665

theorem tailTrace_3706419 : CollatzResearch.WordTrace tailWord_3706419 prefixEnd_3706419 634391484652279784105665 := by
  unfold tailWord_3706419
  simp only [CollatzResearch.WordTrace]
  refine ⟨135184206759284443814130311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90122804506189629209420207 135184206759284443814130311)
  ·
    refine ⟨202776310138926665721195467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135184206759284443814130311 202776310138926665721195467)
    ·
      refine ⟨304164465208389998581793201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202776310138926665721195467 304164465208389998581793201)
      ·
        refine ⟨228123348906292498936344901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304164465208389998581793201 228123348906292498936344901)
        ·
          refine ⟨42773127919929843550564669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228123348906292498936344901 42773127919929843550564669)
          ·
            refine ⟨16039922969973691331461751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42773127919929843550564669 16039922969973691331461751)
            ·
              refine ⟨24059884454960536997192627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16039922969973691331461751 24059884454960536997192627)
              ·
                refine ⟨36089826682440805495788941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24059884454960536997192627 36089826682440805495788941)
                ·
                  refine ⟨13533685005915302060920853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36089826682440805495788941 13533685005915302060920853)
                  ·
                    refine ⟨634391484652279784105665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13533685005915302060920853 634391484652279784105665)
                    ·
                      rfl

theorem cell23_3706419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 6].length) (baseStart_3706419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706419 prefixEnd_3706419 := by exact prefixLift 3706419
  have htrace : WordTrace (prefixWord ++ tailWord_3706419) baseStart_3706419 baseEnd_3706419 := by
    simpa [prefixWord, tailWord_3706419, baseEnd_3706419] using wordTrace_append hprefix tailTrace_3706419
  have hstable : (prefixWord ++ tailWord_3706419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706419).length < 2 ^ (prefixWord ++ tailWord_3706419).sum := by decide
  have hdescent : baseEnd_3706419 < baseStart_3706419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706423 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 1, 5]
def baseStart_3706423 : Nat := 118140960795 + 3706423 * 2 ^ 59
def prefixEnd_3706423 : Nat := 4983230072969 + 3 ^ 40 * 3706423 * 2
def baseEnd_3706423 : Nat := 634392169293152445555659

theorem tailTrace_3706423 : CollatzResearch.WordTrace tailWord_3706423 prefixEnd_3706423 634392169293152445555659 := by
  unfold tailWord_3706423
  simp only [CollatzResearch.WordTrace]
  refine ⟨135184352651269952497275923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90122901767513301664850615 135184352651269952497275923)
  ·
    refine ⟨202776528976904928745913885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135184352651269952497275923 202776528976904928745913885)
    ·
      refine ⟨76041198366339348279717707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202776528976904928745913885 76041198366339348279717707)
      ·
        refine ⟨114061797549509022419576561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76041198366339348279717707 114061797549509022419576561)
        ·
          refine ⟨85546348162131766814682421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114061797549509022419576561 85546348162131766814682421)
          ·
            refine ⟨8019970140199853138876477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85546348162131766814682421 8019970140199853138876477)
            ·
              refine ⟨3007488802574944927078679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8019970140199853138876477 3007488802574944927078679)
              ·
                refine ⟨4511233203862417390618019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007488802574944927078679 4511233203862417390618019)
                ·
                  refine ⟨6766849805793626085927029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511233203862417390618019 6766849805793626085927029)
                  ·
                    refine ⟨634392169293152445555659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6766849805793626085927029 634392169293152445555659)
                    ·
                      rfl

theorem cell23_3706423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_3706423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706423 prefixEnd_3706423 := by exact prefixLift 3706423
  have htrace : WordTrace (prefixWord ++ tailWord_3706423) baseStart_3706423 baseEnd_3706423 := by
    simpa [prefixWord, tailWord_3706423, baseEnd_3706423] using wordTrace_append hprefix tailTrace_3706423
  have hstable : (prefixWord ++ tailWord_3706423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706423).length < 2 ^ (prefixWord ++ tailWord_3706423).sum := by decide
  have hdescent : baseEnd_3706423 < baseStart_3706423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706443 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 3, 2, 2]
def baseStart_3706443 : Nat := 118140960795 + 3706443 * 2 ^ 59
def prefixEnd_3706443 : Nat := 4983230072969 + 3 ^ 40 * 3706443 * 2
def baseEnd_3706443 : Nat := 1903186777492547258416885

theorem tailTrace_3706443 : CollatzResearch.WordTrace tailWord_3706443 prefixEnd_3706443 1903186777492547258416885 := by
  unfold tailWord_3706443
  simp only [CollatzResearch.WordTrace]
  refine ⟨135185082111197495913003983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90123388074131663942002655 135185082111197495913003983)
  ·
    refine ⟨202777623166796243869505975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135185082111197495913003983 202777623166796243869505975)
    ·
      refine ⟨304166434750194365804258963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202777623166796243869505975 304166434750194365804258963)
      ·
        refine ⟨456249652125291548706388445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304166434750194365804258963 456249652125291548706388445)
        ·
          refine ⟨171093619546984330764895667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456249652125291548706388445 171093619546984330764895667)
          ·
            refine ⟨256640429320476496147343501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171093619546984330764895667 256640429320476496147343501)
            ·
              refine ⟨96240160995178686055253813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256640429320476496147343501 96240160995178686055253813)
              ·
                refine ⟨9022515093298001817680045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96240160995178686055253813 9022515093298001817680045)
                ·
                  refine ⟨3383443159986750681630017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9022515093298001817680045 3383443159986750681630017)
                  ·
                    refine ⟨2537582369990063011222513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3383443159986750681630017 2537582369990063011222513)
                    ·
                      refine ⟨1903186777492547258416885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537582369990063011222513 1903186777492547258416885)
                      ·
                        rfl

theorem cell23_3706443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 2, 2].length) (baseStart_3706443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706443 prefixEnd_3706443 := by exact prefixLift 3706443
  have htrace : WordTrace (prefixWord ++ tailWord_3706443) baseStart_3706443 baseEnd_3706443 := by
    simpa [prefixWord, tailWord_3706443, baseEnd_3706443] using wordTrace_append hprefix tailTrace_3706443
  have hstable : (prefixWord ++ tailWord_3706443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706443).length < 2 ^ (prefixWord ++ tailWord_3706443).sum := by decide
  have hdescent : baseEnd_3706443 < baseStart_3706443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706454 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3706454 : Nat := 118140960795 + 3706454 * 2 ^ 59
def prefixEnd_3706454 : Nat := 4983230072969 + 3 ^ 40 * 3706454 * 2
def baseEnd_3706454 : Nat := 1903192425779746715379335

theorem tailTrace_3706454 : CollatzResearch.WordTrace tailWord_3706454 prefixEnd_3706454 1903192425779746715379335 := by
  unfold tailWord_3706454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8449092707134852799478401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90123655542771763194436277 8449092707134852799478401)
  ·
    refine ⟨6336819530351139599608801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8449092707134852799478401 6336819530351139599608801)
    ·
      refine ⟨4752614647763354699706601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6336819530351139599608801 4752614647763354699706601)
      ·
        refine ⟨3564460985822516024779951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4752614647763354699706601 3564460985822516024779951)
        ·
          refine ⟨5346691478733774037169927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3564460985822516024779951 5346691478733774037169927)
          ·
            refine ⟨8020037218100661055754891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346691478733774037169927 8020037218100661055754891)
            ·
              refine ⟨12030055827150991583632337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8020037218100661055754891 12030055827150991583632337)
              ·
                refine ⟨9022541870363243687724253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12030055827150991583632337 9022541870363243687724253)
                ·
                  refine ⟨3383453201386216382896595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9022541870363243687724253 3383453201386216382896595)
                  ·
                    refine ⟨5075179802079324574344893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3383453201386216382896595 5075179802079324574344893)
                    ·
                      refine ⟨1903192425779746715379335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5075179802079324574344893 1903192425779746715379335)
                      ·
                        rfl

theorem cell23_3706454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3706454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706454 prefixEnd_3706454 := by exact prefixLift 3706454
  have htrace : WordTrace (prefixWord ++ tailWord_3706454) baseStart_3706454 baseEnd_3706454 := by
    simpa [prefixWord, tailWord_3706454, baseEnd_3706454] using wordTrace_append hprefix tailTrace_3706454
  have hstable : (prefixWord ++ tailWord_3706454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706454).length < 2 ^ (prefixWord ++ tailWord_3706454).sum := by decide
  have hdescent : baseEnd_3706454 < baseStart_3706454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706460 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_3706460 : Nat := 118140960795 + 3706460 * 2 ^ 59
def prefixEnd_3706460 : Nat := 4983230072969 + 3 ^ 40 * 3706460 * 2
def baseEnd_3706460 : Nat := 1903195506663673691904307

theorem tailTrace_3706460 : CollatzResearch.WordTrace tailWord_3706460 prefixEnd_3706460 1903195506663673691904307 := by
  unfold tailWord_3706460
  simp only [CollatzResearch.WordTrace]
  refine ⟨67592851076067953908186417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90123801434757271877581889 67592851076067953908186417)
  ·
    refine ⟨50694638307050965431139813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67592851076067953908186417 50694638307050965431139813)
    ·
      refine ⟨9505244682572056018338715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50694638307050965431139813 9505244682572056018338715)
      ·
        refine ⟨14257867023858084027508073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9505244682572056018338715 14257867023858084027508073)
        ·
          refine ⟨10693400267893563020631055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14257867023858084027508073 10693400267893563020631055)
          ·
            refine ⟨16040100401840344530946583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10693400267893563020631055 16040100401840344530946583)
            ·
              refine ⟨24060150602760516796419875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16040100401840344530946583 24060150602760516796419875)
              ·
                refine ⟨36090225904140775194629813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24060150602760516796419875 36090225904140775194629813)
                ·
                  refine ⟨3383458678513197674496545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36090225904140775194629813 3383458678513197674496545)
                  ·
                    refine ⟨2537594008884898255872409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3383458678513197674496545 2537594008884898255872409)
                    ·
                      refine ⟨1903195506663673691904307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537594008884898255872409 1903195506663673691904307)
                      ·
                        rfl

theorem cell23_3706460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_3706460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706460 prefixEnd_3706460 := by exact prefixLift 3706460
  have htrace : WordTrace (prefixWord ++ tailWord_3706460) baseStart_3706460 baseEnd_3706460 := by
    simpa [prefixWord, tailWord_3706460, baseEnd_3706460] using wordTrace_append hprefix tailTrace_3706460
  have hstable : (prefixWord ++ tailWord_3706460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706460).length < 2 ^ (prefixWord ++ tailWord_3706460).sum := by decide
  have hdescent : baseEnd_3706460 < baseStart_3706460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706477 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_3706477 : Nat := 118140960795 + 3706477 * 2 ^ 59
def prefixEnd_3706477 : Nat := 4983230072969 + 3 ^ 40 * 3706477 * 2
def baseEnd_3706477 : Nat := 1903204235834800125391729

theorem tailTrace_3706477 : CollatzResearch.WordTrace tailWord_3706477 prefixEnd_3706477 1903204235834800125391729 := by
  unfold tailWord_3706477
  simp only [CollatzResearch.WordTrace]
  refine ⟨135186322193074319719741685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90124214795382879813161123 135186322193074319719741685)
  ·
    refine ⟨12673717705600717473725783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135186322193074319719741685 12673717705600717473725783)
    ·
      refine ⟨19010576558401076210588675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12673717705600717473725783 19010576558401076210588675)
      ·
        refine ⟨28515864837601614315883013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19010576558401076210588675 28515864837601614315883013)
        ·
          refine ⟨5346724657050302684228065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28515864837601614315883013 5346724657050302684228065)
          ·
            refine ⟨4010043492787727013171049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5346724657050302684228065 4010043492787727013171049)
            ·
              refine ⟨3007532619590795259878287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4010043492787727013171049 3007532619590795259878287)
              ·
                refine ⟨4511298929386192889817431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007532619590795259878287 4511298929386192889817431)
                ·
                  refine ⟨6766948394079289334726147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511298929386192889817431 6766948394079289334726147)
                  ·
                    refine ⟨10150422591118934002089221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6766948394079289334726147 10150422591118934002089221)
                    ·
                      refine ⟨1903204235834800125391729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10150422591118934002089221 1903204235834800125391729)
                      ·
                        rfl

theorem cell23_3706477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_3706477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706477 prefixEnd_3706477 := by exact prefixLift 3706477
  have htrace : WordTrace (prefixWord ++ tailWord_3706477) baseStart_3706477 baseEnd_3706477 := by
    simpa [prefixWord, tailWord_3706477, baseEnd_3706477] using wordTrace_append hprefix tailTrace_3706477
  have hstable : (prefixWord ++ tailWord_3706477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706477).length < 2 ^ (prefixWord ++ tailWord_3706477).sum := by decide
  have hdescent : baseEnd_3706477 < baseStart_3706477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706480 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 1, 2, 3]
def baseStart_3706480 : Nat := 118140960795 + 3706480 * 2 ^ 59
def prefixEnd_3706480 : Nat := 4983230072969 + 3 ^ 40 * 3706480 * 2
def baseEnd_3706480 : Nat := 1903205776276763613654215

theorem tailTrace_3706480 : CollatzResearch.WordTrace tailWord_3706480 prefixEnd_3706480 1903205776276763613654215 := by
  unfold tailWord_3706480
  simp only [CollatzResearch.WordTrace]
  refine ⟨67593215806031725616050447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90124287741375634154733929 67593215806031725616050447)
  ·
    refine ⟨101389823709047588424075671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67593215806031725616050447 101389823709047588424075671)
    ·
      refine ⟨152084735563571382636113507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101389823709047588424075671 152084735563571382636113507)
      ·
        refine ⟨228127103345357073954170261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152084735563571382636113507 228127103345357073954170261)
        ·
          refine ⟨10693457969313612841601731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228127103345357073954170261 10693457969313612841601731)
          ·
            refine ⟨16040186953970419262402597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10693457969313612841601731 16040186953970419262402597)
            ·
              refine ⟨3007535053869453611700487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16040186953970419262402597 3007535053869453611700487)
              ·
                refine ⟨4511302580804180417550731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007535053869453611700487 4511302580804180417550731)
                ·
                  refine ⟨6766953871206270626326097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511302580804180417550731 6766953871206270626326097)
                  ·
                    refine ⟨5075215403404702969744573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6766953871206270626326097 5075215403404702969744573)
                    ·
                      refine ⟨1903205776276763613654215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5075215403404702969744573 1903205776276763613654215)
                      ·
                        rfl

theorem cell23_3706480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 2, 3].length) (baseStart_3706480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706480 prefixEnd_3706480 := by exact prefixLift 3706480
  have htrace : WordTrace (prefixWord ++ tailWord_3706480) baseStart_3706480 baseEnd_3706480 := by
    simpa [prefixWord, tailWord_3706480, baseEnd_3706480] using wordTrace_append hprefix tailTrace_3706480
  have hstable : (prefixWord ++ tailWord_3706480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706480).length < 2 ^ (prefixWord ++ tailWord_3706480).sum := by decide
  have hdescent : baseEnd_3706480 < baseStart_3706480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706510 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3706510 : Nat := 118140960795 + 3706510 * 2 ^ 59
def prefixEnd_3706510 : Nat := 4983230072969 + 3 ^ 40 * 3706510 * 2
def baseEnd_3706510 : Nat := 1903221180696398496279077

theorem tailTrace_3706510 : CollatzResearch.WordTrace tailWord_3706510 prefixEnd_3706510 1903221180696398496279077 := by
  unfold tailWord_3706510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16898440725244345794461623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90125017201303177570461989 16898440725244345794461623)
  ·
    refine ⟨25347661087866518691692435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16898440725244345794461623 25347661087866518691692435)
    ·
      refine ⟨38021491631799778037538653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25347661087866518691692435 38021491631799778037538653)
      ·
        refine ⟨14258059361924916764076995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38021491631799778037538653 14258059361924916764076995)
        ·
          refine ⟨21387089042887375146115493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14258059361924916764076995 21387089042887375146115493)
          ·
            refine ⟨4010079195541382839896655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21387089042887375146115493 4010079195541382839896655)
            ·
              refine ⟨6015118793312074259844983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010079195541382839896655 6015118793312074259844983)
              ·
                refine ⟨9022678189968111389767475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6015118793312074259844983 9022678189968111389767475)
                ·
                  refine ⟨13534017284952167084651213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9022678189968111389767475 13534017284952167084651213)
                  ·
                    refine ⟨5075256481857062656744205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13534017284952167084651213 5075256481857062656744205)
                    ·
                      refine ⟨1903221180696398496279077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5075256481857062656744205 1903221180696398496279077)
                      ·
                        rfl

theorem cell23_3706510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3706510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706510 prefixEnd_3706510 := by exact prefixLift 3706510
  have htrace : WordTrace (prefixWord ++ tailWord_3706510) baseStart_3706510 baseEnd_3706510 := by
    simpa [prefixWord, tailWord_3706510, baseEnd_3706510] using wordTrace_append hprefix tailTrace_3706510
  have hstable : (prefixWord ++ tailWord_3706510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706510).length < 2 ^ (prefixWord ++ tailWord_3706510).sum := by decide
  have hdescent : baseEnd_3706510 < baseStart_3706510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706520 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 1, 3, 2]
def baseStart_3706520 : Nat := 118140960795 + 3706520 * 2 ^ 59
def prefixEnd_3706520 : Nat := 4983230072969 + 3 ^ 40 * 3706520 * 2
def baseEnd_3706520 : Nat := 1903226315502943457154031

theorem tailTrace_3706520 : CollatzResearch.WordTrace tailWord_3706520 prefixEnd_3706520 1903226315502943457154031 := by
  unfold tailWord_3706520
  simp only [CollatzResearch.WordTrace]
  refine ⟨67593945265959269031778507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90125260354612358709038009 67593945265959269031778507)
  ·
    refine ⟨101390917898938903547667761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67593945265959269031778507 101390917898938903547667761)
    ·
      refine ⟨76043188424204177660750821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101390917898938903547667761 76043188424204177660750821)
      ·
        refine ⟨14258097829538283311390779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76043188424204177660750821 14258097829538283311390779)
        ·
          refine ⟨21387146744307424967086169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14258097829538283311390779 21387146744307424967086169)
          ·
            refine ⟨16040360058230568725314627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21387146744307424967086169 16040360058230568725314627)
            ·
              refine ⟨24060540087345853087971941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16040360058230568725314627 24060540087345853087971941)
              ·
                refine ⟨4511351266377347453994739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24060540087345853087971941 4511351266377347453994739)
                ·
                  refine ⟨6767026899566021180992109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511351266377347453994739 6767026899566021180992109)
                  ·
                    refine ⟨2537635087337257942872041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6767026899566021180992109 2537635087337257942872041)
                    ·
                      refine ⟨1903226315502943457154031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537635087337257942872041 1903226315502943457154031)
                      ·
                        rfl

theorem cell23_3706520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_3706520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706520 prefixEnd_3706520 := by exact prefixLift 3706520
  have htrace : WordTrace (prefixWord ++ tailWord_3706520) baseStart_3706520 baseEnd_3706520 := by
    simpa [prefixWord, tailWord_3706520, baseEnd_3706520] using wordTrace_append hprefix tailTrace_3706520
  have hstable : (prefixWord ++ tailWord_3706520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706520).length < 2 ^ (prefixWord ++ tailWord_3706520).sum := by decide
  have hdescent : baseEnd_3706520 < baseStart_3706520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706533 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 1, 4, 2]
def baseStart_3706533 : Nat := 118140960795 + 3706533 * 2 ^ 59
def prefixEnd_3706533 : Nat := 4983230072969 + 3 ^ 40 * 3706533 * 2
def baseEnd_3706533 : Nat := 1903232990751451906291471

theorem tailTrace_3706533 : CollatzResearch.WordTrace tailWord_3706533 prefixEnd_3706533 1903232990751451906291471 := by
  unfold tailWord_3706533
  simp only [CollatzResearch.WordTrace]
  refine ⟨135188364680871441283780253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90125576453914294189186835 135188364680871441283780253)
  ·
    refine ⟨50695636755326790481417595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135188364680871441283780253 50695636755326790481417595)
    ·
      refine ⟨76043455132990185722126393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50695636755326790481417595 76043455132990185722126393)
      ·
        refine ⟨57032591349742639291594795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76043455132990185722126393 57032591349742639291594795)
        ·
          refine ⟨85548887024613958937392193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57032591349742639291594795 85548887024613958937392193)
          ·
            refine ⟨64161665268460469203044145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85548887024613958937392193 64161665268460469203044145)
            ·
              refine ⟨48121248951345351902283109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64161665268460469203044145 48121248951345351902283109)
              ·
                refine ⟨9022734178377253481678083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48121248951345351902283109 9022734178377253481678083)
                ·
                  refine ⟨13534101267565880222517125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9022734178377253481678083 13534101267565880222517125)
                  ·
                    refine ⟨2537643987668602541721961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13534101267565880222517125 2537643987668602541721961)
                    ·
                      refine ⟨1903232990751451906291471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537643987668602541721961 1903232990751451906291471)
                      ·
                        rfl

theorem cell23_3706533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_3706533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706533 prefixEnd_3706533 := by exact prefixLift 3706533
  have htrace : WordTrace (prefixWord ++ tailWord_3706533) baseStart_3706533 baseEnd_3706533 := by
    simpa [prefixWord, tailWord_3706533, baseEnd_3706533] using wordTrace_append hprefix tailTrace_3706533
  have hstable : (prefixWord ++ tailWord_3706533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706533).length < 2 ^ (prefixWord ++ tailWord_3706533).sum := by decide
  have hdescent : baseEnd_3706533 < baseStart_3706533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706546 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_3706546 : Nat := 118140960795 + 3706546 * 2 ^ 59
def prefixEnd_3706546 : Nat := 4983230072969 + 3 ^ 40 * 3706546 * 2
def baseEnd_3706546 : Nat := 1903239665999960355428911

theorem tailTrace_3706546 : CollatzResearch.WordTrace tailWord_3706546 prefixEnd_3706546 1903239665999960355428911 := by
  unfold tailWord_3706546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33797209707456086126000873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90125892553216229669335661 33797209707456086126000873)
  ·
    refine ⟨25347907280592064594500655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33797209707456086126000873 25347907280592064594500655)
    ·
      refine ⟨38021860920888096891750983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25347907280592064594500655 38021860920888096891750983)
      ·
        refine ⟨57032791381332145337626475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38021860920888096891750983 57032791381332145337626475)
        ·
          refine ⟨85549187071998218006439713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57032791381332145337626475 85549187071998218006439713)
          ·
            refine ⟨64161890303998663504829785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85549187071998218006439713 64161890303998663504829785)
            ·
              refine ⟨48121417727998997628622339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64161890303998663504829785 48121417727998997628622339)
              ·
                refine ⟨72182126591998496442933509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48121417727998997628622339 72182126591998496442933509)
                ·
                  refine ⟨13534148735999718083050033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72182126591998496442933509 13534148735999718083050033)
                  ·
                    refine ⟨10150611551999788562287525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13534148735999718083050033 10150611551999788562287525)
                    ·
                      refine ⟨1903239665999960355428911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10150611551999788562287525 1903239665999960355428911)
                      ·
                        rfl

theorem cell23_3706546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_3706546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706546 prefixEnd_3706546 := by exact prefixLift 3706546
  have htrace : WordTrace (prefixWord ++ tailWord_3706546) baseStart_3706546 baseEnd_3706546 := by
    simpa [prefixWord, tailWord_3706546, baseEnd_3706546] using wordTrace_append hprefix tailTrace_3706546
  have hstable : (prefixWord ++ tailWord_3706546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706546).length < 2 ^ (prefixWord ++ tailWord_3706546).sum := by decide
  have hdescent : baseEnd_3706546 < baseStart_3706546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706596 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3706596 : Nat := 118140960795 + 3706596 * 2 ^ 59
def prefixEnd_3706596 : Nat := 4983230072969 + 3 ^ 40 * 3706596 * 2
def baseEnd_3706596 : Nat := 1903265340032685159803681

theorem tailTrace_3706596 : CollatzResearch.WordTrace tailWord_3706596 prefixEnd_3706596 1903265340032685159803681 := by
  unfold tailWord_3706596
  simp only [CollatzResearch.WordTrace]
  refine ⟨67595331239821601521661821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90127108319762135362215761 67595331239821601521661821)
  ·
    refine ⟨25348249214933100570623183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67595331239821601521661821 25348249214933100570623183)
    ·
      refine ⟨38022373822399650855934775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25348249214933100570623183 38022373822399650855934775)
      ·
        refine ⟨57033560733599476283902163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38022373822399650855934775 57033560733599476283902163)
        ·
          refine ⟨85550341100399214425853245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57033560733599476283902163 85550341100399214425853245)
          ·
            refine ⟨32081377912649705409694967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85550341100399214425853245 32081377912649705409694967)
            ·
              refine ⟨48122066868974558114542451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32081377912649705409694967 48122066868974558114542451)
              ·
                refine ⟨72183100303461837171813677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48122066868974558114542451 72183100303461837171813677)
                ·
                  refine ⟨27068662613798188939430129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72183100303461837171813677 27068662613798188939430129)
                  ·
                    refine ⟨20301496960348641704572597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27068662613798188939430129 20301496960348641704572597)
                    ·
                      refine ⟨1903265340032685159803681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20301496960348641704572597 1903265340032685159803681)
                      ·
                        rfl

theorem cell23_3706596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3706596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706596 prefixEnd_3706596 := by exact prefixLift 3706596
  have htrace : WordTrace (prefixWord ++ tailWord_3706596) baseStart_3706596 baseEnd_3706596 := by
    simpa [prefixWord, tailWord_3706596, baseEnd_3706596] using wordTrace_append hprefix tailTrace_3706596
  have hstable : (prefixWord ++ tailWord_3706596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706596).length < 2 ^ (prefixWord ++ tailWord_3706596).sum := by decide
  have hdescent : baseEnd_3706596 < baseStart_3706596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706623 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 1, 6, 2]
def baseStart_3706623 : Nat := 118140960795 + 3706623 * 2 ^ 59
def prefixEnd_3706623 : Nat := 4983230072969 + 3 ^ 40 * 3706623 * 2
def baseEnd_3706623 : Nat := 1903279204010356554166057

theorem tailTrace_3706623 : CollatzResearch.WordTrace tailWord_3706623 prefixEnd_3706623 1903279204010356554166057 := by
  unfold tailWord_3706623
  simp only [CollatzResearch.WordTrace]
  refine ⟨135191647250545386654556523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90127764833696924436371015 135191647250545386654556523)
  ·
    refine ⟨202787470875818079981834785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135191647250545386654556523 202787470875818079981834785)
    ·
      refine ⟨152090603156863559986376089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202787470875818079981834785 152090603156863559986376089)
      ·
        refine ⟨114067952367647669989782067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152090603156863559986376089 114067952367647669989782067)
        ·
          refine ⟨171101928551471504984673101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114067952367647669989782067 171101928551471504984673101)
          ·
            refine ⟨64163223206801814369252413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171101928551471504984673101 64163223206801814369252413)
            ·
              refine ⟨24061208702550680388469655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64163223206801814369252413 24061208702550680388469655)
              ·
                refine ⟨36091813053826020582704483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24061208702550680388469655 36091813053826020582704483)
                ·
                  refine ⟨54137719580739030874056725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36091813053826020582704483 54137719580739030874056725)
                  ·
                    refine ⟨2537705605347142072221409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54137719580739030874056725 2537705605347142072221409)
                    ·
                      refine ⟨1903279204010356554166057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537705605347142072221409 1903279204010356554166057)
                      ·
                        rfl

theorem cell23_3706623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_3706623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706623 prefixEnd_3706623 := by exact prefixLift 3706623
  have htrace : WordTrace (prefixWord ++ tailWord_3706623) baseStart_3706623 baseEnd_3706623 := by
    simpa [prefixWord, tailWord_3706623, baseEnd_3706623] using wordTrace_append hprefix tailTrace_3706623
  have hstable : (prefixWord ++ tailWord_3706623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706623).length < 2 ^ (prefixWord ++ tailWord_3706623).sum := by decide
  have hdescent : baseEnd_3706623 < baseStart_3706623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706643 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 3]
def baseStart_3706643 : Nat := 118140960795 + 3706643 * 2 ^ 59
def prefixEnd_3706643 : Nat := 4983230072969 + 3 ^ 40 * 3706643 * 2
def baseEnd_3706643 : Nat := 1903289473623446475915965

theorem tailTrace_3706643 : CollatzResearch.WordTrace tailWord_3706643 prefixEnd_3706643 1903289473623446475915965 := by
  unfold tailWord_3706643
  simp only [CollatzResearch.WordTrace]
  refine ⟨135192376710472930070284583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90128251140315286713523055 135192376710472930070284583)
  ·
    refine ⟨202788565065709395105426875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135192376710472930070284583 202788565065709395105426875)
    ·
      refine ⟨304182847598564092658140313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202788565065709395105426875 304182847598564092658140313)
      ·
        refine ⟨228137135698923069493605235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304182847598564092658140313 228137135698923069493605235)
        ·
          refine ⟨342205703548384604240407853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228137135698923069493605235 342205703548384604240407853)
          ·
            refine ⟨128327138830644226590152945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342205703548384604240407853 128327138830644226590152945)
            ·
              refine ⟨96245354122983169942614709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128327138830644226590152945 96245354122983169942614709)
              ·
                refine ⟨9023001949029672182120129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96245354122983169942614709 9023001949029672182120129)
                ·
                  refine ⟨6767251461772254136590097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9023001949029672182120129 6767251461772254136590097)
                  ·
                    refine ⟨5075438596329190602442573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6767251461772254136590097 5075438596329190602442573)
                    ·
                      refine ⟨1903289473623446475915965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5075438596329190602442573 1903289473623446475915965)
                      ·
                        rfl

theorem cell23_3706643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 3].length) (baseStart_3706643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706643 prefixEnd_3706643 := by exact prefixLift 3706643
  have htrace : WordTrace (prefixWord ++ tailWord_3706643) baseStart_3706643 baseEnd_3706643 := by
    simpa [prefixWord, tailWord_3706643, baseEnd_3706643] using wordTrace_append hprefix tailTrace_3706643
  have hstable : (prefixWord ++ tailWord_3706643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706643).length < 2 ^ (prefixWord ++ tailWord_3706643).sum := by decide
  have hdescent : baseEnd_3706643 < baseStart_3706643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706680 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 6]
def baseStart_3706680 : Nat := 118140960795 + 3706680 * 2 ^ 59
def prefixEnd_3706680 : Nat := 4983230072969 + 3 ^ 40 * 3706680 * 2
def baseEnd_3706680 : Nat := 211478719156406981239255

theorem tailTrace_3706680 : CollatzResearch.WordTrace tailWord_3706680 prefixEnd_3706680 211478719156406981239255 := by
  unfold tailWord_3706680
  simp only [CollatzResearch.WordTrace]
  refine ⟨67596863105669442694690747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90129150807559256926254329 67596863105669442694690747)
  ·
    refine ⟨101395294658504164042036121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67596863105669442694690747 101395294658504164042036121)
    ·
      refine ⟨76046470993878123031527091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101395294658504164042036121 76046470993878123031527091)
      ·
        refine ⟨114069706490817184547290637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76046470993878123031527091 114069706490817184547290637)
        ·
          refine ⟨42776139934056444205233989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114069706490817184547290637 42776139934056444205233989)
          ·
            refine ⟨8020526237635583288481373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42776139934056444205233989 8020526237635583288481373)
            ·
              refine ⟨3007697339113343733180515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8020526237635583288481373 3007697339113343733180515)
              ·
                refine ⟨4511546008670015599770773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007697339113343733180515 4511546008670015599770773)
                ·
                  refine ⟨211478719156406981239255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4511546008670015599770773 211478719156406981239255)
                  ·
                    rfl

theorem cell23_3706680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 6].length) (baseStart_3706680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706680 prefixEnd_3706680 := by exact prefixLift 3706680
  have htrace : WordTrace (prefixWord ++ tailWord_3706680) baseStart_3706680 baseEnd_3706680 := by
    simpa [prefixWord, tailWord_3706680, baseEnd_3706680] using wordTrace_append hprefix tailTrace_3706680
  have hstable : (prefixWord ++ tailWord_3706680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706680).length < 2 ^ (prefixWord ++ tailWord_3706680).sum := by decide
  have hdescent : baseEnd_3706680 < baseStart_3706680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706701 : List Nat := [1, 6, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_3706701 : Nat := 118140960795 + 3706701 * 2 ^ 59
def prefixEnd_3706701 : Nat := 4983230072969 + 3 ^ 40 * 3706701 * 2
def baseEnd_3706701 : Nat := 634439751833802416330233

theorem tailTrace_3706701 : CollatzResearch.WordTrace tailWord_3706701 prefixEnd_3706701 634439751833802416330233 := by
  unfold tailWord_3706701
  simp only [CollatzResearch.WordTrace]
  refine ⟨135194492144262805975895957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90129661429508537317263971 135194492144262805975895957)
  ·
    refine ⟨6337241819262319030120123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135194492144262805975895957 6337241819262319030120123)
    ·
      refine ⟨9505862728893478545180185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6337241819262319030120123 9505862728893478545180185)
      ·
        refine ⟨7129397046670108908885139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9505862728893478545180185 7129397046670108908885139)
        ·
          refine ⟨10694095570005163363327709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7129397046670108908885139 10694095570005163363327709)
          ·
            refine ⟨4010285838751936261247891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10694095570005163363327709 4010285838751936261247891)
            ·
              refine ⟨6015428758127904391871837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010285838751936261247891 6015428758127904391871837)
              ·
                refine ⟨2255785784297964146951939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6015428758127904391871837 2255785784297964146951939)
                ·
                  refine ⟨3383678676446946220427909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255785784297964146951939 3383678676446946220427909)
                  ·
                    refine ⟨634439751833802416330233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3383678676446946220427909 634439751833802416330233)
                    ·
                      rfl

theorem cell23_3706701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_3706701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706701 prefixEnd_3706701 := by exact prefixLift 3706701
  have htrace : WordTrace (prefixWord ++ tailWord_3706701) baseStart_3706701 baseEnd_3706701 := by
    simpa [prefixWord, tailWord_3706701, baseEnd_3706701] using wordTrace_append hprefix tailTrace_3706701
  have hstable : (prefixWord ++ tailWord_3706701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706701).length < 2 ^ (prefixWord ++ tailWord_3706701).sum := by decide
  have hdescent : baseEnd_3706701 < baseStart_3706701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706724 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_3706724 : Nat := 118140960795 + 3706724 * 2 ^ 59
def prefixEnd_3706724 : Nat := 4983230072969 + 3 ^ 40 * 3706724 * 2
def baseEnd_3706724 : Nat := 1903331065556460659003093

theorem tailTrace_3706724 : CollatzResearch.WordTrace tailWord_3706724 prefixEnd_3706724 1903331065556460659003093 := by
  unfold tailWord_3706724
  simp only [CollatzResearch.WordTrace]
  refine ⟨67597665511589740451991613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90130220682119653935988817 67597665511589740451991613)
  ·
    refine ⟨25349124566846152669496855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67597665511589740451991613 25349124566846152669496855)
    ·
      refine ⟨38023686850269229004245283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25349124566846152669496855 38023686850269229004245283)
      ·
        refine ⟨57035530275403843506367925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38023686850269229004245283 57035530275403843506367925)
        ·
          refine ⟨5347080963319110328721993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57035530275403843506367925 5347080963319110328721993)
          ·
            refine ⟨4010310722489332746541495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5347080963319110328721993 4010310722489332746541495)
            ·
              refine ⟨6015466083733999119812243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010310722489332746541495 6015466083733999119812243)
              ·
                refine ⟨9023199125600998679718365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6015466083733999119812243 9023199125600998679718365)
                ·
                  refine ⟨3383699672100374504894387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9023199125600998679718365 3383699672100374504894387)
                  ·
                    refine ⟨5075549508150561757341581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3383699672100374504894387 5075549508150561757341581)
                    ·
                      refine ⟨1903331065556460659003093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5075549508150561757341581 1903331065556460659003093)
                      ·
                        rfl

theorem cell23_3706724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_3706724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706724 prefixEnd_3706724 := by exact prefixLift 3706724
  have htrace : WordTrace (prefixWord ++ tailWord_3706724) baseStart_3706724 baseEnd_3706724 := by
    simpa [prefixWord, tailWord_3706724, baseEnd_3706724] using wordTrace_append hprefix tailTrace_3706724
  have hstable : (prefixWord ++ tailWord_3706724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706724).length < 2 ^ (prefixWord ++ tailWord_3706724).sum := by decide
  have hdescent : baseEnd_3706724 < baseStart_3706724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706764 : List Nat := [2, 2, 1, 2, 1, 2, 1, 7, 1, 2, 2]
def baseStart_3706764 : Nat := 118140960795 + 3706764 * 2 ^ 59
def prefixEnd_3706764 : Nat := 4983230072969 + 3 ^ 40 * 3706764 * 2
def baseEnd_3706764 : Nat := 1903351604782640502502909

theorem tailTrace_3706764 : CollatzResearch.WordTrace tailWord_3706764 prefixEnd_3706764 1903351604782640502502909 := by
  unfold tailWord_3706764
  simp only [CollatzResearch.WordTrace]
  refine ⟨67598394971517283867719673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90131193295356378490292897 67598394971517283867719673)
  ·
    refine ⟨50698796228637962900789755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67598394971517283867719673 50698796228637962900789755)
    ·
      refine ⟨76048194342956944351184633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50698796228637962900789755 76048194342956944351184633)
      ·
        refine ⟨57036145757217708263388475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76048194342956944351184633 57036145757217708263388475)
        ·
          refine ⟨85554218635826562395082713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57036145757217708263388475 85554218635826562395082713)
          ·
            refine ⟨64165663976869921796312035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85554218635826562395082713 64165663976869921796312035)
            ·
              refine ⟨96248495965304882694468053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64165663976869921796312035 96248495965304882694468053)
              ·
                refine ⟨2255824124186833188151595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96248495965304882694468053 2255824124186833188151595)
                ·
                  refine ⟨3383736186280249782227393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255824124186833188151595 3383736186280249782227393)
                  ·
                    refine ⟨2537802139710187336670545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3383736186280249782227393 2537802139710187336670545)
                    ·
                      refine ⟨1903351604782640502502909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537802139710187336670545 1903351604782640502502909)
                      ·
                        rfl

theorem cell23_3706764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_3706764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706764 prefixEnd_3706764 := by exact prefixLift 3706764
  have htrace : WordTrace (prefixWord ++ tailWord_3706764) baseStart_3706764 baseEnd_3706764 := by
    simpa [prefixWord, tailWord_3706764, baseEnd_3706764] using wordTrace_append hprefix tailTrace_3706764
  have hstable : (prefixWord ++ tailWord_3706764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706764).length < 2 ^ (prefixWord ++ tailWord_3706764).sum := by decide
  have hdescent : baseEnd_3706764 < baseStart_3706764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706781 : List Nat := [1, 4, 2, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_3706781 : Nat := 118140960795 + 3706781 * 2 ^ 59
def prefixEnd_3706781 : Nat := 4983230072969 + 3 ^ 40 * 3706781 * 2
def baseEnd_3706781 : Nat := 1903360333953766935990331

theorem tailTrace_3706781 : CollatzResearch.WordTrace tailWord_3706781 prefixEnd_3706781 1903360333953766935990331 := by
  unfold tailWord_3706781
  simp only [CollatzResearch.WordTrace]
  refine ⟨135197409983972979638808197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90131606655981986425872131 135197409983972979638808197)
  ·
    refine ⟨25349514371994933682276537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135197409983972979638808197 25349514371994933682276537)
    ·
      refine ⟨19012135778996200261707403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25349514371994933682276537 19012135778996200261707403)
      ·
        refine ⟨28518203668494300392561105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19012135778996200261707403 28518203668494300392561105)
        ·
          refine ⟨21388652751370725294420829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28518203668494300392561105 21388652751370725294420829)
          ·
            refine ⟨8020744781764021985407811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21388652751370725294420829 8020744781764021985407811)
            ·
              refine ⟨12031117172646032978111717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8020744781764021985407811 12031117172646032978111717)
              ·
                refine ⟨2255834469871131183395947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12031117172646032978111717 2255834469871131183395947)
                ·
                  refine ⟨3383751704806696775093921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255834469871131183395947 3383751704806696775093921)
                  ·
                    refine ⟨2537813778605022581320441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3383751704806696775093921 2537813778605022581320441)
                    ·
                      refine ⟨1903360333953766935990331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537813778605022581320441 1903360333953766935990331)
                      ·
                        rfl

theorem cell23_3706781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_3706781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706781 prefixEnd_3706781 := by exact prefixLift 3706781
  have htrace : WordTrace (prefixWord ++ tailWord_3706781) baseStart_3706781 baseEnd_3706781 := by
    simpa [prefixWord, tailWord_3706781, baseEnd_3706781] using wordTrace_append hprefix tailTrace_3706781
  have hstable : (prefixWord ++ tailWord_3706781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706781).length < 2 ^ (prefixWord ++ tailWord_3706781).sum := by decide
  have hdescent : baseEnd_3706781 < baseStart_3706781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706803 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 4]
def baseStart_3706803 : Nat := 118140960795 + 3706803 * 2 ^ 59
def prefixEnd_3706803 : Nat := 4983230072969 + 3 ^ 40 * 3706803 * 2
def baseEnd_3706803 : Nat := 1903371630528165849915229

theorem tailTrace_3706803 : CollatzResearch.WordTrace tailWord_3706803 prefixEnd_3706803 1903371630528165849915229 := by
  unfold tailWord_3706803
  simp only [CollatzResearch.WordTrace]
  refine ⟨135198212389893277396109063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90132141593262184930739375 135198212389893277396109063)
  ·
    refine ⟨202797318584839916094163595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135198212389893277396109063 202797318584839916094163595)
    ·
      refine ⟨304195977877259874141245393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202797318584839916094163595 304195977877259874141245393)
      ·
        refine ⟨228146983407944905605934045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304195977877259874141245393 228146983407944905605934045)
        ·
          refine ⟨85555118777979339602225267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228146983407944905605934045 85555118777979339602225267)
          ·
            refine ⟨128332678166969009403337901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85555118777979339602225267 128332678166969009403337901)
            ·
              refine ⟨48124754312613378526251713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128332678166969009403337901 48124754312613378526251713)
              ·
                refine ⟨36093565734460033894688785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48124754312613378526251713 36093565734460033894688785)
                ·
                  refine ⟨27070174300845025421016589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36093565734460033894688785 27070174300845025421016589)
                  ·
                    refine ⟨10151315362816884532881221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27070174300845025421016589 10151315362816884532881221)
                    ·
                      refine ⟨1903371630528165849915229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10151315362816884532881221 1903371630528165849915229)
                      ·
                        rfl

theorem cell23_3706803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_3706803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706803 prefixEnd_3706803 := by exact prefixLift 3706803
  have htrace : WordTrace (prefixWord ++ tailWord_3706803) baseStart_3706803 baseEnd_3706803 := by
    simpa [prefixWord, tailWord_3706803, baseEnd_3706803] using wordTrace_append hprefix tailTrace_3706803
  have hstable : (prefixWord ++ tailWord_3706803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706803).length < 2 ^ (prefixWord ++ tailWord_3706803).sum := by decide
  have hdescent : baseEnd_3706803 < baseStart_3706803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706804 : List Nat := [2, 5, 2, 1, 2, 1, 3, 7]
def baseStart_3706804 : Nat := 118140960795 + 3706804 * 2 ^ 59
def prefixEnd_3706804 : Nat := 4983230072969 + 3 ^ 40 * 3706804 * 2
def baseEnd_3706804 : Nat := 70495264592919272074175

theorem tailTrace_3706804 : CollatzResearch.WordTrace tailWord_3706804 prefixEnd_3706804 70495264592919272074175 := by
  unfold tailWord_3706804
  simp only [CollatzResearch.WordTrace]
  refine ⟨67599124431444827283447733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90132165908593103044596977 67599124431444827283447733)
  ·
    refine ⟨6337417915447952557823225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67599124431444827283447733 6337417915447952557823225)
    ·
      refine ⟨4753063436585964418367419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6337417915447952557823225 4753063436585964418367419)
      ·
        refine ⟨7129595154878946627551129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4753063436585964418367419 7129595154878946627551129)
        ·
          refine ⟨5347196366159209970663347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7129595154878946627551129 5347196366159209970663347)
          ·
            refine ⟨8020794549238814955995021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347196366159209970663347 8020794549238814955995021)
            ·
              refine ⟨3007797955964555608498133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8020794549238814955995021 3007797955964555608498133)
              ·
                refine ⟨70495264592919272074175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3007797955964555608498133 70495264592919272074175)
                ·
                  rfl

theorem cell23_3706804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 7].length) (baseStart_3706804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706804 prefixEnd_3706804 := by exact prefixLift 3706804
  have htrace : WordTrace (prefixWord ++ tailWord_3706804) baseStart_3706804 baseEnd_3706804 := by
    simpa [prefixWord, tailWord_3706804, baseEnd_3706804] using wordTrace_append hprefix tailTrace_3706804
  have hstable : (prefixWord ++ tailWord_3706804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706804).length < 2 ^ (prefixWord ++ tailWord_3706804).sum := by decide
  have hdescent : baseEnd_3706804 < baseStart_3706804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706807 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 1, 3, 2]
def baseStart_3706807 : Nat := 118140960795 + 3706807 * 2 ^ 59
def prefixEnd_3706807 : Nat := 4983230072969 + 3 ^ 40 * 3706807 * 2
def baseEnd_3706807 : Nat := 1903373684450783834265211

theorem tailTrace_3706807 : CollatzResearch.WordTrace tailWord_3706807 prefixEnd_3706807 1903373684450783834265211 := by
  unfold tailWord_3706807
  simp only [CollatzResearch.WordTrace]
  refine ⟨135198358281878786079254675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90132238854585857386169783 135198358281878786079254675)
  ·
    refine ⟨202797537422818179118882013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135198358281878786079254675 202797537422818179118882013)
    ·
      refine ⟨76049076533556817169580755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202797537422818179118882013 76049076533556817169580755)
      ·
        refine ⟨114073614800335225754371133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76049076533556817169580755 114073614800335225754371133)
        ·
          refine ⟨42777605550125709657889175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114073614800335225754371133 42777605550125709657889175)
          ·
            refine ⟨64166408325188564486833763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42777605550125709657889175 64166408325188564486833763)
            ·
              refine ⟨96249612487782846730250645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64166408325188564486833763 96249612487782846730250645)
              ·
                refine ⟨4511700585364820940480499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96249612487782846730250645 4511700585364820940480499)
                ·
                  refine ⟨6767550878047231410720749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511700585364820940480499 6767550878047231410720749)
                  ·
                    refine ⟨2537831579267711779020281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6767550878047231410720749 2537831579267711779020281)
                    ·
                      refine ⟨1903373684450783834265211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537831579267711779020281 1903373684450783834265211)
                      ·
                        rfl

theorem cell23_3706807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_3706807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706807 prefixEnd_3706807 := by exact prefixLift 3706807
  have htrace : WordTrace (prefixWord ++ tailWord_3706807) baseStart_3706807 baseEnd_3706807 := by
    simpa [prefixWord, tailWord_3706807, baseEnd_3706807] using wordTrace_append hprefix tailTrace_3706807
  have hstable : (prefixWord ++ tailWord_3706807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706807).length < 2 ^ (prefixWord ++ tailWord_3706807).sum := by decide
  have hdescent : baseEnd_3706807 < baseStart_3706807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706823 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_3706823 : Nat := 118140960795 + 3706823 * 2 ^ 59
def prefixEnd_3706823 : Nat := 4983230072969 + 3 ^ 40 * 3706823 * 2
def baseEnd_3706823 : Nat := 1903381900141255771665137

theorem tailTrace_3706823 : CollatzResearch.WordTrace tailWord_3706823 prefixEnd_3706823 1903381900141255771665137 := by
  unfold tailWord_3706823
  simp only [CollatzResearch.WordTrace]
  refine ⟨135198941849820820811837123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90132627899880547207891415 135198941849820820811837123)
  ·
    refine ⟨202798412774731231217755685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135198941849820820811837123 202798412774731231217755685)
    ·
      refine ⟨38024702395262105853329191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202798412774731231217755685 38024702395262105853329191)
      ·
        refine ⟨57037053592893158779993787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38024702395262105853329191 57037053592893158779993787)
        ·
          refine ⟨85555580389339738169990681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57037053592893158779993787 85555580389339738169990681)
          ·
            refine ⟨64166685292004803627493011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85555580389339738169990681 64166685292004803627493011)
            ·
              refine ⟨96250027938007205441239517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64166685292004803627493011 96250027938007205441239517)
              ·
                refine ⟨36093760476752702040464819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96250027938007205441239517 36093760476752702040464819)
                ·
                  refine ⟨54140640715129053060697229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36093760476752702040464819 54140640715129053060697229)
                  ·
                    refine ⟨20302740268173394897761461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54140640715129053060697229 20302740268173394897761461)
                    ·
                      refine ⟨1903381900141255771665137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20302740268173394897761461 1903381900141255771665137)
                      ·
                        rfl

theorem cell23_3706823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_3706823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706823 prefixEnd_3706823 := by exact prefixLift 3706823
  have htrace : WordTrace (prefixWord ++ tailWord_3706823) baseStart_3706823 baseEnd_3706823 := by
    simpa [prefixWord, tailWord_3706823, baseEnd_3706823] using wordTrace_append hprefix tailTrace_3706823
  have hstable : (prefixWord ++ tailWord_3706823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706823).length < 2 ^ (prefixWord ++ tailWord_3706823).sum := by decide
  have hdescent : baseEnd_3706823 < baseStart_3706823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706824 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 1, 3, 2]
def baseStart_3706824 : Nat := 118140960795 + 3706824 * 2 ^ 59
def prefixEnd_3706824 : Nat := 4983230072969 + 3 ^ 40 * 3706824 * 2
def baseEnd_3706824 : Nat := 1903382413621910267752633

theorem tailTrace_3706824 : CollatzResearch.WordTrace tailWord_3706824 prefixEnd_3706824 1903382413621910267752633 := by
  unfold tailWord_3706824
  simp only [CollatzResearch.WordTrace]
  refine ⟨67599489161408598991311763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90132652215211465321749017 67599489161408598991311763)
  ·
    refine ⟨101399233742112898486967645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67599489161408598991311763 101399233742112898486967645)
    ·
      refine ⟨38024712653292336932612867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101399233742112898486967645 38024712653292336932612867)
      ·
        refine ⟨57037068979938505398919301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38024712653292336932612867 57037068979938505398919301)
        ·
          refine ⟨10694450433738469762297369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57037068979938505398919301 10694450433738469762297369)
          ·
            refine ⟨8020837825303852321723027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10694450433738469762297369 8020837825303852321723027)
            ·
              refine ⟨12031256737955778482584541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8020837825303852321723027 12031256737955778482584541)
              ·
                refine ⟨4511721276733416930969203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12031256737955778482584541 4511721276733416930969203)
                ·
                  refine ⟨6767581915100125396453805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511721276733416930969203 6767581915100125396453805)
                  ·
                    refine ⟨2537843218162547023670177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6767581915100125396453805 2537843218162547023670177)
                    ·
                      refine ⟨1903382413621910267752633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2537843218162547023670177 1903382413621910267752633)
                      ·
                        rfl

theorem cell23_3706824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_3706824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706824 prefixEnd_3706824 := by exact prefixLift 3706824
  have htrace : WordTrace (prefixWord ++ tailWord_3706824) baseStart_3706824 baseEnd_3706824 := by
    simpa [prefixWord, tailWord_3706824, baseEnd_3706824] using wordTrace_append hprefix tailTrace_3706824
  have hstable : (prefixWord ++ tailWord_3706824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706824).length < 2 ^ (prefixWord ++ tailWord_3706824).sum := by decide
  have hdescent : baseEnd_3706824 < baseStart_3706824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706877 : List Nat := [1, 4, 1, 1, 1, 2, 5, 3, 5]
def baseStart_3706877 : Nat := 118140960795 + 3706877 * 2 ^ 59
def prefixEnd_3706877 : Nat := 4983230072969 + 3 ^ 40 * 3706877 * 2
def baseEnd_3706877 : Nat := 211489958677399840043321

theorem tailTrace_3706877 : CollatzResearch.WordTrace tailWord_3706877 prefixEnd_3706877 211489958677399840043321 := by
  unfold tailWord_3706877
  simp only [CollatzResearch.WordTrace]
  refine ⟨135200911391625188034302885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90133940927750125356201923 135200911391625188034302885)
  ·
    refine ⟨25350170885929722756431791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135200911391625188034302885 25350170885929722756431791)
    ·
      refine ⟨38025256328894584134647687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25350170885929722756431791 38025256328894584134647687)
      ·
        refine ⟨57037884493341876201971531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38025256328894584134647687 57037884493341876201971531)
        ·
          refine ⟨85556826740012814302957297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57037884493341876201971531 85556826740012814302957297)
          ·
            refine ⟨64167620055009610727217973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85556826740012814302957297 64167620055009610727217973)
            ·
              refine ⟨6015714380157151005676685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64167620055009610727217973 6015714380157151005676685)
              ·
                refine ⟨2255892892558931627128757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6015714380157151005676685 2255892892558931627128757)
                ·
                  refine ⟨211489958677399840043321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2255892892558931627128757 211489958677399840043321)
                  ·
                    rfl

theorem cell23_3706877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_3706877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706877 prefixEnd_3706877 := by exact prefixLift 3706877
  have htrace : WordTrace (prefixWord ++ tailWord_3706877) baseStart_3706877 baseEnd_3706877 := by
    simpa [prefixWord, tailWord_3706877, baseEnd_3706877] using wordTrace_append hprefix tailTrace_3706877
  have hstable : (prefixWord ++ tailWord_3706877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706877).length < 2 ^ (prefixWord ++ tailWord_3706877).sum := by decide
  have hdescent : baseEnd_3706877 < baseStart_3706877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706883 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 7]
def baseStart_3706883 : Nat := 118140960795 + 3706883 * 2 ^ 59
def prefixEnd_3706883 : Nat := 4983230072969 + 3 ^ 40 * 3706883 * 2
def baseEnd_3706883 : Nat := 1903412708980525536914861

theorem tailTrace_3706883 : CollatzResearch.WordTrace tailWord_3706883 prefixEnd_3706883 1903412708980525536914861 := by
  unfold tailWord_3706883
  simp only [CollatzResearch.WordTrace]
  refine ⟨135201130229603451059021303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90134086819735634039347535 135201130229603451059021303)
  ·
    refine ⟨202801695344405176588531955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135201130229603451059021303 202801695344405176588531955)
    ·
      refine ⟨304202543016607764882797933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202801695344405176588531955 304202543016607764882797933)
      ·
        refine ⟨114075953631227911831049225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304202543016607764882797933 114075953631227911831049225)
        ·
          refine ⟨85556965223420933873286919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114075953631227911831049225 85556965223420933873286919)
          ·
            refine ⟨128335447835131400809930379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85556965223420933873286919 128335447835131400809930379)
            ·
              refine ⟨192503171752697101214895569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128335447835131400809930379 192503171752697101214895569)
              ·
                refine ⟨144377378814522825911171677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192503171752697101214895569 144377378814522825911171677)
                ·
                  refine ⟨54141517055446059716689379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144377378814522825911171677 54141517055446059716689379)
                  ·
                    refine ⟨81212275583169089575034069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54141517055446059716689379 81212275583169089575034069)
                    ·
                      refine ⟨1903412708980525536914861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81212275583169089575034069 1903412708980525536914861)
                      ·
                        rfl

theorem cell23_3706883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_3706883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706883 prefixEnd_3706883 := by exact prefixLift 3706883
  have htrace : WordTrace (prefixWord ++ tailWord_3706883) baseStart_3706883 baseEnd_3706883 := by
    simpa [prefixWord, tailWord_3706883, baseEnd_3706883] using wordTrace_append hprefix tailTrace_3706883
  have hstable : (prefixWord ++ tailWord_3706883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706883).length < 2 ^ (prefixWord ++ tailWord_3706883).sum := by decide
  have hdescent : baseEnd_3706883 < baseStart_3706883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706894 : List Nat := [4, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_3706894 : Nat := 118140960795 + 3706894 * 2 ^ 59
def prefixEnd_3706894 : Nat := 4983230072969 + 3 ^ 40 * 3706894 * 2
def baseEnd_3706894 : Nat := 211490928585302777097479

theorem tailTrace_3706894 : CollatzResearch.WordTrace tailWord_3706894 prefixEnd_3706894 211490928585302777097479 := by
  unfold tailWord_3706894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16900191429070449992208967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90134354288375733291781157 16900191429070449992208967)
  ·
    refine ⟨25350287143605674988313451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16900191429070449992208967 25350287143605674988313451)
    ·
      refine ⟨38025430715408512482470177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25350287143605674988313451 38025430715408512482470177)
      ·
        refine ⟨28519073036556384361852633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38025430715408512482470177 28519073036556384361852633)
        ·
          refine ⟨21389304777417288271389475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28519073036556384361852633 21389304777417288271389475)
          ·
            refine ⟨32083957166125932407084213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21389304777417288271389475 32083957166125932407084213)
            ·
              refine ⟨3007870984324306163164145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32083957166125932407084213 3007870984324306163164145)
              ·
                refine ⟨2255903238243229622373109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3007870984324306163164145 2255903238243229622373109)
                ·
                  refine ⟨211490928585302777097479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2255903238243229622373109 211490928585302777097479)
                  ·
                    rfl

theorem cell23_3706894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_3706894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706894 prefixEnd_3706894 := by exact prefixLift 3706894
  have htrace : WordTrace (prefixWord ++ tailWord_3706894) baseStart_3706894 baseEnd_3706894 := by
    simpa [prefixWord, tailWord_3706894, baseEnd_3706894] using wordTrace_append hprefix tailTrace_3706894
  have hstable : (prefixWord ++ tailWord_3706894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706894).length < 2 ^ (prefixWord ++ tailWord_3706894).sum := by decide
  have hdescent : baseEnd_3706894 < baseStart_3706894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706940 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3706940 : Nat := 118140960795 + 3706940 * 2 ^ 59
def prefixEnd_3706940 : Nat := 4983230072969 + 3 ^ 40 * 3706940 * 2
def baseEnd_3706940 : Nat := 1903441977377831813902099

theorem tailTrace_3706940 : CollatzResearch.WordTrace tailWord_3706940 prefixEnd_3706940 1903441977377831813902099 := by
  unfold tailWord_3706940
  simp only [CollatzResearch.WordTrace]
  refine ⟨67601604595198474896923137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90135472793597966529230849 67601604595198474896923137)
  ·
    refine ⟨50701203446398856172692353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67601604595198474896923137 50701203446398856172692353)
    ·
      refine ⟨38025902584799142129519265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50701203446398856172692353 38025902584799142129519265)
      ·
        refine ⟨28519426938599356597139449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38025902584799142129519265 28519426938599356597139449)
        ·
          refine ⟨21389570203949517447854587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28519426938599356597139449 21389570203949517447854587)
          ·
            refine ⟨32084355305924276171781881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21389570203949517447854587 32084355305924276171781881)
            ·
              refine ⟨24063266479443207128836411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32084355305924276171781881 24063266479443207128836411)
              ·
                refine ⟨36094899719164810693254617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24063266479443207128836411 36094899719164810693254617)
                ·
                  refine ⟨27071174789373608019940963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36094899719164810693254617 27071174789373608019940963)
                  ·
                    refine ⟨40606762184060412029911445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27071174789373608019940963 40606762184060412029911445)
                    ·
                      refine ⟨1903441977377831813902099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40606762184060412029911445 1903441977377831813902099)
                      ·
                        rfl

theorem cell23_3706940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3706940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706940 prefixEnd_3706940 := by exact prefixLift 3706940
  have htrace : WordTrace (prefixWord ++ tailWord_3706940) baseStart_3706940 baseEnd_3706940 := by
    simpa [prefixWord, tailWord_3706940, baseEnd_3706940] using wordTrace_append hprefix tailTrace_3706940
  have hstable : (prefixWord ++ tailWord_3706940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706940).length < 2 ^ (prefixWord ++ tailWord_3706940).sum := by decide
  have hdescent : baseEnd_3706940 < baseStart_3706940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706960 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 3]
def baseStart_3706960 : Nat := 118140960795 + 3706960 * 2 ^ 59
def prefixEnd_3706960 : Nat := 4983230072969 + 3 ^ 40 * 3706960 * 2
def baseEnd_3706960 : Nat := 1903452246990921735652007

theorem tailTrace_3706960 : CollatzResearch.WordTrace tailWord_3706960 prefixEnd_3706960 1903452246990921735652007 := by
  unfold tailWord_3706960
  simp only [CollatzResearch.WordTrace]
  refine ⟨67601969325162246604787167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90135959100216328806382889 67601969325162246604787167)
  ·
    refine ⟨101402953987743369907180751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67601969325162246604787167 101402953987743369907180751)
    ·
      refine ⟨152104430981615054860771127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101402953987743369907180751 152104430981615054860771127)
      ·
        refine ⟨228156646472422582291156691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152104430981615054860771127 228156646472422582291156691)
        ·
          refine ⟨342234969708633873436735037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228156646472422582291156691 342234969708633873436735037)
          ·
            refine ⟨128338113640737702538775639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342234969708633873436735037 128338113640737702538775639)
            ·
              refine ⟨192507170461106553808163459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128338113640737702538775639 192507170461106553808163459)
              ·
                refine ⟨288760755691659830712245189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192507170461106553808163459 288760755691659830712245189)
                ·
                  refine ⟨54142641692186218258545973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288760755691659830712245189 54142641692186218258545973)
                  ·
                    refine ⟨5075872658642457961738685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54142641692186218258545973 5075872658642457961738685)
                    ·
                      refine ⟨1903452246990921735652007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5075872658642457961738685 1903452246990921735652007)
                      ·
                        rfl

theorem cell23_3706960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 3].length) (baseStart_3706960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706960 prefixEnd_3706960 := by exact prefixLift 3706960
  have htrace : WordTrace (prefixWord ++ tailWord_3706960) baseStart_3706960 baseEnd_3706960 := by
    simpa [prefixWord, tailWord_3706960, baseEnd_3706960] using wordTrace_append hprefix tailTrace_3706960
  have hstable : (prefixWord ++ tailWord_3706960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706960).length < 2 ^ (prefixWord ++ tailWord_3706960).sum := by decide
  have hdescent : baseEnd_3706960 < baseStart_3706960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706978 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3706978 : Nat := 118140960795 + 3706978 * 2 ^ 59
def prefixEnd_3706978 : Nat := 4983230072969 + 3 ^ 40 * 3706978 * 2
def baseEnd_3706978 : Nat := 1903461489642702665226925

theorem tailTrace_3706978 : CollatzResearch.WordTrace tailWord_3706978 prefixEnd_3706978 1903461489642702665226925 := by
  unfold tailWord_3706978
  simp only [CollatzResearch.WordTrace]
  refine ⟨33801148791064820570932397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90136396776172854855819725 33801148791064820570932397)
  ·
    refine ⟨12675430796649307714099649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33801148791064820570932397 12675430796649307714099649)
    ·
      refine ⟨9506573097486980785574737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12675430796649307714099649 9506573097486980785574737)
      ·
        refine ⟨7129929823115235589181053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9506573097486980785574737 7129929823115235589181053)
        ·
          refine ⟨2673723683668213345942895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7129929823115235589181053 2673723683668213345942895)
          ·
            refine ⟨4010585525502320018914343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673723683668213345942895 4010585525502320018914343)
            ·
              refine ⟨6015878288253480028371515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010585525502320018914343 6015878288253480028371515)
              ·
                refine ⟨9023817432380220042557273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6015878288253480028371515 9023817432380220042557273)
                ·
                  refine ⟨6767863074285165031917955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9023817432380220042557273 6767863074285165031917955)
                  ·
                    refine ⟨10151794611427747547876933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6767863074285165031917955 10151794611427747547876933)
                    ·
                      refine ⟨1903461489642702665226925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10151794611427747547876933 1903461489642702665226925)
                      ·
                        rfl

theorem cell23_3706978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3706978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3706978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3706978 prefixEnd_3706978 := by exact prefixLift 3706978
  have htrace : WordTrace (prefixWord ++ tailWord_3706978) baseStart_3706978 baseEnd_3706978 := by
    simpa [prefixWord, tailWord_3706978, baseEnd_3706978] using wordTrace_append hprefix tailTrace_3706978
  have hstable : (prefixWord ++ tailWord_3706978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706978).length < 2 ^ (prefixWord ++ tailWord_3706978).sum := by decide
  have hdescent : baseEnd_3706978 < baseStart_3706978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707011 : List Nat := [1, 1, 1, 3, 3, 3, 2, 4, 1, 1, 3]
def baseStart_3707011 : Nat := 118140960795 + 3707011 * 2 ^ 59
def prefixEnd_3707011 : Nat := 4983230072969 + 3 ^ 40 * 3707011 * 2
def baseEnd_3707011 : Nat := 1903478434504301036114273

theorem tailTrace_3707011 : CollatzResearch.WordTrace tailWord_3707011 prefixEnd_3707011 1903478434504301036114273 := by
  unfold tailWord_3707011
  simp only [CollatzResearch.WordTrace]
  refine ⟨135205798773139728919680887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90137199182093152613120591 135205798773139728919680887)
  ·
    refine ⟨202808698159709593379521331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135205798773139728919680887 202808698159709593379521331)
    ·
      refine ⟨304213047239564390069281997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202808698159709593379521331 304213047239564390069281997)
      ·
        refine ⟨114079892714836646275980749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304213047239564390069281997 114079892714836646275980749)
        ·
          refine ⟨42779959768063742353492781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114079892714836646275980749 42779959768063742353492781)
          ·
            refine ⟨16042484913023903382559793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42779959768063742353492781 16042484913023903382559793)
            ·
              refine ⟨12031863684767927536919845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16042484913023903382559793 12031863684767927536919845)
              ·
                refine ⟨2255974440893986413172471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12031863684767927536919845 2255974440893986413172471)
                ·
                  refine ⟨3383961661340979619758707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255974440893986413172471 3383961661340979619758707)
                  ·
                    refine ⟨5075942492011469429638061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3383961661340979619758707 5075942492011469429638061)
                    ·
                      refine ⟨1903478434504301036114273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5075942492011469429638061 1903478434504301036114273)
                      ·
                        rfl

theorem cell23_3707011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 1, 1, 3].length) (baseStart_3707011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707011 prefixEnd_3707011 := by exact prefixLift 3707011
  have htrace : WordTrace (prefixWord ++ tailWord_3707011) baseStart_3707011 baseEnd_3707011 := by
    simpa [prefixWord, tailWord_3707011, baseEnd_3707011] using wordTrace_append hprefix tailTrace_3707011
  have hstable : (prefixWord ++ tailWord_3707011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707011).length < 2 ^ (prefixWord ++ tailWord_3707011).sum := by decide
  have hdescent : baseEnd_3707011 < baseStart_3707011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707101 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3707101 : Nat := 118140960795 + 3707101 * 2 ^ 59
def prefixEnd_3707101 : Nat := 4983230072969 + 3 ^ 40 * 3707101 * 2
def baseEnd_3707101 : Nat := 1903524647763205683988859

theorem tailTrace_3707101 : CollatzResearch.WordTrace tailWord_3707101 prefixEnd_3707101 1903524647763205683988859 := by
  unfold tailWord_3707101
  simp only [CollatzResearch.WordTrace]
  refine ⟨135209081342813674290457157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90139387561875782860304771 135209081342813674290457157)
  ·
    refine ⟨25351702751777563929460717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135209081342813674290457157 25351702751777563929460717)
    ·
      refine ⟨9506888531916586473547769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25351702751777563929460717 9506888531916586473547769)
      ·
        refine ⟨7130166398937439855160827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9506888531916586473547769 7130166398937439855160827)
        ·
          refine ⟨10695249598406159782741241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7130166398937439855160827 10695249598406159782741241)
          ·
            refine ⟨8021437198804619837055931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10695249598406159782741241 8021437198804619837055931)
            ·
              refine ⟨12032155798206929755583897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8021437198804619837055931 12032155798206929755583897)
              ·
                refine ⟨9024116848655197316687923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12032155798206929755583897 9024116848655197316687923)
                ·
                  refine ⟨13536175272982795975031885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9024116848655197316687923 13536175272982795975031885)
                  ·
                    refine ⟨5076065727368548490636957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13536175272982795975031885 5076065727368548490636957)
                    ·
                      refine ⟨1903524647763205683988859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5076065727368548490636957 1903524647763205683988859)
                      ·
                        rfl

theorem cell23_3707101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3707101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707101 prefixEnd_3707101 := by exact prefixLift 3707101
  have htrace : WordTrace (prefixWord ++ tailWord_3707101) baseStart_3707101 baseEnd_3707101 := by
    simpa [prefixWord, tailWord_3707101, baseEnd_3707101] using wordTrace_append hprefix tailTrace_3707101
  have hstable : (prefixWord ++ tailWord_3707101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707101).length < 2 ^ (prefixWord ++ tailWord_3707101).sum := by decide
  have hdescent : baseEnd_3707101 < baseStart_3707101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707134 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3707134 : Nat := 118140960795 + 3707134 * 2 ^ 59
def prefixEnd_3707134 : Nat := 4983230072969 + 3 ^ 40 * 3707134 * 2
def baseEnd_3707134 : Nat := 634513864208268018292069

theorem tailTrace_3707134 : CollatzResearch.WordTrace tailWord_3707134 prefixEnd_3707134 634513864208268018292069 := by
  unfold tailWord_3707134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16901285618961765115801057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90140189967796080617605637 16901285618961765115801057)
  ·
    refine ⟨12675964214221323836850793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16901285618961765115801057 12675964214221323836850793)
    ·
      refine ⟨9506973160665992877638095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12675964214221323836850793 9506973160665992877638095)
      ·
        refine ⟨14260459740998989316457143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9506973160665992877638095 14260459740998989316457143)
        ·
          refine ⟨21390689611498483974685715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14260459740998989316457143 21390689611498483974685715)
          ·
            refine ⟨32086034417247725962028573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21390689611498483974685715 32086034417247725962028573)
            ·
              refine ⟨12032262906467897235760715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32086034417247725962028573 12032262906467897235760715)
              ·
                refine ⟨18048394359701845853641073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12032262906467897235760715 18048394359701845853641073)
                ·
                  refine ⟨13536295769776384390230805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18048394359701845853641073 13536295769776384390230805)
                  ·
                    refine ⟨634513864208268018292069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13536295769776384390230805 634513864208268018292069)
                    ·
                      rfl

theorem cell23_3707134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3707134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707134 prefixEnd_3707134 := by exact prefixLift 3707134
  have htrace : WordTrace (prefixWord ++ tailWord_3707134) baseStart_3707134 baseEnd_3707134 := by
    simpa [prefixWord, tailWord_3707134, baseEnd_3707134] using wordTrace_append hprefix tailTrace_3707134
  have hstable : (prefixWord ++ tailWord_3707134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707134).length < 2 ^ (prefixWord ++ tailWord_3707134).sum := by decide
  have hdescent : baseEnd_3707134 < baseStart_3707134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707147 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 7]
def baseStart_3707147 : Nat := 118140960795 + 3707147 * 2 ^ 59
def prefixEnd_3707147 : Nat := 4983230072969 + 3 ^ 40 * 3707147 * 2
def baseEnd_3707147 : Nat := 211505363097034722668183

theorem tailTrace_3707147 : CollatzResearch.WordTrace tailWord_3707147 prefixEnd_3707147 211505363097034722668183 := by
  unfold tailWord_3707147
  simp only [CollatzResearch.WordTrace]
  refine ⟨135210759100647024146631695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90140506067098016097754463 135210759100647024146631695)
  ·
    refine ⟨202816138650970536219947543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135210759100647024146631695 202816138650970536219947543)
    ·
      refine ⟨304224207976455804329921315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202816138650970536219947543 304224207976455804329921315)
      ·
        refine ⟨456336311964683706494881973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304224207976455804329921315 456336311964683706494881973)
        ·
          refine ⟨42781529246689097483895185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 456336311964683706494881973 42781529246689097483895185)
          ·
            refine ⟨32086146935016823112921389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42781529246689097483895185 32086146935016823112921389)
            ·
              refine ⟨12032305100631308667345521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32086146935016823112921389 12032305100631308667345521)
              ·
                refine ⟨9024228825473481500509141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12032305100631308667345521 9024228825473481500509141)
                ·
                  refine ⟨211505363097034722668183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9024228825473481500509141 211505363097034722668183)
                  ·
                    rfl

theorem cell23_3707147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 7].length) (baseStart_3707147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707147 prefixEnd_3707147 := by exact prefixLift 3707147
  have htrace : WordTrace (prefixWord ++ tailWord_3707147) baseStart_3707147 baseEnd_3707147 := by
    simpa [prefixWord, tailWord_3707147, baseEnd_3707147] using wordTrace_append hprefix tailTrace_3707147
  have hstable : (prefixWord ++ tailWord_3707147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707147).length < 2 ^ (prefixWord ++ tailWord_3707147).sum := by decide
  have hdescent : baseEnd_3707147 < baseStart_3707147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707162 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2]
def baseStart_3707162 : Nat := 118140960795 + 3707162 * 2 ^ 59
def prefixEnd_3707162 : Nat := 4983230072969 + 3 ^ 40 * 3707162 * 2
def baseEnd_3707162 : Nat := 1903555970083129945326079

theorem tailTrace_3707162 : CollatzResearch.WordTrace tailWord_3707162 prefixEnd_3707162 1903555970083129945326079 := by
  unfold tailWord_3707162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33802826548898170427106935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90140870797061787805618493 33802826548898170427106935)
  ·
    refine ⟨50704239823347255640660403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33802826548898170427106935 50704239823347255640660403)
    ·
      refine ⟨76056359735020883460990605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50704239823347255640660403 76056359735020883460990605)
      ·
        refine ⟨28521134900632831297871477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76056359735020883460990605 28521134900632831297871477)
        ·
          refine ⟨2673856396934327934175451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28521134900632831297871477 2673856396934327934175451)
          ·
            refine ⟨4010784595401491901263177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673856396934327934175451 4010784595401491901263177)
            ·
              refine ⟨3008088446551118925947383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4010784595401491901263177 3008088446551118925947383)
              ·
                refine ⟨4512132669826678388921075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008088446551118925947383 4512132669826678388921075)
                ·
                  refine ⟨6768199004740017583381613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512132669826678388921075 6768199004740017583381613)
                  ·
                    refine ⟨2538074626777506593768105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6768199004740017583381613 2538074626777506593768105)
                    ·
                      refine ⟨1903555970083129945326079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538074626777506593768105 1903555970083129945326079)
                      ·
                        rfl

theorem cell23_3707162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_3707162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707162 prefixEnd_3707162 := by exact prefixLift 3707162
  have htrace : WordTrace (prefixWord ++ tailWord_3707162) baseStart_3707162 baseEnd_3707162 := by
    simpa [prefixWord, tailWord_3707162, baseEnd_3707162] using wordTrace_append hprefix tailTrace_3707162
  have hstable : (prefixWord ++ tailWord_3707162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707162).length < 2 ^ (prefixWord ++ tailWord_3707162).sum := by decide
  have hdescent : baseEnd_3707162 < baseStart_3707162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707184 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 2, 5, 2]
def baseStart_3707184 : Nat := 118140960795 + 3707184 * 2 ^ 59
def prefixEnd_3707184 : Nat := 4983230072969 + 3 ^ 40 * 3707184 * 2
def baseEnd_3707184 : Nat := 1903567266657528859250977

theorem tailTrace_3707184 : CollatzResearch.WordTrace tailWord_3707184 prefixEnd_3707184 1903567266657528859250977 := by
  unfold tailWord_3707184
  simp only [CollatzResearch.WordTrace]
  refine ⟨67606054300756489732864303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90141405734341986310485737 67606054300756489732864303)
  ·
    refine ⟨101409081451134734599296455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67606054300756489732864303 101409081451134734599296455)
    ·
      refine ⟨152113622176702101898944683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101409081451134734599296455 152113622176702101898944683)
      ·
        refine ⟨228170433265053152848417025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152113622176702101898944683 228170433265053152848417025)
        ·
          refine ⟨171127824948789864636312769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228170433265053152848417025 171127824948789864636312769)
          ·
            refine ⟨128345868711592398477234577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171127824948789864636312769 128345868711592398477234577)
            ·
              refine ⟨96259401533694298857925933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128345868711592398477234577 96259401533694298857925933)
              ·
                refine ⟨36097275575135362071722225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96259401533694298857925933 36097275575135362071722225)
                ·
                  refine ⟨27072956681351521553791669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36097275575135362071722225 27072956681351521553791669)
                  ·
                    refine ⟨2538089688876705145667969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27072956681351521553791669 2538089688876705145667969)
                    ·
                      refine ⟨1903567266657528859250977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538089688876705145667969 1903567266657528859250977)
                      ·
                        rfl

theorem cell23_3707184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 5, 2].length) (baseStart_3707184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707184 prefixEnd_3707184 := by exact prefixLift 3707184
  have htrace : WordTrace (prefixWord ++ tailWord_3707184) baseStart_3707184 baseEnd_3707184 := by
    simpa [prefixWord, tailWord_3707184, baseEnd_3707184] using wordTrace_append hprefix tailTrace_3707184
  have hstable : (prefixWord ++ tailWord_3707184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707184).length < 2 ^ (prefixWord ++ tailWord_3707184).sum := by decide
  have hdescent : baseEnd_3707184 < baseStart_3707184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707187 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 7]
def baseStart_3707187 : Nat := 118140960795 + 3707187 * 2 ^ 59
def prefixEnd_3707187 : Nat := 4983230072969 + 3 ^ 40 * 3707187 * 2
def baseEnd_3707187 : Nat := 1903568807099492347513463

theorem tailTrace_3707187 : CollatzResearch.WordTrace tailWord_3707187 prefixEnd_3707187 1903568807099492347513463 := by
  unfold tailWord_3707187
  simp only [CollatzResearch.WordTrace]
  refine ⟨135212218020502110978087815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90141478680334740652058543 135212218020502110978087815)
  ·
    refine ⟨202818327030753166467131723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135212218020502110978087815 202818327030753166467131723)
    ·
      refine ⟨304227490546129749700697585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202818327030753166467131723 304227490546129749700697585)
      ·
        refine ⟨228170617909597312275523189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304227490546129749700697585 228170617909597312275523189)
        ·
          refine ⟨21390995429024748025830299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228170617909597312275523189 21390995429024748025830299)
          ·
            refine ⟨32086493143537122038745449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21390995429024748025830299 32086493143537122038745449)
            ·
              refine ⟨24064869857652841529059087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32086493143537122038745449 24064869857652841529059087)
              ·
                refine ⟨36097304786479262293588631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24064869857652841529059087 36097304786479262293588631)
                ·
                  refine ⟨54145957179718893440382947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36097304786479262293588631 54145957179718893440382947)
                  ·
                    refine ⟨81218935769578340160574421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54145957179718893440382947 81218935769578340160574421)
                    ·
                      refine ⟨1903568807099492347513463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81218935769578340160574421 1903568807099492347513463)
                      ·
                        rfl

theorem cell23_3707187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_3707187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707187 prefixEnd_3707187 := by exact prefixLift 3707187
  have htrace : WordTrace (prefixWord ++ tailWord_3707187) baseStart_3707187 baseEnd_3707187 := by
    simpa [prefixWord, tailWord_3707187, baseEnd_3707187] using wordTrace_append hprefix tailTrace_3707187
  have hstable : (prefixWord ++ tailWord_3707187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707187).length < 2 ^ (prefixWord ++ tailWord_3707187).sum := by decide
  have hdescent : baseEnd_3707187 < baseStart_3707187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707207 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 2, 8]
def baseStart_3707207 : Nat := 118140960795 + 3707207 * 2 ^ 59
def prefixEnd_3707207 : Nat := 4983230072969 + 3 ^ 40 * 3707207 * 2
def baseEnd_3707207 : Nat := 634526358904194089754457

theorem tailTrace_3707207 : CollatzResearch.WordTrace tailWord_3707207 prefixEnd_3707207 634526358904194089754457 := by
  unfold tailWord_3707207
  simp only [CollatzResearch.WordTrace]
  refine ⟨135212947480429654393815875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90141964986953102929210583 135212947480429654393815875)
  ·
    refine ⟨202819421220644481590723813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135212947480429654393815875 202819421220644481590723813)
    ·
      refine ⟨38028641478870840298260715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202819421220644481590723813 38028641478870840298260715)
      ·
        refine ⟨57042962218306260447391073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38028641478870840298260715 57042962218306260447391073)
        ·
          refine ⟨42782221663729695335543305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57042962218306260447391073 42782221663729695335543305)
          ·
            refine ⟨32086666247797271501657479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42782221663729695335543305 32086666247797271501657479)
            ·
              refine ⟨48129999371695907252486219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32086666247797271501657479 48129999371695907252486219)
              ·
                refine ⟨72194999057543860878729329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48129999371695907252486219 72194999057543860878729329)
                ·
                  refine ⟨54146249293157895659046997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72194999057543860878729329 54146249293157895659046997)
                  ·
                    refine ⟨634526358904194089754457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54146249293157895659046997 634526358904194089754457)
                    ·
                      rfl

theorem cell23_3707207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_3707207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707207 prefixEnd_3707207 := by exact prefixLift 3707207
  have htrace : WordTrace (prefixWord ++ tailWord_3707207) baseStart_3707207 baseEnd_3707207 := by
    simpa [prefixWord, tailWord_3707207, baseEnd_3707207] using wordTrace_append hprefix tailTrace_3707207
  have hstable : (prefixWord ++ tailWord_3707207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707207).length < 2 ^ (prefixWord ++ tailWord_3707207).sum := by decide
  have hdescent : baseEnd_3707207 < baseStart_3707207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707228 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3707228 : Nat := 118140960795 + 3707228 * 2 ^ 59
def prefixEnd_3707228 : Nat := 4983230072969 + 3 ^ 40 * 3707228 * 2
def baseEnd_3707228 : Nat := 634529953268775562366925

theorem tailTrace_3707228 : CollatzResearch.WordTrace tailWord_3707228 prefixEnd_3707228 634529953268775562366925 := by
  unfold tailWord_3707228
  simp only [CollatzResearch.WordTrace]
  refine ⟨67606856706676787490165169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90142475608902383320220225 67606856706676787490165169)
  ·
    refine ⟨50705142530007590617623877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67606856706676787490165169 50705142530007590617623877)
    ·
      refine ⟨9507214224376423240804477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50705142530007590617623877 9507214224376423240804477)
      ·
        refine ⟨3565205334141158715301679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9507214224376423240804477 3565205334141158715301679)
        ·
          refine ⟨5347808001211738072952519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565205334141158715301679 5347808001211738072952519)
          ·
            refine ⟨8021712001817607109428779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347808001211738072952519 8021712001817607109428779)
            ·
              refine ⟨12032568002726410664143169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8021712001817607109428779 12032568002726410664143169)
              ·
                refine ⟨9024426002044807998107377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12032568002726410664143169 9024426002044807998107377)
                ·
                  refine ⟨6768319501533605998580533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9024426002044807998107377 6768319501533605998580533)
                  ·
                    refine ⟨634529953268775562366925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6768319501533605998580533 634529953268775562366925)
                    ·
                      rfl

theorem cell23_3707228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3707228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707228 prefixEnd_3707228 := by exact prefixLift 3707228
  have htrace : WordTrace (prefixWord ++ tailWord_3707228) baseStart_3707228 baseEnd_3707228 := by
    simpa [prefixWord, tailWord_3707228, baseEnd_3707228] using wordTrace_append hprefix tailTrace_3707228
  have hstable : (prefixWord ++ tailWord_3707228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707228).length < 2 ^ (prefixWord ++ tailWord_3707228).sum := by decide
  have hdescent : baseEnd_3707228 < baseStart_3707228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707298 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_3707298 : Nat := 118140960795 + 3707298 * 2 ^ 59
def prefixEnd_3707298 : Nat := 4983230072969 + 3 ^ 40 * 3707298 * 2
def baseEnd_3707298 : Nat := 1903625803452141413225453

theorem tailTrace_3707298 : CollatzResearch.WordTrace tailWord_3707298 prefixEnd_3707298 1903625803452141413225453 := by
  unfold tailWord_3707298
  simp only [CollatzResearch.WordTrace]
  refine ⟨33804066630774994233844637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90144177682066651290252365 33804066630774994233844637)
  ·
    refine ⟨12676524986540622837691739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33804066630774994233844637 12676524986540622837691739)
    ·
      refine ⟨19014787479810934256537609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12676524986540622837691739 19014787479810934256537609)
      ·
        refine ⟨14261090609858200692403207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19014787479810934256537609 14261090609858200692403207)
        ·
          refine ⟨21391635914787301038604811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14261090609858200692403207 21391635914787301038604811)
          ·
            refine ⟨32087453872180951557907217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21391635914787301038604811 32087453872180951557907217)
            ·
              refine ⟨24065590404135713668430413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32087453872180951557907217 24065590404135713668430413)
              ·
                refine ⟨9024596401550892625661405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24065590404135713668430413 9024596401550892625661405)
                ·
                  refine ⟨3384223650581584734623027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9024596401550892625661405 3384223650581584734623027)
                  ·
                    refine ⟨5076335475872377101934541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3384223650581584734623027 5076335475872377101934541)
                    ·
                      refine ⟨1903625803452141413225453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5076335475872377101934541 1903625803452141413225453)
                      ·
                        rfl

theorem cell23_3707298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_3707298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707298 prefixEnd_3707298 := by exact prefixLift 3707298
  have htrace : WordTrace (prefixWord ++ tailWord_3707298) baseStart_3707298 baseEnd_3707298 := by
    simpa [prefixWord, tailWord_3707298, baseEnd_3707298] using wordTrace_append hprefix tailTrace_3707298
  have hstable : (prefixWord ++ tailWord_3707298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707298).length < 2 ^ (prefixWord ++ tailWord_3707298).sum := by decide
  have hdescent : baseEnd_3707298 < baseStart_3707298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707321 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3707321 : Nat := 118140960795 + 3707321 * 2 ^ 59
def prefixEnd_3707321 : Nat := 4983230072969 + 3 ^ 40 * 3707321 * 2
def baseEnd_3707321 : Nat := 1903637613507194823237847

theorem tailTrace_3707321 : CollatzResearch.WordTrace tailWord_3707321 prefixEnd_3707321 1903637613507194823237847 := by
  unfold tailWord_3707321
  simp only [CollatzResearch.WordTrace]
  refine ⟨135217105402016651863465817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90144736934677767908977211 135217105402016651863465817)
  ·
    refine ⟨101412829051512488897599363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135217105402016651863465817 101412829051512488897599363)
    ·
      refine ⟨152119243577268733346399045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101412829051512488897599363 152119243577268733346399045)
      ·
        refine ⟨28522358170737887502449821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152119243577268733346399045 28522358170737887502449821)
        ·
          refine ⟨10695884314026707813418683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28522358170737887502449821 10695884314026707813418683)
          ·
            refine ⟨16043826471040061720128025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10695884314026707813418683 16043826471040061720128025)
            ·
              refine ⟨12032869853280046290096019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16043826471040061720128025 12032869853280046290096019)
              ·
                refine ⟨18049304779920069435144029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12032869853280046290096019 18049304779920069435144029)
                ·
                  refine ⟨6768489292470026038179011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18049304779920069435144029 6768489292470026038179011)
                  ·
                    refine ⟨10152733938705039057268517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6768489292470026038179011 10152733938705039057268517)
                    ·
                      refine ⟨1903637613507194823237847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10152733938705039057268517 1903637613507194823237847)
                      ·
                        rfl

theorem cell23_3707321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3707321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707321 prefixEnd_3707321 := by exact prefixLift 3707321
  have htrace : WordTrace (prefixWord ++ tailWord_3707321) baseStart_3707321 baseEnd_3707321 := by
    simpa [prefixWord, tailWord_3707321, baseEnd_3707321] using wordTrace_append hprefix tailTrace_3707321
  have hstable : (prefixWord ++ tailWord_3707321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707321).length < 2 ^ (prefixWord ++ tailWord_3707321).sum := by decide
  have hdescent : baseEnd_3707321 < baseStart_3707321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707325 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 2, 3, 2]
def baseStart_3707325 : Nat := 118140960795 + 3707325 * 2 ^ 59
def prefixEnd_3707325 : Nat := 4983230072969 + 3 ^ 40 * 3707325 * 2
def baseEnd_3707325 : Nat := 1903639667429812807587829

theorem tailTrace_3707325 : CollatzResearch.WordTrace tailWord_3707325 prefixEnd_3707325 1903639667429812807587829 := by
  unfold tailWord_3707325
  simp only [CollatzResearch.WordTrace]
  refine ⟨135217251294002160546611429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90144834196001440364407619 135217251294002160546611429)
  ·
    refine ⟨25353234617625405102489643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135217251294002160546611429 25353234617625405102489643)
    ·
      refine ⟨38029851926438107653734465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25353234617625405102489643 38029851926438107653734465)
      ·
        refine ⟨28522388944828580740300849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38029851926438107653734465 28522388944828580740300849)
        ·
          refine ⟨21391791708621435555225637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28522388944828580740300849 21391791708621435555225637)
          ·
            refine ⟨4010960945366519166604807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21391791708621435555225637 4010960945366519166604807)
            ·
              refine ⟨6016441418049778749907211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010960945366519166604807 6016441418049778749907211)
              ·
                refine ⟨9024662127074668124860817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016441418049778749907211 9024662127074668124860817)
                ·
                  refine ⟨6768496595306001093645613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9024662127074668124860817 6768496595306001093645613)
                  ·
                    refine ⟨2538186223239750410117105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6768496595306001093645613 2538186223239750410117105)
                    ·
                      refine ⟨1903639667429812807587829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538186223239750410117105 1903639667429812807587829)
                      ·
                        rfl

theorem cell23_3707325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_3707325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707325 prefixEnd_3707325 := by exact prefixLift 3707325
  have htrace : WordTrace (prefixWord ++ tailWord_3707325) baseStart_3707325 baseEnd_3707325 := by
    simpa [prefixWord, tailWord_3707325, baseEnd_3707325] using wordTrace_append hprefix tailTrace_3707325
  have hstable : (prefixWord ++ tailWord_3707325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707325).length < 2 ^ (prefixWord ++ tailWord_3707325).sum := by decide
  have hdescent : baseEnd_3707325 < baseStart_3707325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707338 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2]
def baseStart_3707338 : Nat := 118140960795 + 3707338 * 2 ^ 59
def prefixEnd_3707338 : Nat := 4983230072969 + 3 ^ 40 * 3707338 * 2
def baseEnd_3707338 : Nat := 1903646342678321256725269

theorem tailTrace_3707338 : CollatzResearch.WordTrace tailWord_3707338 prefixEnd_3707338 1903646342678321256725269 := by
  unfold tailWord_3707338
  simp only [CollatzResearch.WordTrace]
  refine ⟨33804431360738765941708667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90145150295303375844556445 33804431360738765941708667)
  ·
    refine ⟨50706647041108148912563001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33804431360738765941708667 50706647041108148912563001)
    ·
      refine ⟨38029985280831111684422251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50706647041108148912563001 38029985280831111684422251)
      ·
        refine ⟨57044977921246667526633377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38029985280831111684422251 57044977921246667526633377)
        ·
          refine ⟨42783733440935000644975033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57044977921246667526633377 42783733440935000644975033)
          ·
            refine ⟨32087800080701250483731275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42783733440935000644975033 32087800080701250483731275)
            ·
              refine ⟨48131700121051875725596913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32087800080701250483731275 48131700121051875725596913)
              ·
                refine ⟨36098775090788906794197685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48131700121051875725596913 36098775090788906794197685)
                ·
                  refine ⟨3384260164761460011956033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36098775090788906794197685 3384260164761460011956033)
                  ·
                    refine ⟨2538195123571095008967025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3384260164761460011956033 2538195123571095008967025)
                    ·
                      refine ⟨1903646342678321256725269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538195123571095008967025 1903646342678321256725269)
                      ·
                        rfl

theorem cell23_3707338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_3707338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707338 prefixEnd_3707338 := by exact prefixLift 3707338
  have htrace : WordTrace (prefixWord ++ tailWord_3707338) baseStart_3707338 baseEnd_3707338 := by
    simpa [prefixWord, tailWord_3707338, baseEnd_3707338] using wordTrace_append hprefix tailTrace_3707338
  have hstable : (prefixWord ++ tailWord_3707338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707338).length < 2 ^ (prefixWord ++ tailWord_3707338).sum := by decide
  have hdescent : baseEnd_3707338 < baseStart_3707338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707348 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_3707348 : Nat := 118140960795 + 3707348 * 2 ^ 59
def prefixEnd_3707348 : Nat := 4983230072969 + 3 ^ 40 * 3707348 * 2
def baseEnd_3707348 : Nat := 634550492494955405866741

theorem tailTrace_3707348 : CollatzResearch.WordTrace tailWord_3707348 prefixEnd_3707348 634550492494955405866741 := by
  unfold tailWord_3707348
  simp only [CollatzResearch.WordTrace]
  refine ⟨67609045086459417737349349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90145393448612556983132465 67609045086459417737349349)
  ·
    refine ⟨12676695953711140825753003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67609045086459417737349349 12676695953711140825753003)
    ·
      refine ⟨19015043930566711238629505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12676695953711140825753003 19015043930566711238629505)
      ·
        refine ⟨14261282947925033428972129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19015043930566711238629505 14261282947925033428972129)
        ·
          refine ⟨10695962210943775071729097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14261282947925033428972129 10695962210943775071729097)
          ·
            refine ⟨8021971658207831303796823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10695962210943775071729097 8021971658207831303796823)
            ·
              refine ⟨12032957487311746955695235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8021971658207831303796823 12032957487311746955695235)
              ·
                refine ⟨18049436230967620433542853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12032957487311746955695235 18049436230967620433542853)
                ·
                  refine ⟨3384269293306428831289285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18049436230967620433542853 3384269293306428831289285)
                  ·
                    refine ⟨634550492494955405866741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3384269293306428831289285 634550492494955405866741)
                    ·
                      rfl

theorem cell23_3707348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_3707348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707348 prefixEnd_3707348 := by exact prefixLift 3707348
  have htrace : WordTrace (prefixWord ++ tailWord_3707348) baseStart_3707348 baseEnd_3707348 := by
    simpa [prefixWord, tailWord_3707348, baseEnd_3707348] using wordTrace_append hprefix tailTrace_3707348
  have hstable : (prefixWord ++ tailWord_3707348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707348).length < 2 ^ (prefixWord ++ tailWord_3707348).sum := by decide
  have hdescent : baseEnd_3707348 < baseStart_3707348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707365 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 1, 6]
def baseStart_3707365 : Nat := 118140960795 + 3707365 * 2 ^ 59
def prefixEnd_3707365 : Nat := 4983230072969 + 3 ^ 40 * 3707365 * 2
def baseEnd_3707365 : Nat := 634553402218664217029215

theorem tailTrace_3707365 : CollatzResearch.WordTrace tailWord_3707365 prefixEnd_3707365 634553402218664217029215 := by
  unfold tailWord_3707365
  simp only [CollatzResearch.WordTrace]
  refine ⟨135218710213857247378067549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90145806809238164918711699 135218710213857247378067549)
  ·
    refine ⟨50707016330196467766775331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135218710213857247378067549 50707016330196467766775331)
    ·
      refine ⟨76060524495294701650162997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50707016330196467766775331 76060524495294701650162997)
      ·
        refine ⟨7130674171433878279702781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76060524495294701650162997 7130674171433878279702781)
        ·
          refine ⟨2674002814287704354888543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7130674171433878279702781 2674002814287704354888543)
          ·
            refine ⟨4011004221431556532332815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674002814287704354888543 4011004221431556532332815)
            ·
              refine ⟨6016506332147334798499223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011004221431556532332815 6016506332147334798499223)
              ·
                refine ⟨9024759498221002197748835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016506332147334798499223 9024759498221002197748835)
                ·
                  refine ⟨13537139247331503296623253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9024759498221002197748835 13537139247331503296623253)
                  ·
                    refine ⟨634553402218664217029215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13537139247331503296623253 634553402218664217029215)
                    ·
                      rfl

theorem cell23_3707365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_3707365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707365 prefixEnd_3707365 := by exact prefixLift 3707365
  have htrace : WordTrace (prefixWord ++ tailWord_3707365) baseStart_3707365 baseEnd_3707365 := by
    simpa [prefixWord, tailWord_3707365, baseEnd_3707365] using wordTrace_append hprefix tailTrace_3707365
  have hstable : (prefixWord ++ tailWord_3707365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707365).length < 2 ^ (prefixWord ++ tailWord_3707365).sum := by decide
  have hdescent : baseEnd_3707365 < baseStart_3707365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707368 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3707368 : Nat := 118140960795 + 3707368 * 2 ^ 59
def prefixEnd_3707368 : Nat := 4983230072969 + 3 ^ 40 * 3707368 * 2
def baseEnd_3707368 : Nat := 1903661747097956139350131

theorem tailTrace_3707368 : CollatzResearch.WordTrace tailWord_3707368 prefixEnd_3707368 1903661747097956139350131 := by
  unfold tailWord_3707368
  simp only [CollatzResearch.WordTrace]
  refine ⟨67609409816423189445213379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90145879755230919260284505 67609409816423189445213379)
  ·
    refine ⟨101414114724634784167820069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67609409816423189445213379 101414114724634784167820069)
    ·
      refine ⟨19015146510869022031466263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101414114724634784167820069 19015146510869022031466263)
      ·
        refine ⟨28522719766303533047199395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19015146510869022031466263 28522719766303533047199395)
        ·
          refine ⟨42784079649455299570799093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28522719766303533047199395 42784079649455299570799093)
          ·
            refine ⟨4011007467136434334762415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42784079649455299570799093 4011007467136434334762415)
            ·
              refine ⟨6016511200704651502143623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011007467136434334762415 6016511200704651502143623)
              ·
                refine ⟨9024766801056977253215435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016511200704651502143623 9024766801056977253215435)
                ·
                  refine ⟨13537150201585465879823153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9024766801056977253215435 13537150201585465879823153)
                  ·
                    refine ⟨10152862651189099409867365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13537150201585465879823153 10152862651189099409867365)
                    ·
                      refine ⟨1903661747097956139350131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10152862651189099409867365 1903661747097956139350131)
                      ·
                        rfl

theorem cell23_3707368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3707368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707368 prefixEnd_3707368 := by exact prefixLift 3707368
  have htrace : WordTrace (prefixWord ++ tailWord_3707368) baseStart_3707368 baseEnd_3707368 := by
    simpa [prefixWord, tailWord_3707368, baseEnd_3707368] using wordTrace_append hprefix tailTrace_3707368
  have hstable : (prefixWord ++ tailWord_3707368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707368).length < 2 ^ (prefixWord ++ tailWord_3707368).sum := by decide
  have hdescent : baseEnd_3707368 < baseStart_3707368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707384 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_3707384 : Nat := 118140960795 + 3707384 * 2 ^ 59
def prefixEnd_3707384 : Nat := 4983230072969 + 3 ^ 40 * 3707384 * 2
def baseEnd_3707384 : Nat := 1903669962788428076750057

theorem tailTrace_3707384 : CollatzResearch.WordTrace tailWord_3707384 prefixEnd_3707384 1903669962788428076750057 := by
  unfold tailWord_3707384
  simp only [CollatzResearch.WordTrace]
  refine ⟨67609701600394206811504603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90146268800525609082006137 67609701600394206811504603)
  ·
    refine ⟨101414552400591310217256905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67609701600394206811504603 101414552400591310217256905)
    ·
      refine ⟨76060914300443482662942679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101414552400591310217256905 76060914300443482662942679)
      ·
        refine ⟨114091371450665223994414019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76060914300443482662942679 114091371450665223994414019)
        ·
          refine ⟨171137057175997835991621029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114091371450665223994414019 171137057175997835991621029)
          ·
            refine ⟨32088198220499594248428943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171137057175997835991621029 32088198220499594248428943)
            ·
              refine ⟨48132297330749391372643415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32088198220499594248428943 48132297330749391372643415)
              ·
                refine ⟨72198445996124087058965123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48132297330749391372643415 72198445996124087058965123)
                ·
                  refine ⟨108297668994186130588447685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72198445996124087058965123 108297668994186130588447685)
                  ·
                    refine ⟨20305812936409899485333941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108297668994186130588447685 20305812936409899485333941)
                    ·
                      refine ⟨1903669962788428076750057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20305812936409899485333941 1903669962788428076750057)
                      ·
                        rfl

theorem cell23_3707384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_3707384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707384 prefixEnd_3707384 := by exact prefixLift 3707384
  have htrace : WordTrace (prefixWord ++ tailWord_3707384) baseStart_3707384 baseEnd_3707384 := by
    simpa [prefixWord, tailWord_3707384, baseEnd_3707384] using wordTrace_append hprefix tailTrace_3707384
  have hstable : (prefixWord ++ tailWord_3707384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707384).length < 2 ^ (prefixWord ++ tailWord_3707384).sum := by decide
  have hdescent : baseEnd_3707384 < baseStart_3707384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707432 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3707432 : Nat := 118140960795 + 3707432 * 2 ^ 59
def prefixEnd_3707432 : Nat := 4983230072969 + 3 ^ 40 * 3707432 * 2
def baseEnd_3707432 : Nat := 1903694609859843888949837

theorem tailTrace_3707432 : CollatzResearch.WordTrace tailWord_3707432 prefixEnd_3707432 1903694609859843888949837 := by
  unfold tailWord_3707432
  simp only [CollatzResearch.WordTrace]
  refine ⟨67610576952307258910378275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90147435936409678547171033 67610576952307258910378275)
  ·
    refine ⟨101415865428460888365567413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67610576952307258910378275 101415865428460888365567413)
    ·
      refine ⟨9507737383918208284271945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101415865428460888365567413 9507737383918208284271945)
      ·
        refine ⟨7130803037938656213203959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9507737383918208284271945 7130803037938656213203959)
        ·
          refine ⟨10696204556907984319805939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7130803037938656213203959 10696204556907984319805939)
          ·
            refine ⟨16044306835361976479708909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10696204556907984319805939 16044306835361976479708909)
            ·
              refine ⟨6016615063260741179890841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16044306835361976479708909 6016615063260741179890841)
              ·
                refine ⟨4512461297445555884918131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6016615063260741179890841 4512461297445555884918131)
                ·
                  refine ⟨6768691946168333827377197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512461297445555884918131 6768691946168333827377197)
                  ·
                    refine ⟨2538259479813125185266449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6768691946168333827377197 2538259479813125185266449)
                    ·
                      refine ⟨1903694609859843888949837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538259479813125185266449 1903694609859843888949837)
                      ·
                        rfl

theorem cell23_3707432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3707432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707432 prefixEnd_3707432 := by exact prefixLift 3707432
  have htrace : WordTrace (prefixWord ++ tailWord_3707432) baseStart_3707432 baseEnd_3707432 := by
    simpa [prefixWord, tailWord_3707432, baseEnd_3707432] using wordTrace_append hprefix tailTrace_3707432
  have hstable : (prefixWord ++ tailWord_3707432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707432).length < 2 ^ (prefixWord ++ tailWord_3707432).sum := by decide
  have hdescent : baseEnd_3707432 < baseStart_3707432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707468 : List Nat := [2, 2, 1, 3, 1, 2, 3, 4, 5]
def baseStart_3707468 : Nat := 118140960795 + 3707468 * 2 ^ 59
def prefixEnd_3707468 : Nat := 4983230072969 + 3 ^ 40 * 3707468 * 2
def baseEnd_3707468 : Nat := 211523677240378416455519

theorem tailTrace_3707468 : CollatzResearch.WordTrace tailWord_3707468 prefixEnd_3707468 211523677240378416455519 := by
  unfold tailWord_3707468
  simp only [CollatzResearch.WordTrace]
  refine ⟨67611233466242047984533529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90148311288322730646044705 67611233466242047984533529)
  ·
    refine ⟨50708425099681535988400147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67611233466242047984533529 50708425099681535988400147)
    ·
      refine ⟨76062637649522303982600221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50708425099681535988400147 76062637649522303982600221)
      ·
        refine ⟨28523489118570863993475083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76062637649522303982600221 28523489118570863993475083)
        ·
          refine ⟨42785233677856295990212625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28523489118570863993475083 42785233677856295990212625)
          ·
            refine ⟨32088925258392221992659469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42785233677856295990212625 32088925258392221992659469)
            ·
              refine ⟨12033346971897083247247301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32088925258392221992659469 12033346971897083247247301)
              ·
                refine ⟨2256252557230703108858869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12033346971897083247247301 2256252557230703108858869)
                ·
                  refine ⟨211523677240378416455519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2256252557230703108858869 211523677240378416455519)
                  ·
                    rfl

theorem cell23_3707468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_3707468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707468 prefixEnd_3707468 := by exact prefixLift 3707468
  have htrace : WordTrace (prefixWord ++ tailWord_3707468) baseStart_3707468 baseEnd_3707468 := by
    simpa [prefixWord, tailWord_3707468, baseEnd_3707468] using wordTrace_append hprefix tailTrace_3707468
  have hstable : (prefixWord ++ tailWord_3707468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707468).length < 2 ^ (prefixWord ++ tailWord_3707468).sum := by decide
  have hdescent : baseEnd_3707468 < baseStart_3707468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707631 : List Nat := [1, 1, 2, 1, 5, 13]
def baseStart_3707631 : Nat := 118140960795 + 3707631 * 2 ^ 59
def prefixEnd_3707631 : Nat := 4983230072969 + 3 ^ 40 * 3707631 * 2
def baseEnd_3707631 : Nat := 7834554701687607450047

theorem tailTrace_3707631 : CollatzResearch.WordTrace tailWord_3707631 prefixEnd_3707631 7834554701687607450047 := by
  unfold tailWord_3707631
  simp only [CollatzResearch.WordTrace]
  refine ⟨135228412030893574807250747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90152274687262383204833831 135228412030893574807250747)
  ·
    refine ⟨202842618046340362210876121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135228412030893574807250747 202842618046340362210876121)
    ·
      refine ⟨152131963534755271658157091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202842618046340362210876121 152131963534755271658157091)
      ·
        refine ⟨228197945302132907487235637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152131963534755271658157091 228197945302132907487235637)
        ·
          refine ⟨21393557372074960076928341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228197945302132907487235637 21393557372074960076928341)
          ·
            refine ⟨7834554701687607450047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 21393557372074960076928341 7834554701687607450047)
            ·
              rfl

theorem cell23_3707631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 13].length) (baseStart_3707631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707631 prefixEnd_3707631 := by exact prefixLift 3707631
  have htrace : WordTrace (prefixWord ++ tailWord_3707631) baseStart_3707631 baseEnd_3707631 := by
    simpa [prefixWord, tailWord_3707631, baseEnd_3707631] using wordTrace_append hprefix tailTrace_3707631
  have hstable : (prefixWord ++ tailWord_3707631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707631).length < 2 ^ (prefixWord ++ tailWord_3707631).sum := by decide
  have hdescent : baseEnd_3707631 < baseStart_3707631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707655 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3707655 : Nat := 118140960795 + 3707655 * 2 ^ 59
def prefixEnd_3707655 : Nat := 4983230072969 + 3 ^ 40 * 3707655 * 2
def baseEnd_3707655 : Nat := 1903809116045796516461311

theorem tailTrace_3707655 : CollatzResearch.WordTrace tailWord_3707655 prefixEnd_3707655 1903809116045796516461311 := by
  unfold tailWord_3707655
  simp only [CollatzResearch.WordTrace]
  refine ⟨135229287382806626906124419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90152858255204417937416279 135229287382806626906124419)
  ·
    refine ⟨202843931074209940359186629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135229287382806626906124419 202843931074209940359186629)
    ·
      refine ⟨38033237076414363817347493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202843931074209940359186629 38033237076414363817347493)
      ·
        refine ⟨7131231951827693215752655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38033237076414363817347493 7131231951827693215752655)
        ·
          refine ⟨10696847927741539823628983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7131231951827693215752655 10696847927741539823628983)
          ·
            refine ⟨16045271891612309735443475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10696847927741539823628983 16045271891612309735443475)
            ·
              refine ⟨24067907837418464603165213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16045271891612309735443475 24067907837418464603165213)
              ·
                refine ⟨9025465439031924226186955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24067907837418464603165213 9025465439031924226186955)
                ·
                  refine ⟨13538198158547886339280433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9025465439031924226186955 13538198158547886339280433)
                  ·
                    refine ⟨10153648618910914754460325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13538198158547886339280433 10153648618910914754460325)
                    ·
                      refine ⟨1903809116045796516461311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10153648618910914754460325 1903809116045796516461311)
                      ·
                        rfl

theorem cell23_3707655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3707655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707655 prefixEnd_3707655 := by exact prefixLift 3707655
  have htrace : WordTrace (prefixWord ++ tailWord_3707655) baseStart_3707655 baseEnd_3707655 := by
    simpa [prefixWord, tailWord_3707655, baseEnd_3707655] using wordTrace_append hprefix tailTrace_3707655
  have hstable : (prefixWord ++ tailWord_3707655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707655).length < 2 ^ (prefixWord ++ tailWord_3707655).sum := by decide
  have hdescent : baseEnd_3707655 < baseStart_3707655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707676 : List Nat := [2, 2, 3, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_3707676 : Nat := 118140960795 + 3707676 * 2 ^ 59
def prefixEnd_3707676 : Nat := 4983230072969 + 3 ^ 40 * 3707676 * 2
def baseEnd_3707676 : Nat := 1903819899139540934298715

theorem tailTrace_3707676 : CollatzResearch.WordTrace tailWord_3707676 prefixEnd_3707676 1903819899139540934298715 := by
  unfold tailWord_3707676
  simp only [CollatzResearch.WordTrace]
  refine ⟨67615026657865273746319441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90153368877153698328425921 67615026657865273746319441)
  ·
    refine ⟨50711269993398955309739581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67615026657865273746319441 50711269993398955309739581)
    ·
      refine ⟨19016726247524608241152343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50711269993398955309739581 19016726247524608241152343)
      ·
        refine ⟨28525089371286912361728515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19016726247524608241152343 28525089371286912361728515)
        ·
          refine ⟨42787634056930368542592773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28525089371286912361728515 42787634056930368542592773)
          ·
            refine ⟨8022681385674444101736145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42787634056930368542592773 8022681385674444101736145)
            ·
              refine ⟨6017011039255833076302109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8022681385674444101736145 6017011039255833076302109)
              ·
                refine ⟨2256379139720937403613291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6017011039255833076302109 2256379139720937403613291)
                ·
                  refine ⟨3384568709581406105419937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256379139720937403613291 3384568709581406105419937)
                  ·
                    refine ⟨2538426532186054579064953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3384568709581406105419937 2538426532186054579064953)
                    ·
                      refine ⟨1903819899139540934298715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538426532186054579064953 1903819899139540934298715)
                      ·
                        rfl

theorem cell23_3707676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_3707676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707676 prefixEnd_3707676 := by exact prefixLift 3707676
  have htrace : WordTrace (prefixWord ++ tailWord_3707676) baseStart_3707676 baseEnd_3707676 := by
    simpa [prefixWord, tailWord_3707676, baseEnd_3707676] using wordTrace_append hprefix tailTrace_3707676
  have hstable : (prefixWord ++ tailWord_3707676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707676).length < 2 ^ (prefixWord ++ tailWord_3707676).sum := by decide
  have hdescent : baseEnd_3707676 < baseStart_3707676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707679 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 1, 2, 3]
def baseStart_3707679 : Nat := 118140960795 + 3707679 * 2 ^ 59
def prefixEnd_3707679 : Nat := 4983230072969 + 3 ^ 40 * 3707679 * 2
def baseEnd_3707679 : Nat := 1903821439581504422561201

theorem tailTrace_3707679 : CollatzResearch.WordTrace tailWord_3707679 prefixEnd_3707679 1903821439581504422561201 := by
  unfold tailWord_3707679
  simp only [CollatzResearch.WordTrace]
  refine ⟨135230162734719679004998091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90153441823146452669998727 135230162734719679004998091)
  ·
    refine ⟨202845244102079518507497137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135230162734719679004998091 202845244102079518507497137)
    ·
      refine ⟨152133933076559638880622853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202845244102079518507497137 152133933076559638880622853)
      ·
        refine ⟨28525112451854932290116785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152133933076559638880622853 28525112451854932290116785)
        ·
          refine ⟨21393834338891199217587589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28525112451854932290116785 21393834338891199217587589)
          ·
            refine ⟨4011343938542099853297673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21393834338891199217587589 4011343938542099853297673)
            ·
              refine ⟨3008507953906574889973255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011343938542099853297673 3008507953906574889973255)
              ·
                refine ⟨4512761930859862334959883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008507953906574889973255 4512761930859862334959883)
                ·
                  refine ⟨6769142896289793502439825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512761930859862334959883 6769142896289793502439825)
                  ·
                    refine ⟨5076857172217345126829869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6769142896289793502439825 5076857172217345126829869)
                    ·
                      refine ⟨1903821439581504422561201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5076857172217345126829869 1903821439581504422561201)
                      ·
                        rfl

theorem cell23_3707679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_3707679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707679 prefixEnd_3707679 := by exact prefixLift 3707679
  have htrace : WordTrace (prefixWord ++ tailWord_3707679) baseStart_3707679 baseEnd_3707679 := by
    simpa [prefixWord, tailWord_3707679, baseEnd_3707679] using wordTrace_append hprefix tailTrace_3707679
  have hstable : (prefixWord ++ tailWord_3707679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707679).length < 2 ^ (prefixWord ++ tailWord_3707679).sum := by decide
  have hdescent : baseEnd_3707679 < baseStart_3707679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707693 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3707693 : Nat := 118140960795 + 3707693 * 2 ^ 59
def prefixEnd_3707693 : Nat := 4983230072969 + 3 ^ 40 * 3707693 * 2
def baseEnd_3707693 : Nat := 1903828628310667367786137

theorem tailTrace_3707693 : CollatzResearch.WordTrace tailWord_3707693 prefixEnd_3707693 1903828628310667367786137 := by
  unfold tailWord_3707693
  simp only [CollatzResearch.WordTrace]
  refine ⟨135230673356668959396007733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90153782237779306264005155 135230673356668959396007733)
  ·
    refine ⟨12677875627187714943375725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135230673356668959396007733 12677875627187714943375725)
    ·
      refine ⟨4754203360195393103765897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12677875627187714943375725 4754203360195393103765897)
      ·
        refine ⟨3565652520146544827824423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4754203360195393103765897 3565652520146544827824423)
        ·
          refine ⟨5348478780219817241736635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565652520146544827824423 5348478780219817241736635)
          ·
            refine ⟨8022718170329725862604953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5348478780219817241736635 8022718170329725862604953)
            ·
              refine ⟨6017038627747294396953715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8022718170329725862604953 6017038627747294396953715)
              ·
                refine ⟨9025557941620941595430573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017038627747294396953715 9025557941620941595430573)
                ·
                  refine ⟨3384584228107853098286465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9025557941620941595430573 3384584228107853098286465)
                  ·
                    refine ⟨2538438171080889823714849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3384584228107853098286465 2538438171080889823714849)
                    ·
                      refine ⟨1903828628310667367786137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538438171080889823714849 1903828628310667367786137)
                      ·
                        rfl

theorem cell23_3707693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3707693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707693 prefixEnd_3707693 := by exact prefixLift 3707693
  have htrace : WordTrace (prefixWord ++ tailWord_3707693) baseStart_3707693 baseEnd_3707693 := by
    simpa [prefixWord, tailWord_3707693, baseEnd_3707693] using wordTrace_append hprefix tailTrace_3707693
  have hstable : (prefixWord ++ tailWord_3707693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707693).length < 2 ^ (prefixWord ++ tailWord_3707693).sum := by decide
  have hdescent : baseEnd_3707693 < baseStart_3707693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707709 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3707709 : Nat := 118140960795 + 3707709 * 2 ^ 59
def prefixEnd_3707709 : Nat := 4983230072969 + 3 ^ 40 * 3707709 * 2
def baseEnd_3707709 : Nat := 1903836844001139305186063

theorem tailTrace_3707709 : CollatzResearch.WordTrace tailWord_3707709 prefixEnd_3707709 1903836844001139305186063 := by
  unfold tailWord_3707709
  simp only [CollatzResearch.WordTrace]
  refine ⟨135231256924610994128590181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90154171283073996085726787 135231256924610994128590181)
  ·
    refine ⟨25355860673364561399110659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135231256924610994128590181 25355860673364561399110659)
    ·
      refine ⟨38033791010046842098665989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25355860673364561399110659 38033791010046842098665989)
      ·
        refine ⟨7131335814383782893499873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38033791010046842098665989 7131335814383782893499873)
        ·
          refine ⟨5348501860787837170124905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7131335814383782893499873 5348501860787837170124905)
          ·
            refine ⟨4011376395590877877593679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5348501860787837170124905 4011376395590877877593679)
            ·
              refine ⟨6017064593386316816390519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011376395590877877593679 6017064593386316816390519)
              ·
                refine ⟨9025596890079475224585779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017064593386316816390519 9025596890079475224585779)
                ·
                  refine ⟨13538395335119212836878669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9025596890079475224585779 13538395335119212836878669)
                  ·
                    refine ⟨5076898250669704813829501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13538395335119212836878669 5076898250669704813829501)
                    ·
                      refine ⟨1903836844001139305186063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5076898250669704813829501 1903836844001139305186063)
                      ·
                        rfl

theorem cell23_3707709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3707709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707709 prefixEnd_3707709 := by exact prefixLift 3707709
  have htrace : WordTrace (prefixWord ++ tailWord_3707709) baseStart_3707709 baseEnd_3707709 := by
    simpa [prefixWord, tailWord_3707709, baseEnd_3707709] using wordTrace_append hprefix tailTrace_3707709
  have hstable : (prefixWord ++ tailWord_3707709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707709).length < 2 ^ (prefixWord ++ tailWord_3707709).sum := by decide
  have hdescent : baseEnd_3707709 < baseStart_3707709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707716 : List Nat := [2, 3, 4, 2, 2, 1, 2, 7]
def baseStart_3707716 : Nat := 118140960795 + 3707716 * 2 ^ 59
def prefixEnd_3707716 : Nat := 4983230072969 + 3 ^ 40 * 3707716 * 2
def baseEnd_3707716 : Nat := 70512608828360028807353

theorem tailTrace_3707716 : CollatzResearch.WordTrace tailWord_3707716 prefixEnd_3707716 70512608828360028807353 := by
  unfold tailWord_3707716
  simp only [CollatzResearch.WordTrace]
  refine ⟨67615756117792817162047501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90154341490390422882730001 67615756117792817162047501)
  ·
    refine ⟨25355908544172306435767813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67615756117792817162047501 25355908544172306435767813)
    ·
      refine ⟨4754232852032307456706465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25355908544172306435767813 4754232852032307456706465)
      ·
        refine ⟨3565674639024230592529849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4754232852032307456706465 3565674639024230592529849)
        ·
          refine ⟨2674255979268172944397387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3565674639024230592529849 2674255979268172944397387)
          ·
            refine ⟨4011383968902259416596081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674255979268172944397387 4011383968902259416596081)
            ·
              refine ⟨3008537976676694562447061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011383968902259416596081 3008537976676694562447061)
              ·
                refine ⟨70512608828360028807353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3008537976676694562447061 70512608828360028807353)
                ·
                  rfl

theorem cell23_3707716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 7].length) (baseStart_3707716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707716 prefixEnd_3707716 := by exact prefixLift 3707716
  have htrace : WordTrace (prefixWord ++ tailWord_3707716) baseStart_3707716 baseEnd_3707716 := by
    simpa [prefixWord, tailWord_3707716, baseEnd_3707716] using wordTrace_append hprefix tailTrace_3707716
  have hstable : (prefixWord ++ tailWord_3707716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707716).length < 2 ^ (prefixWord ++ tailWord_3707716).sum := by decide
  have hdescent : baseEnd_3707716 < baseStart_3707716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707728 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_3707728 : Nat := 118140960795 + 3707728 * 2 ^ 59
def prefixEnd_3707728 : Nat := 4983230072969 + 3 ^ 40 * 3707728 * 2
def baseEnd_3707728 : Nat := 1903846600133574730848475

theorem tailTrace_3707728 : CollatzResearch.WordTrace tailWord_3707728 prefixEnd_3707728 1903846600133574730848475 := by
  unfold tailWord_3707728
  simp only [CollatzResearch.WordTrace]
  refine ⟨67615974955771080186765919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90154633274361440249021225 67615974955771080186765919)
  ·
    refine ⟨101423962433656620280148879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67615974955771080186765919 101423962433656620280148879)
    ·
      refine ⟨152135943650484930420223319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101423962433656620280148879 152135943650484930420223319)
      ·
        refine ⟨228203915475727395630334979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152135943650484930420223319 228203915475727395630334979)
        ·
          refine ⟨342305873213591093445502469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228203915475727395630334979 342305873213591093445502469)
          ·
            refine ⟨64182351227548330021031713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342305873213591093445502469 64182351227548330021031713)
            ·
              refine ⟨48136763420661247515773785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64182351227548330021031713 48136763420661247515773785)
              ·
                refine ⟨36102572565495935636830339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48136763420661247515773785 36102572565495935636830339)
                ·
                  refine ⟨54153858848243903455245509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36102572565495935636830339 54153858848243903455245509)
                  ·
                    refine ⟨10153848534045731897858533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54153858848243903455245509 10153848534045731897858533)
                    ·
                      refine ⟨1903846600133574730848475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10153848534045731897858533 1903846600133574730848475)
                      ·
                        rfl

theorem cell23_3707728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_3707728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707728 prefixEnd_3707728 := by exact prefixLift 3707728
  have htrace : WordTrace (prefixWord ++ tailWord_3707728) baseStart_3707728 baseEnd_3707728 := by
    simpa [prefixWord, tailWord_3707728, baseEnd_3707728] using wordTrace_append hprefix tailTrace_3707728
  have hstable : (prefixWord ++ tailWord_3707728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707728).length < 2 ^ (prefixWord ++ tailWord_3707728).sum := by decide
  have hdescent : baseEnd_3707728 < baseStart_3707728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707735 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_3707735 : Nat := 118140960795 + 3707735 * 2 ^ 59
def prefixEnd_3707735 : Nat := 4983230072969 + 3 ^ 40 * 3707735 * 2
def baseEnd_3707735 : Nat := 1903850194498156203460943

theorem tailTrace_3707735 : CollatzResearch.WordTrace tailWord_3707735 prefixEnd_3707735 1903850194498156203460943 := by
  unfold tailWord_3707735
  simp only [CollatzResearch.WordTrace]
  refine ⟨135232205222516800569036659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90154803481677867046024439 135232205222516800569036659)
  ·
    refine ⟨202848307833775200853554989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135232205222516800569036659 202848307833775200853554989)
    ·
      refine ⟨76068115437665700320083121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202848307833775200853554989 76068115437665700320083121)
      ·
        refine ⟨57051086578249275240062341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76068115437665700320083121 57051086578249275240062341)
        ·
          refine ⟨10697078733421739107511689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57051086578249275240062341 10697078733421739107511689)
          ·
            refine ⟨8022809050066304330633767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10697078733421739107511689 8022809050066304330633767)
            ·
              refine ⟨12034213575099456495950651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8022809050066304330633767 12034213575099456495950651)
              ·
                refine ⟨18051320362649184743925977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12034213575099456495950651 18051320362649184743925977)
                ·
                  refine ⟨13538490271986888557944483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18051320362649184743925977 13538490271986888557944483)
                  ·
                    refine ⟨20307735407980332836916725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13538490271986888557944483 20307735407980332836916725)
                    ·
                      refine ⟨1903850194498156203460943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20307735407980332836916725 1903850194498156203460943)
                      ·
                        rfl

theorem cell23_3707735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_3707735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707735 prefixEnd_3707735 := by exact prefixLift 3707735
  have htrace : WordTrace (prefixWord ++ tailWord_3707735) baseStart_3707735 baseEnd_3707735 := by
    simpa [prefixWord, tailWord_3707735, baseEnd_3707735] using wordTrace_append hprefix tailTrace_3707735
  have hstable : (prefixWord ++ tailWord_3707735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707735).length < 2 ^ (prefixWord ++ tailWord_3707735).sum := by decide
  have hdescent : baseEnd_3707735 < baseStart_3707735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707755 : List Nat := [1, 1, 1, 1, 2, 2, 4, 6, 5]
def baseStart_3707755 : Nat := 118140960795 + 3707755 * 2 ^ 59
def prefixEnd_3707755 : Nat := 4983230072969 + 3 ^ 40 * 3707755 * 2
def baseEnd_3707755 : Nat := 211540051567916236134539

theorem tailTrace_3707755 : CollatzResearch.WordTrace tailWord_3707755 prefixEnd_3707755 211540051567916236134539 := by
  unfold tailWord_3707755
  simp only [CollatzResearch.WordTrace]
  refine ⟨135232934682444343984764719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90155289788296229323176479 135232934682444343984764719)
  ·
    refine ⟨202849402023666515977147079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135232934682444343984764719 202849402023666515977147079)
    ·
      refine ⟨304274103035499773965720619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202849402023666515977147079 304274103035499773965720619)
      ·
        refine ⟨456411154553249660948580929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304274103035499773965720619 456411154553249660948580929)
        ·
          refine ⟨342308365914937245711435697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456411154553249660948580929 342308365914937245711435697)
          ·
            refine ⟨256731274436202934283576773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342308365914937245711435697 256731274436202934283576773)
            ·
              refine ⟨48137113956788050178170645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256731274436202934283576773 48137113956788050178170645)
              ·
                refine ⟨2256427216724439852101749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48137113956788050178170645 2256427216724439852101749)
                ·
                  refine ⟨211540051567916236134539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2256427216724439852101749 211540051567916236134539)
                  ·
                    rfl

theorem cell23_3707755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 5].length) (baseStart_3707755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707755 prefixEnd_3707755 := by exact prefixLift 3707755
  have htrace : WordTrace (prefixWord ++ tailWord_3707755) baseStart_3707755 baseEnd_3707755 := by
    simpa [prefixWord, tailWord_3707755, baseEnd_3707755] using wordTrace_append hprefix tailTrace_3707755
  have hstable : (prefixWord ++ tailWord_3707755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707755).length < 2 ^ (prefixWord ++ tailWord_3707755).sum := by decide
  have hdescent : baseEnd_3707755 < baseStart_3707755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707768 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 1, 7]
def baseStart_3707768 : Nat := 118140960795 + 3707768 * 2 ^ 59
def prefixEnd_3707768 : Nat := 4983230072969 + 3 ^ 40 * 3707768 * 2
def baseEnd_3707768 : Nat := 634622379786584858116097

theorem tailTrace_3707768 : CollatzResearch.WordTrace tailWord_3707768 prefixEnd_3707768 634622379786584858116097 := by
  unfold tailWord_3707768
  simp only [CollatzResearch.WordTrace]
  refine ⟨67616704415698623602493979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90155605887598164803325305 67616704415698623602493979)
  ·
    refine ⟨101425056623547935403740969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67616704415698623602493979 101425056623547935403740969)
    ·
      refine ⟨76068792467660951552805727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101425056623547935403740969 76068792467660951552805727)
      ·
        refine ⟨114103188701491427329208591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76068792467660951552805727 114103188701491427329208591)
        ·
          refine ⟨171154783052237140993812887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114103188701491427329208591 171154783052237140993812887)
          ·
            refine ⟨256732174578355711490719331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171154783052237140993812887 256732174578355711490719331)
            ·
              refine ⟨385098261867533567236078997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256732174578355711490719331 385098261867533567236078997)
              ·
                refine ⟨18051481025040635964191203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385098261867533567236078997 18051481025040635964191203)
                ·
                  refine ⟨27077221537560953946286805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18051481025040635964191203 27077221537560953946286805)
                  ·
                    refine ⟨634622379786584858116097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27077221537560953946286805 634622379786584858116097)
                    ·
                      rfl

theorem cell23_3707768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_3707768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707768 prefixEnd_3707768 := by exact prefixLift 3707768
  have htrace : WordTrace (prefixWord ++ tailWord_3707768) baseStart_3707768 baseEnd_3707768 := by
    simpa [prefixWord, tailWord_3707768, baseEnd_3707768] using wordTrace_append hprefix tailTrace_3707768
  have hstable : (prefixWord ++ tailWord_3707768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707768).length < 2 ^ (prefixWord ++ tailWord_3707768).sum := by decide
  have hdescent : baseEnd_3707768 < baseStart_3707768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707785 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 2, 5]
def baseStart_3707785 : Nat := 118140960795 + 3707785 * 2 ^ 59
def prefixEnd_3707785 : Nat := 4983230072969 + 3 ^ 40 * 3707785 * 2
def baseEnd_3707785 : Nat := 634625289510293669278571

theorem tailTrace_3707785 : CollatzResearch.WordTrace tailWord_3707785 prefixEnd_3707785 634625289510293669278571 := by
  unfold tailWord_3707785
  simp only [CollatzResearch.WordTrace]
  refine ⟨135234028872335659108356809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90156019248223772738904539 135234028872335659108356809)
  ·
    refine ⟨101425521654251744331267607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135234028872335659108356809 101425521654251744331267607)
    ·
      refine ⟨152138282481377616496901411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101425521654251744331267607 152138282481377616496901411)
      ·
        refine ⟨228207423722066424745352117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152138282481377616496901411 228207423722066424745352117)
        ·
          refine ⟨21394445973943727319876761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228207423722066424745352117 21394445973943727319876761)
          ·
            refine ⟨16045834480457795489907571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21394445973943727319876761 16045834480457795489907571)
            ·
              refine ⟨24068751720686693234861357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16045834480457795489907571 24068751720686693234861357)
              ·
                refine ⟨9025781895257509963073009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24068751720686693234861357 9025781895257509963073009)
                ·
                  refine ⟨6769336421443132472304757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9025781895257509963073009 6769336421443132472304757)
                  ·
                    refine ⟨634625289510293669278571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6769336421443132472304757 634625289510293669278571)
                    ·
                      rfl

theorem cell23_3707785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_3707785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707785 prefixEnd_3707785 := by exact prefixLift 3707785
  have htrace : WordTrace (prefixWord ++ tailWord_3707785) baseStart_3707785 baseEnd_3707785 := by
    simpa [prefixWord, tailWord_3707785, baseEnd_3707785] using wordTrace_append hprefix tailTrace_3707785
  have hstable : (prefixWord ++ tailWord_3707785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707785).length < 2 ^ (prefixWord ++ tailWord_3707785).sum := by decide
  have hdescent : baseEnd_3707785 < baseStart_3707785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707832 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 3, 4]
def baseStart_3707832 : Nat := 118140960795 + 3707832 * 2 ^ 59
def prefixEnd_3707832 : Nat := 4983230072969 + 3 ^ 40 * 3707832 * 2
def baseEnd_3707832 : Nat := 634633334040547441315999

theorem tailTrace_3707832 : CollatzResearch.WordTrace tailWord_3707832 prefixEnd_3707832 634633334040547441315999 := by
  unfold tailWord_3707832
  simp only [CollatzResearch.WordTrace]
  refine ⟨67617871551582693067658875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90157162068776924090211833 67617871551582693067658875)
  ·
    refine ⟨101426807327374039601488313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67617871551582693067658875 101426807327374039601488313)
    ·
      refine ⟨76070105495530529701116235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101426807327374039601488313 76070105495530529701116235)
      ·
        refine ⟨114105158243295794551674353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76070105495530529701116235 114105158243295794551674353)
        ·
          refine ⟨85578868682471845913755765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114105158243295794551674353 85578868682471845913755765)
          ·
            refine ⟨8023018938981735554414603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85578868682471845913755765 8023018938981735554414603)
            ·
              refine ⟨12034528408472603331621905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8023018938981735554414603 12034528408472603331621905)
              ·
                refine ⟨9025896306354452498716429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12034528408472603331621905 9025896306354452498716429)
                ·
                  refine ⟨3384711114882919687018661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9025896306354452498716429 3384711114882919687018661)
                  ·
                    refine ⟨634633334040547441315999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3384711114882919687018661 634633334040547441315999)
                    ·
                      rfl

theorem cell23_3707832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_3707832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707832 prefixEnd_3707832 := by exact prefixLift 3707832
  have htrace : WordTrace (prefixWord ++ tailWord_3707832) baseStart_3707832 baseEnd_3707832 := by
    simpa [prefixWord, tailWord_3707832, baseEnd_3707832] using wordTrace_append hprefix tailTrace_3707832
  have hstable : (prefixWord ++ tailWord_3707832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707832).length < 2 ^ (prefixWord ++ tailWord_3707832).sum := by decide
  have hdescent : baseEnd_3707832 < baseStart_3707832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707865 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_3707865 : Nat := 118140960795 + 3707865 * 2 ^ 59
def prefixEnd_3707865 : Nat := 4983230072969 + 3 ^ 40 * 3707865 * 2
def baseEnd_3707865 : Nat := 1903916946983240694835345

theorem tailTrace_3707865 : CollatzResearch.WordTrace tailWord_3707865 prefixEnd_3707865 1903916946983240694835345 := by
  unfold tailWord_3707865
  simp only [CollatzResearch.WordTrace]
  refine ⟨135236946712045832771269049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90157964474697221847512699 135236946712045832771269049)
  ·
    refine ⟨101427710034034374578451787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135236946712045832771269049 101427710034034374578451787)
    ·
      refine ⟨152141565051051561867677681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101427710034034374578451787 152141565051051561867677681)
      ·
        refine ⟨114106173788288671400758261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152141565051051561867677681 114106173788288671400758261)
        ·
          refine ⟨10697453792652062943821087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114106173788288671400758261 10697453792652062943821087)
          ·
            refine ⟨16046180688978094415731631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10697453792652062943821087 16046180688978094415731631)
            ·
              refine ⟨24069271033467141623597447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16046180688978094415731631 24069271033467141623597447)
              ·
                refine ⟨36103906550200712435396171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24069271033467141623597447 36103906550200712435396171)
                ·
                  refine ⟨54155859825301068653094257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36103906550200712435396171 54155859825301068653094257)
                  ·
                    refine ⟨40616894868975801489820693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54155859825301068653094257 40616894868975801489820693)
                    ·
                      refine ⟨1903916946983240694835345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40616894868975801489820693 1903916946983240694835345)
                      ·
                        rfl

theorem cell23_3707865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_3707865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707865 prefixEnd_3707865 := by exact prefixLift 3707865
  have htrace : WordTrace (prefixWord ++ tailWord_3707865) baseStart_3707865 baseEnd_3707865 := by
    simpa [prefixWord, tailWord_3707865, baseEnd_3707865] using wordTrace_append hprefix tailTrace_3707865
  have hstable : (prefixWord ++ tailWord_3707865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707865).length < 2 ^ (prefixWord ++ tailWord_3707865).sum := by decide
  have hdescent : baseEnd_3707865 < baseStart_3707865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707879 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 6]
def baseStart_3707879 : Nat := 118140960795 + 3707879 * 2 ^ 59
def prefixEnd_3707879 : Nat := 4983230072969 + 3 ^ 40 * 3707879 * 2
def baseEnd_3707879 : Nat := 211547126190267071117809

theorem tailTrace_3707879 : CollatzResearch.WordTrace tailWord_3707879 prefixEnd_3707879 211547126190267071117809 := by
  unfold tailWord_3707879
  simp only [CollatzResearch.WordTrace]
  refine ⟨135237457333995113162278691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90158304889330075441519127 135237457333995113162278691)
  ·
    refine ⟨202856186000992669743418037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135237457333995113162278691 202856186000992669743418037)
    ·
      refine ⟨19017767437593062788445441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202856186000992669743418037 19017767437593062788445441)
      ·
        refine ⟨14263325578194797091334081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19017767437593062788445441 14263325578194797091334081)
        ·
          refine ⟨10697494183646097818500561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14263325578194797091334081 10697494183646097818500561)
          ·
            refine ⟨8023120637734573363875421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10697494183646097818500561 8023120637734573363875421)
            ·
              refine ⟨3008670239150465011453283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8023120637734573363875421 3008670239150465011453283)
              ·
                refine ⟨4513005358725697517179925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008670239150465011453283 4513005358725697517179925)
                ·
                  refine ⟨211547126190267071117809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4513005358725697517179925 211547126190267071117809)
                  ·
                    rfl

theorem cell23_3707879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 6].length) (baseStart_3707879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707879 prefixEnd_3707879 := by exact prefixLift 3707879
  have htrace : WordTrace (prefixWord ++ tailWord_3707879) baseStart_3707879 baseEnd_3707879 := by
    simpa [prefixWord, tailWord_3707879, baseEnd_3707879] using wordTrace_append hprefix tailTrace_3707879
  have hstable : (prefixWord ++ tailWord_3707879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707879).length < 2 ^ (prefixWord ++ tailWord_3707879).sum := by decide
  have hdescent : baseEnd_3707879 < baseStart_3707879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707889 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 3]
def baseStart_3707889 : Nat := 118140960795 + 3707889 * 2 ^ 59
def prefixEnd_3707889 : Nat := 4983230072969 + 3 ^ 40 * 3707889 * 2
def baseEnd_3707889 : Nat := 1903929270518948600935235

theorem tailTrace_3707889 : CollatzResearch.WordTrace tailWord_3707889 prefixEnd_3707889 1903929270518948600935235 := by
  unfold tailWord_3707889
  simp only [CollatzResearch.WordTrace]
  refine ⟨135237822063958884870142721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90158548042639256580095147 135237822063958884870142721)
  ·
    refine ⟨101428366547969163652607041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135237822063958884870142721 101428366547969163652607041)
    ·
      refine ⟨76071274910976872739455281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101428366547969163652607041 76071274910976872739455281)
      ·
        refine ⟨57053456183232654554591461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76071274910976872739455281 57053456183232654554591461)
        ·
          refine ⟨10697523034356122728985899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57053456183232654554591461 10697523034356122728985899)
          ·
            refine ⟨16046284551534184093478849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10697523034356122728985899 16046284551534184093478849)
            ·
              refine ⟨12034713413650638070109137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16046284551534184093478849 12034713413650638070109137)
              ·
                refine ⟨9026035060237978552581853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12034713413650638070109137 9026035060237978552581853)
                ·
                  refine ⟨3384763147589241957218195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9026035060237978552581853 3384763147589241957218195)
                  ·
                    refine ⟨5077144721383862935827293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3384763147589241957218195 5077144721383862935827293)
                    ·
                      refine ⟨1903929270518948600935235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5077144721383862935827293 1903929270518948600935235)
                      ·
                        rfl

theorem cell23_3707889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_3707889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707889 prefixEnd_3707889 := by exact prefixLift 3707889
  have htrace : WordTrace (prefixWord ++ tailWord_3707889) baseStart_3707889 baseEnd_3707889 := by
    simpa [prefixWord, tailWord_3707889, baseEnd_3707889] using wordTrace_append hprefix tailTrace_3707889
  have hstable : (prefixWord ++ tailWord_3707889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707889).length < 2 ^ (prefixWord ++ tailWord_3707889).sum := by decide
  have hdescent : baseEnd_3707889 < baseStart_3707889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707935 : List Nat := [1, 1, 2, 4, 1, 3, 1, 10]
def baseStart_3707935 : Nat := 118140960795 + 3707935 * 2 ^ 59
def prefixEnd_3707935 : Nat := 4983230072969 + 3 ^ 40 * 3707935 * 2
def baseEnd_3707935 : Nat := 70516773727002052628149

theorem tailTrace_3707935 : CollatzResearch.WordTrace tailWord_3707935 prefixEnd_3707935 70516773727002052628149 := by
  unfold tailWord_3707935
  simp only [CollatzResearch.WordTrace]
  refine ⟨135239499821792234726317259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90159666547861489817544839 135239499821792234726317259)
  ·
    refine ⟨202859249732688352089475889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135239499821792234726317259 202859249732688352089475889)
    ·
      refine ⟨152144437299516264067106917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202859249732688352089475889 152144437299516264067106917)
      ·
        refine ⟨28527081993659299512582547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152144437299516264067106917 28527081993659299512582547)
        ·
          refine ⟨42790622990488949268873821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28527081993659299512582547 42790622990488949268873821)
          ·
            refine ⟨16046483621433355975827683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42790622990488949268873821 16046483621433355975827683)
            ·
              refine ⟨24069725432150033963741525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16046483621433355975827683 24069725432150033963741525)
              ·
                refine ⟨70516773727002052628149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24069725432150033963741525 70516773727002052628149)
                ·
                  rfl

theorem cell23_3707935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 10].length) (baseStart_3707935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707935 prefixEnd_3707935 := by exact prefixLift 3707935
  have htrace : WordTrace (prefixWord ++ tailWord_3707935) baseStart_3707935 baseEnd_3707935 := by
    simpa [prefixWord, tailWord_3707935, baseEnd_3707935] using wordTrace_append hprefix tailTrace_3707935
  have hstable : (prefixWord ++ tailWord_3707935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707935).length < 2 ^ (prefixWord ++ tailWord_3707935).sum := by decide
  have hdescent : baseEnd_3707935 < baseStart_3707935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707939 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 2, 4]
def baseStart_3707939 : Nat := 118140960795 + 3707939 * 2 ^ 59
def prefixEnd_3707939 : Nat := 4983230072969 + 3 ^ 40 * 3707939 * 2
def baseEnd_3707939 : Nat := 634651648183891135103335

theorem tailTrace_3707939 : CollatzResearch.WordTrace tailWord_3707939 prefixEnd_3707939 634651648183891135103335 := by
  unfold tailWord_3707939
  simp only [CollatzResearch.WordTrace]
  refine ⟨135239645713777743409462871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90159763809185162272975247 135239645713777743409462871)
  ·
    refine ⟨202859468570666615114194307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135239645713777743409462871 202859468570666615114194307)
    ·
      refine ⟨304289202855999922671291461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202859468570666615114194307 304289202855999922671291461)
      ·
        refine ⟨57054225535499985500867149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304289202855999922671291461 57054225535499985500867149)
        ·
          refine ⟨21395334575812494562825181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57054225535499985500867149 21395334575812494562825181)
          ·
            refine ⟨8023250465929685461059443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21395334575812494562825181 8023250465929685461059443)
            ·
              refine ⟨12034875698894528191589165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8023250465929685461059443 12034875698894528191589165)
              ·
                refine ⟨4513078387085448071845937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12034875698894528191589165 4513078387085448071845937)
                ·
                  refine ⟨3384808790314086053884453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4513078387085448071845937 3384808790314086053884453)
                  ·
                    refine ⟨634651648183891135103335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3384808790314086053884453 634651648183891135103335)
                    ·
                      rfl

theorem cell23_3707939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 4].length) (baseStart_3707939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707939 prefixEnd_3707939 := by exact prefixLift 3707939
  have htrace : WordTrace (prefixWord ++ tailWord_3707939) baseStart_3707939 baseEnd_3707939 := by
    simpa [prefixWord, tailWord_3707939, baseEnd_3707939] using wordTrace_append hprefix tailTrace_3707939
  have hstable : (prefixWord ++ tailWord_3707939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707939).length < 2 ^ (prefixWord ++ tailWord_3707939).sum := by decide
  have hdescent : baseEnd_3707939 < baseStart_3707939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707962 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3]
def baseStart_3707962 : Nat := 118140960795 + 3707962 * 2 ^ 59
def prefixEnd_3707962 : Nat := 4983230072969 + 3 ^ 40 * 3707962 * 2
def baseEnd_3707962 : Nat := 1903966754606726815322399

theorem tailTrace_3707962 : CollatzResearch.WordTrace tailWord_3707962 prefixEnd_3707962 1903966754606726815322399 := by
  unfold tailWord_3707962
  simp only [CollatzResearch.WordTrace]
  refine ⟨33810121148173604584387535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90160323061796278891700093 33810121148173604584387535)
  ·
    refine ⟨50715181722260406876581303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33810121148173604584387535 50715181722260406876581303)
    ·
      refine ⟨76072772583390610314871955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50715181722260406876581303 76072772583390610314871955)
      ·
        refine ⟨114109158875085915472307933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76072772583390610314871955 114109158875085915472307933)
        ·
          refine ⟨42790934578157218302115475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114109158875085915472307933 42790934578157218302115475)
          ·
            refine ⟨64186401867235827453173213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42790934578157218302115475 64186401867235827453173213)
            ·
              refine ⟨24069900700213435294939955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64186401867235827453173213 24069900700213435294939955)
              ·
                refine ⟨36104851050320152942409933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24069900700213435294939955 36104851050320152942409933)
                ·
                  refine ⟨13539319143870057353403725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36104851050320152942409933 13539319143870057353403725)
                  ·
                    refine ⟨5077244678951271507526397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13539319143870057353403725 5077244678951271507526397)
                    ·
                      refine ⟨1903966754606726815322399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5077244678951271507526397 1903966754606726815322399)
                      ·
                        rfl

theorem cell23_3707962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_3707962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707962 prefixEnd_3707962 := by exact prefixLift 3707962
  have htrace : WordTrace (prefixWord ++ tailWord_3707962) baseStart_3707962 baseEnd_3707962 := by
    simpa [prefixWord, tailWord_3707962, baseEnd_3707962] using wordTrace_append hprefix tailTrace_3707962
  have hstable : (prefixWord ++ tailWord_3707962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707962).length < 2 ^ (prefixWord ++ tailWord_3707962).sum := by decide
  have hdescent : baseEnd_3707962 < baseStart_3707962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707966 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3707966 : Nat := 118140960795 + 3707966 * 2 ^ 59
def prefixEnd_3707966 : Nat := 4983230072969 + 3 ^ 40 * 3707966 * 2
def baseEnd_3707966 : Nat := 1903968808529344799672381

theorem tailTrace_3707966 : CollatzResearch.WordTrace tailWord_3707966 prefixEnd_3707966 1903968808529344799672381 := by
  unfold tailWord_3707966
  simp only [CollatzResearch.WordTrace]
  refine ⟨16905078810584990877586969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90160420323119951347130501 16905078810584990877586969)
  ·
    refine ⟨12678809107938743158190227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16905078810584990877586969 12678809107938743158190227)
    ·
      refine ⟨19018213661908114737285341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12678809107938743158190227 19018213661908114737285341)
      ·
        refine ⟨7131830123215543026482003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19018213661908114737285341 7131830123215543026482003)
        ·
          refine ⟨10697745184823314539723005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7131830123215543026482003 10697745184823314539723005)
          ·
            refine ⟨4011654444308742952396127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10697745184823314539723005 4011654444308742952396127)
            ·
              refine ⟨6017481666463114428594191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011654444308742952396127 6017481666463114428594191)
              ·
                refine ⟨9026222499694671642891287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017481666463114428594191 9026222499694671642891287)
                ·
                  refine ⟨13539333749542007464336931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9026222499694671642891287 13539333749542007464336931)
                  ·
                    refine ⟨20309000624313011196505397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13539333749542007464336931 20309000624313011196505397)
                    ·
                      refine ⟨1903968808529344799672381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20309000624313011196505397 1903968808529344799672381)
                      ·
                        rfl

theorem cell23_3707966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3707966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707966 prefixEnd_3707966 := by exact prefixLift 3707966
  have htrace : WordTrace (prefixWord ++ tailWord_3707966) baseStart_3707966 baseEnd_3707966 := by
    simpa [prefixWord, tailWord_3707966, baseEnd_3707966] using wordTrace_append hprefix tailTrace_3707966
  have hstable : (prefixWord ++ tailWord_3707966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707966).length < 2 ^ (prefixWord ++ tailWord_3707966).sum := by decide
  have hdescent : baseEnd_3707966 < baseStart_3707966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707989 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 5, 3, 2]
def baseStart_3707989 : Nat := 118140960795 + 3707989 * 2 ^ 59
def prefixEnd_3707989 : Nat := 4983230072969 + 3 ^ 40 * 3707989 * 2
def baseEnd_3707989 : Nat := 1903980618584398209684775

theorem tailTrace_3707989 : CollatzResearch.WordTrace tailWord_3707989 prefixEnd_3707989 1903980618584398209684775 := by
  unfold tailWord_3707989
  simp only [CollatzResearch.WordTrace]
  refine ⟨135241469363596601948783021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90160979575731067965855347 135241469363596601948783021)
  ·
    refine ⟨50715551011348725730793633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135241469363596601948783021 50715551011348725730793633)
    ·
      refine ⟨38036663258511544298095225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50715551011348725730793633 38036663258511544298095225)
      ·
        refine ⟨28527497443883658223571419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38036663258511544298095225 28527497443883658223571419)
        ·
          refine ⟨42791246165825487335357129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28527497443883658223571419 42791246165825487335357129)
          ·
            refine ⟨32093434624369115501517847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42791246165825487335357129 32093434624369115501517847)
            ·
              refine ⟨48140151936553673252276771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32093434624369115501517847 48140151936553673252276771)
              ·
                refine ⟨72210227904830509878415157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48140151936553673252276771 72210227904830509878415157)
                ·
                  refine ⟨6769708866077860301101421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72210227904830509878415157 6769708866077860301101421)
                  ·
                    refine ⟨2538640824779197612913033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6769708866077860301101421 2538640824779197612913033)
                    ·
                      refine ⟨1903980618584398209684775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538640824779197612913033 1903980618584398209684775)
                      ·
                        rfl

theorem cell23_3707989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_3707989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707989 prefixEnd_3707989 := by exact prefixLift 3707989
  have htrace : WordTrace (prefixWord ++ tailWord_3707989) baseStart_3707989 baseEnd_3707989 := by
    simpa [prefixWord, tailWord_3707989, baseEnd_3707989] using wordTrace_append hprefix tailTrace_3707989
  have hstable : (prefixWord ++ tailWord_3707989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707989).length < 2 ^ (prefixWord ++ tailWord_3707989).sum := by decide
  have hdescent : baseEnd_3707989 < baseStart_3707989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707996 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3707996 : Nat := 118140960795 + 3707996 * 2 ^ 59
def prefixEnd_3707996 : Nat := 4983230072969 + 3 ^ 40 * 3707996 * 2
def baseEnd_3707996 : Nat := 1903984212948979682297243

theorem tailTrace_3707996 : CollatzResearch.WordTrace tailWord_3707996 prefixEnd_3707996 1903984212948979682297243 := by
  unfold tailWord_3707996
  simp only [CollatzResearch.WordTrace]
  refine ⟨67620862337285621072143921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90161149783047494762858561 67620862337285621072143921)
  ·
    refine ⟨50715646752964215804107941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67620862337285621072143921 50715646752964215804107941)
    ·
      refine ⟨9509183766180790463270239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50715646752964215804107941 9509183766180790463270239)
      ·
        refine ⟨14263775649271185694905359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9509183766180790463270239 14263775649271185694905359)
        ·
          refine ⟨21395663473906778542358039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14263775649271185694905359 21395663473906778542358039)
          ·
            refine ⟨32093495210860167813537059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21395663473906778542358039 32093495210860167813537059)
            ·
              refine ⟨48140242816290251720305589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32093495210860167813537059 48140242816290251720305589)
              ·
                refine ⟨4513147764027211098778649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48140242816290251720305589 4513147764027211098778649)
                ·
                  refine ⟨3384860823020408324083987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4513147764027211098778649 3384860823020408324083987)
                  ·
                    refine ⟨5077291234530612486125981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3384860823020408324083987 5077291234530612486125981)
                    ·
                      refine ⟨1903984212948979682297243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5077291234530612486125981 1903984212948979682297243)
                      ·
                        rfl

theorem cell23_3707996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3707996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3707996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3707996 prefixEnd_3707996 := by exact prefixLift 3707996
  have htrace : WordTrace (prefixWord ++ tailWord_3707996) baseStart_3707996 baseEnd_3707996 := by
    simpa [prefixWord, tailWord_3707996, baseEnd_3707996] using wordTrace_append hprefix tailTrace_3707996
  have hstable : (prefixWord ++ tailWord_3707996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707996).length < 2 ^ (prefixWord ++ tailWord_3707996).sum := by decide
  have hdescent : baseEnd_3707996 < baseStart_3707996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708032 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_3708032 : Nat := 118140960795 + 3708032 * 2 ^ 59
def prefixEnd_3708032 : Nat := 4983230072969 + 3 ^ 40 * 3708032 * 2
def baseEnd_3708032 : Nat := 1904002698252541541447077

theorem tailTrace_3708032 : CollatzResearch.WordTrace tailWord_3708032 prefixEnd_3708032 1904002698252541541447077 := by
  unfold tailWord_3708032
  simp only [CollatzResearch.WordTrace]
  refine ⟨67621518851220410146299175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90162025134960546861732233 67621518851220410146299175)
  ·
    refine ⟨101432278276830615219448763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67621518851220410146299175 101432278276830615219448763)
    ·
      refine ⟨152148417415245922829173145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101432278276830615219448763 152148417415245922829173145)
      ·
        refine ⟨114111313061434442121879859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152148417415245922829173145 114111313061434442121879859)
        ·
          refine ⟨171166969592151663182819789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114111313061434442121879859 171166969592151663182819789)
          ·
            refine ⟨64187613597056873693557421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171166969592151663182819789 64187613597056873693557421)
            ·
              refine ⟨24070355098896327635084033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64187613597056873693557421 24070355098896327635084033)
              ·
                refine ⟨18052766324172245726313025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24070355098896327635084033 18052766324172245726313025)
                ·
                  refine ⟨13539574743129184294734769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18052766324172245726313025 13539574743129184294734769)
                  ·
                    refine ⟨10154681057346888221051077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13539574743129184294734769 10154681057346888221051077)
                    ·
                      refine ⟨1904002698252541541447077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10154681057346888221051077 1904002698252541541447077)
                      ·
                        rfl

theorem cell23_3708032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_3708032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708032 prefixEnd_3708032 := by exact prefixLift 3708032
  have htrace : WordTrace (prefixWord ++ tailWord_3708032) baseStart_3708032 baseEnd_3708032 := by
    simpa [prefixWord, tailWord_3708032, baseEnd_3708032] using wordTrace_append hprefix tailTrace_3708032
  have hstable : (prefixWord ++ tailWord_3708032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708032).length < 2 ^ (prefixWord ++ tailWord_3708032).sum := by decide
  have hdescent : baseEnd_3708032 < baseStart_3708032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708089 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 2, 5]
def baseStart_3708089 : Nat := 118140960795 + 3708089 * 2 ^ 59
def prefixEnd_3708089 : Nat := 4983230072969 + 3 ^ 40 * 3708089 * 2
def baseEnd_3708089 : Nat := 634677322216615939478105

theorem tailTrace_3708089 : CollatzResearch.WordTrace tailWord_3708089 prefixEnd_3708089 634677322216615939478105 := by
  unfold tailWord_3708089
  simp only [CollatzResearch.WordTrace]
  refine ⟨135245116663234319027423321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90163411108822879351615547 135245116663234319027423321)
  ·
    refine ⟨101433837497425739270567491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135245116663234319027423321 101433837497425739270567491)
    ·
      refine ⟨152150756246138608905851237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101433837497425739270567491 152150756246138608905851237)
      ·
        refine ⟨28528266796150989169847107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152150756246138608905851237 28528266796150989169847107)
        ·
          refine ⟨42792400194226483754770661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28528266796150989169847107 42792400194226483754770661)
          ·
            refine ⟨8023575036417465704019499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42792400194226483754770661 8023575036417465704019499)
            ·
              refine ⟨12035362554626198556029249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8023575036417465704019499 12035362554626198556029249)
              ·
                refine ⟨9026521915969648917021937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12035362554626198556029249 9026521915969648917021937)
                ·
                  refine ⟨6769891436977236687766453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9026521915969648917021937 6769891436977236687766453)
                  ·
                    refine ⟨634677322216615939478105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6769891436977236687766453 634677322216615939478105)
                    ·
                      rfl

theorem cell23_3708089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_3708089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708089 prefixEnd_3708089 := by exact prefixLift 3708089
  have htrace : WordTrace (prefixWord ++ tailWord_3708089) baseStart_3708089 baseEnd_3708089 := by
    simpa [prefixWord, tailWord_3708089, baseEnd_3708089] using wordTrace_append hprefix tailTrace_3708089
  have hstable : (prefixWord ++ tailWord_3708089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708089).length < 2 ^ (prefixWord ++ tailWord_3708089).sum := by decide
  have hdescent : baseEnd_3708089 < baseStart_3708089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708119 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 3, 4]
def baseStart_3708119 : Nat := 118140960795 + 3708119 * 2 ^ 59
def prefixEnd_3708119 : Nat := 4983230072969 + 3 ^ 40 * 3708119 * 2
def baseEnd_3708119 : Nat := 634682457023160900353059

theorem tailTrace_3708119 : CollatzResearch.WordTrace tailWord_3708119 prefixEnd_3708119 634682457023160900353059 := by
  unfold tailWord_3708119
  simp only [CollatzResearch.WordTrace]
  refine ⟨135246210853125634151015411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90164140568750422767343607 135246210853125634151015411)
  ·
    refine ⟨202869316279688451226523117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135246210853125634151015411 202869316279688451226523117)
    ·
      refine ⟨76075993604883169209946169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202869316279688451226523117 76075993604883169209946169)
      ·
        refine ⟨57056995203662376907459627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76075993604883169209946169 57056995203662376907459627)
        ·
          refine ⟨85585492805493565361189441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57056995203662376907459627 85585492805493565361189441)
          ·
            refine ⟨64189119604120174020892081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85585492805493565361189441 64189119604120174020892081)
            ·
              refine ⟨48141839703090130515669061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64189119604120174020892081 48141839703090130515669061)
              ·
                refine ⟨9026594944329399471687949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48141839703090130515669061 9026594944329399471687949)
                ·
                  refine ⟨3384973104123524801882981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9026594944329399471687949 3384973104123524801882981)
                  ·
                    refine ⟨634682457023160900353059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3384973104123524801882981 634682457023160900353059)
                    ·
                      rfl

theorem cell23_3708119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_3708119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708119 prefixEnd_3708119 := by exact prefixLift 3708119
  have htrace : WordTrace (prefixWord ++ tailWord_3708119) baseStart_3708119 baseEnd_3708119 := by
    simpa [prefixWord, tailWord_3708119, baseEnd_3708119] using wordTrace_append hprefix tailTrace_3708119
  have hstable : (prefixWord ++ tailWord_3708119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708119).length < 2 ^ (prefixWord ++ tailWord_3708119).sum := by decide
  have hdescent : baseEnd_3708119 < baseStart_3708119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708122 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_3708122 : Nat := 118140960795 + 3708122 * 2 ^ 59
def prefixEnd_3708122 : Nat := 4983230072969 + 3 ^ 40 * 3708122 * 2
def baseEnd_3708122 : Nat := 1904048911511446189321663

theorem tailTrace_3708122 : CollatzResearch.WordTrace tailWord_3708122 prefixEnd_3708122 1904048911511446189321663 := by
  unfold tailWord_3708122
  simp only [CollatzResearch.WordTrace]
  refine ⟨33811580068028691415843655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90164213514743177108916413 33811580068028691415843655)
  ·
    refine ⟨50717370102043037123765483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33811580068028691415843655 50717370102043037123765483)
    ·
      refine ⟨76076055153064555685648225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50717370102043037123765483 76076055153064555685648225)
      ·
        refine ⟨57057041364798416764236169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76076055153064555685648225 57057041364798416764236169)
        ·
          refine ⟨42792781023598812573177127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57057041364798416764236169 42792781023598812573177127)
          ·
            refine ⟨64189171535398218859765691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42792781023598812573177127 64189171535398218859765691)
            ·
              refine ⟨96283757303097328289648537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64189171535398218859765691 96283757303097328289648537)
              ·
                refine ⟨72212817977322996217236403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96283757303097328289648537 72212817977322996217236403)
                ·
                  refine ⟨108319226965984494325854605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72212817977322996217236403 108319226965984494325854605)
                  ·
                    refine ⟨40619710112244185372195477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108319226965984494325854605 40619710112244185372195477)
                    ·
                      refine ⟨1904048911511446189321663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40619710112244185372195477 1904048911511446189321663)
                      ·
                        rfl

theorem cell23_3708122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_3708122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708122 prefixEnd_3708122 := by exact prefixLift 3708122
  have htrace : WordTrace (prefixWord ++ tailWord_3708122) baseStart_3708122 baseEnd_3708122 := by
    simpa [prefixWord, tailWord_3708122, baseEnd_3708122] using wordTrace_append hprefix tailTrace_3708122
  have hstable : (prefixWord ++ tailWord_3708122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708122).length < 2 ^ (prefixWord ++ tailWord_3708122).sum := by decide
  have hdescent : baseEnd_3708122 < baseStart_3708122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708132 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 10]
def baseStart_3708132 : Nat := 118140960795 + 3708132 * 2 ^ 59
def prefixEnd_3708132 : Nat := 4983230072969 + 3 ^ 40 * 3708132 * 2
def baseEnd_3708132 : Nat := 211561560701999016688513

theorem tailTrace_3708132 : CollatzResearch.WordTrace tailWord_3708132 prefixEnd_3708132 211561560701999016688513 := by
  unfold tailWord_3708132
  simp only [CollatzResearch.WordTrace]
  refine ⟨67623342501039268685619325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90164456668052358247492433 67623342501039268685619325)
  ·
    refine ⟨25358753437889725757107247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67623342501039268685619325 25358753437889725757107247)
    ·
      refine ⟨38038130156834588635660871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25358753437889725757107247 38038130156834588635660871)
      ·
        refine ⟨57057195235251882953491307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38038130156834588635660871 57057195235251882953491307)
        ·
          refine ⟨85585792852877824430236961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57057195235251882953491307 85585792852877824430236961)
          ·
            refine ⟨64189344639658368322677721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85585792852877824430236961 64189344639658368322677721)
            ·
              refine ⟨48142008479743776242008291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64189344639658368322677721 48142008479743776242008291)
              ·
                refine ⟨72213012719615664363012437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48142008479743776242008291 72213012719615664363012437)
                ·
                  refine ⟨211561560701999016688513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 72213012719615664363012437 211561560701999016688513)
                  ·
                    rfl

theorem cell23_3708132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_3708132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708132 prefixEnd_3708132 := by exact prefixLift 3708132
  have htrace : WordTrace (prefixWord ++ tailWord_3708132) baseStart_3708132 baseEnd_3708132 := by
    simpa [prefixWord, tailWord_3708132, baseEnd_3708132] using wordTrace_append hprefix tailTrace_3708132
  have hstable : (prefixWord ++ tailWord_3708132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708132).length < 2 ^ (prefixWord ++ tailWord_3708132).sum := by decide
  have hdescent : baseEnd_3708132 < baseStart_3708132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708196 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_3708196 : Nat := 118140960795 + 3708196 * 2 ^ 59
def prefixEnd_3708196 : Nat := 4983230072969 + 3 ^ 40 * 3708196 * 2
def baseEnd_3708196 : Nat := 634695636359959633265441

theorem tailTrace_3708196 : CollatzResearch.WordTrace tailWord_3708196 prefixEnd_3708196 634695636359959633265441 := by
  unfold tailWord_3708196
  simp only [CollatzResearch.WordTrace]
  refine ⟨67624509636923338150784221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90166012849231117534378961 67624509636923338150784221)
  ·
    refine ⟨25359191113846251806544083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67624509636923338150784221 25359191113846251806544083)
    ·
      refine ⟨38038786670769377709816125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25359191113846251806544083 38038786670769377709816125)
      ·
        refine ⟨14264545001538516641181047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38038786670769377709816125 14264545001538516641181047)
        ·
          refine ⟨21396817502307774961771571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14264545001538516641181047 21396817502307774961771571)
          ·
            refine ⟨32095226253461662442657357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21396817502307774961771571 32095226253461662442657357)
            ·
              refine ⟨12035709845048123415996509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32095226253461662442657357 12035709845048123415996509)
              ·
                refine ⟨4513391191893046280998691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12035709845048123415996509 4513391191893046280998691)
                ·
                  refine ⟨6770086787839569421498037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4513391191893046280998691 6770086787839569421498037)
                  ·
                    refine ⟨634695636359959633265441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6770086787839569421498037 634695636359959633265441)
                    ·
                      rfl

theorem cell23_3708196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_3708196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708196 prefixEnd_3708196 := by exact prefixLift 3708196
  have htrace : WordTrace (prefixWord ++ tailWord_3708196) baseStart_3708196 baseEnd_3708196 := by
    simpa [prefixWord, tailWord_3708196, baseEnd_3708196] using wordTrace_append hprefix tailTrace_3708196
  have hstable : (prefixWord ++ tailWord_3708196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708196).length < 2 ^ (prefixWord ++ tailWord_3708196).sum := by decide
  have hdescent : baseEnd_3708196 < baseStart_3708196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708210 : List Nat := [3, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3]
def baseStart_3708210 : Nat := 118140960795 + 3708210 * 2 ^ 59
def prefixEnd_3708210 : Nat := 4983230072969 + 3 ^ 40 * 3708210 * 2
def baseEnd_3708210 : Nat := 1904094097809041845021259

theorem tailTrace_3708210 : CollatzResearch.WordTrace tailWord_3708210 prefixEnd_3708210 1904094097809041845021259 := by
  unfold tailWord_3708210
  simp only [CollatzResearch.WordTrace]
  refine ⟨33812382473948989173144521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90166353263863971128385389 33812382473948989173144521)
  ·
    refine ⟨25359286855461741879858391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33812382473948989173144521 25359286855461741879858391)
    ·
      refine ⟨38038930283192612819787587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25359286855461741879858391 38038930283192612819787587)
      ·
        refine ⟨57058395424788919229681381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38038930283192612819787587 57058395424788919229681381)
        ·
          refine ⟨10698449142147922355565259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57058395424788919229681381 10698449142147922355565259)
          ·
            refine ⟨16047673713221883533347889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10698449142147922355565259 16047673713221883533347889)
            ·
              refine ⟨12035755284916412650010917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16047673713221883533347889 12035755284916412650010917)
              ·
                refine ⟨2256704115921827371877047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12035755284916412650010917 2256704115921827371877047)
                ·
                  refine ⟨3385056173882741057815571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256704115921827371877047 3385056173882741057815571)
                  ·
                    refine ⟨5077584260824111586723357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3385056173882741057815571 5077584260824111586723357)
                    ·
                      refine ⟨1904094097809041845021259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5077584260824111586723357 1904094097809041845021259)
                      ·
                        rfl

theorem cell23_3708210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_3708210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708210 prefixEnd_3708210 := by exact prefixLift 3708210
  have htrace : WordTrace (prefixWord ++ tailWord_3708210) baseStart_3708210 baseEnd_3708210 := by
    simpa [prefixWord, tailWord_3708210, baseEnd_3708210] using wordTrace_append hprefix tailTrace_3708210
  have hstable : (prefixWord ++ tailWord_3708210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708210).length < 2 ^ (prefixWord ++ tailWord_3708210).sum := by decide
  have hdescent : baseEnd_3708210 < baseStart_3708210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708233 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 3, 2, 2]
def baseStart_3708233 : Nat := 118140960795 + 3708233 * 2 ^ 59
def prefixEnd_3708233 : Nat := 4983230072969 + 3 ^ 40 * 3708233 * 2
def baseEnd_3708233 : Nat := 1904105907864095255033653

theorem tailTrace_3708233 : CollatzResearch.WordTrace tailWord_3708233 prefixEnd_3708233 1904105907864095255033653 := by
  unfold tailWord_3708233
  simp only [CollatzResearch.WordTrace]
  refine ⟨135250368774712631620665353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90166912516475087747110235 135250368774712631620665353)
  ·
    refine ⟨101437776581034473715499015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135250368774712631620665353 101437776581034473715499015)
    ·
      refine ⟨152156664871551710573248523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101437776581034473715499015 152156664871551710573248523)
      ·
        refine ⟨228234997307327565859872785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152156664871551710573248523 228234997307327565859872785)
        ·
          refine ⟨171176247980495674394904589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228234997307327565859872785 171176247980495674394904589)
          ·
            refine ⟨64191092992685877898089221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171176247980495674394904589 64191092992685877898089221)
            ·
              refine ⟨12035829936128602105891729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64191092992685877898089221 12035829936128602105891729)
              ·
                refine ⟨9026872452096451579418797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12035829936128602105891729 9026872452096451579418797)
                ·
                  refine ⟨3385077169536169342282049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9026872452096451579418797 3385077169536169342282049)
                  ·
                    refine ⟨2538807877152127006711537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3385077169536169342282049 2538807877152127006711537)
                    ·
                      refine ⟨1904105907864095255033653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538807877152127006711537 1904105907864095255033653)
                      ·
                        rfl

theorem cell23_3708233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 2, 2].length) (baseStart_3708233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708233 prefixEnd_3708233 := by exact prefixLift 3708233
  have htrace : WordTrace (prefixWord ++ tailWord_3708233) baseStart_3708233 baseEnd_3708233 := by
    simpa [prefixWord, tailWord_3708233, baseEnd_3708233] using wordTrace_append hprefix tailTrace_3708233
  have hstable : (prefixWord ++ tailWord_3708233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708233).length < 2 ^ (prefixWord ++ tailWord_3708233).sum := by decide
  have hdescent : baseEnd_3708233 < baseStart_3708233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708277 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3708277 : Nat := 118140960795 + 3708277 * 2 ^ 59
def prefixEnd_3708277 : Nat := 4983230072969 + 3 ^ 40 * 3708277 * 2
def baseEnd_3708277 : Nat := 634709500337631027627817

theorem tailTrace_3708277 : CollatzResearch.WordTrace tailWord_3708277 prefixEnd_3708277 634709500337631027627817 := by
  unfold tailWord_3708277
  simp only [CollatzResearch.WordTrace]
  refine ⟨135251973586553227135267085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90167982391035484756844723 135251973586553227135267085)
  ·
    refine ⟨50719490094957460175725157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135251973586553227135267085 50719490094957460175725157)
    ·
      refine ⟨9509904392804523782948467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50719490094957460175725157 9509904392804523782948467)
      ·
        refine ⟨14264856589206785674422701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9509904392804523782948467 14264856589206785674422701)
        ·
          refine ⟨5349321220952544627908513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14264856589206785674422701 5349321220952544627908513)
          ·
            refine ⟨4011990915714408470931385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5349321220952544627908513 4011990915714408470931385)
            ·
              refine ⟨3008993186785806353198539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011990915714408470931385 3008993186785806353198539)
              ·
                refine ⟨4513489780178709529797809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008993186785806353198539 4513489780178709529797809)
                ·
                  refine ⟨3385117335134032147348357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4513489780178709529797809 3385117335134032147348357)
                  ·
                    refine ⟨634709500337631027627817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3385117335134032147348357 634709500337631027627817)
                    ·
                      rfl

theorem cell23_3708277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3708277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708277 prefixEnd_3708277 := by exact prefixLift 3708277
  have htrace : WordTrace (prefixWord ++ tailWord_3708277) baseStart_3708277 baseEnd_3708277 := by
    simpa [prefixWord, tailWord_3708277, baseEnd_3708277] using wordTrace_append hprefix tailTrace_3708277
  have hstable : (prefixWord ++ tailWord_3708277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708277).length < 2 ^ (prefixWord ++ tailWord_3708277).sum := by decide
  have hdescent : baseEnd_3708277 < baseStart_3708277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
