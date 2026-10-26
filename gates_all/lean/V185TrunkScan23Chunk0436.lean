import V185TrunkScan23Chunk0435

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2577964 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_2577964 : Nat := 118140960795 + 2577964 * 2 ^ 59
def prefixEnd_2577964 : Nat := 4983230072969 + 3 ^ 40 * 2577964 * 2
def baseEnd_2577964 : Nat := 441244880662485645898055

theorem tailTrace_2577964 : CollatzResearch.WordTrace tailWord_2577964 prefixEnd_2577964 441244880662485645898055 := by
  unfold tailWord_2577964
  simp only [CollatzResearch.WordTrace]
  refine ⟨47013035816242092021866473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62684047754989456029155297 47013035816242092021866473)
  ·
    refine ⟨35259776862181569016399855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47013035816242092021866473 35259776862181569016399855)
    ·
      refine ⟨52889665293272353524599783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35259776862181569016399855 52889665293272353524599783)
      ·
        refine ⟨79334497939908530286899675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52889665293272353524599783 79334497939908530286899675)
        ·
          refine ⟨119001746909862795430349513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79334497939908530286899675 119001746909862795430349513)
          ·
            refine ⟨89251310182397096572762135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119001746909862795430349513 89251310182397096572762135)
            ·
              refine ⟨133876965273595644859143203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89251310182397096572762135 133876965273595644859143203)
              ·
                refine ⟨200815447910393467288714805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133876965273595644859143203 200815447910393467288714805)
                ·
                  refine ⟨18826448241599387558317013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200815447910393467288714805 18826448241599387558317013)
                  ·
                    refine ⟨441244880662485645898055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18826448241599387558317013 441244880662485645898055)
                    ·
                      rfl

theorem cell23_2577964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_2577964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577964 prefixEnd_2577964 := by exact prefixLift 2577964
  have htrace : WordTrace (prefixWord ++ tailWord_2577964) baseStart_2577964 baseEnd_2577964 := by
    simpa [prefixWord, tailWord_2577964, baseEnd_2577964] using wordTrace_append hprefix tailTrace_2577964
  have hstable : (prefixWord ++ tailWord_2577964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577964).length < 2 ^ (prefixWord ++ tailWord_2577964).sum := by decide
  have hdescent : baseEnd_2577964 < baseStart_2577964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578001 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_2578001 : Nat := 118140960795 + 2578001 * 2 ^ 59
def prefixEnd_2578001 : Nat := 4983230072969 + 3 ^ 40 * 2578001 * 2
def baseEnd_2578001 : Nat := 1323753640771673292931495

theorem tailTrace_2578001 : CollatzResearch.WordTrace tailWord_2578001 prefixEnd_2578001 1323753640771673292931495 := by
  unfold tailWord_2578001
  simp only [CollatzResearch.WordTrace]
  refine ⟨94027421133350139362829857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62684947422233426241886571 94027421133350139362829857)
  ·
    refine ⟨70520565850012604522122393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94027421133350139362829857 70520565850012604522122393)
    ·
      refine ⟨52890424387509453391591795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70520565850012604522122393 52890424387509453391591795)
      ·
        refine ⟨79335636581264180087387693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52890424387509453391591795 79335636581264180087387693)
        ·
          refine ⟨29750863717974067532770385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79335636581264180087387693 29750863717974067532770385)
          ·
            refine ⟨22313147788480550649577789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29750863717974067532770385 22313147788480550649577789)
            ·
              refine ⟨8367430420680206493591671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22313147788480550649577789 8367430420680206493591671)
              ·
                refine ⟨12551145631020309740387507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8367430420680206493591671 12551145631020309740387507)
                ·
                  refine ⟨18826718446530464610581261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12551145631020309740387507 18826718446530464610581261)
                  ·
                    refine ⟨7060019417448924228967973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18826718446530464610581261 7060019417448924228967973)
                    ·
                      refine ⟨1323753640771673292931495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7060019417448924228967973 1323753640771673292931495)
                      ·
                        rfl

theorem cell23_2578001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_2578001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578001 prefixEnd_2578001 := by exact prefixLift 2578001
  have htrace : WordTrace (prefixWord ++ tailWord_2578001) baseStart_2578001 baseEnd_2578001 := by
    simpa [prefixWord, tailWord_2578001, baseEnd_2578001] using wordTrace_append hprefix tailTrace_2578001
  have hstable : (prefixWord ++ tailWord_2578001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578001).length < 2 ^ (prefixWord ++ tailWord_2578001).sum := by decide
  have hdescent : baseEnd_2578001 < baseStart_2578001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578013 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2578013 : Nat := 118140960795 + 2578013 * 2 ^ 59
def prefixEnd_2578013 : Nat := 4983230072969 + 3 ^ 40 * 2578013 * 2
def baseEnd_2578013 : Nat := 1323759802539527245981441

theorem tailTrace_2578013 : CollatzResearch.WordTrace tailWord_2578013 prefixEnd_2578013 1323759802539527245981441 := by
  unfold tailWord_2578013
  simp only [CollatzResearch.WordTrace]
  refine ⟨94027858809306665412266693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62685239206204443608177795 94027858809306665412266693)
  ·
    refine ⟨17630223526744999764800005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94027858809306665412266693 17630223526744999764800005)
    ·
      refine ⟨3305666911264687455900001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17630223526744999764800005 3305666911264687455900001)
      ·
        refine ⟨2479250183448515591925001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3305666911264687455900001 2479250183448515591925001)
        ·
          refine ⟨1859437637586386693943751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2479250183448515591925001 1859437637586386693943751)
          ·
            refine ⟨2789156456379580040915627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1859437637586386693943751 2789156456379580040915627)
            ·
              refine ⟨4183734684569370061373441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789156456379580040915627 4183734684569370061373441)
              ·
                refine ⟨3137801013427027546030081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4183734684569370061373441 3137801013427027546030081)
                ·
                  refine ⟨2353350760070270659522561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3137801013427027546030081 2353350760070270659522561)
                  ·
                    refine ⟨1765013070052702994641921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2353350760070270659522561 1765013070052702994641921)
                    ·
                      refine ⟨1323759802539527245981441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1765013070052702994641921 1323759802539527245981441)
                      ·
                        rfl

theorem cell23_2578013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2578013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578013 prefixEnd_2578013 := by exact prefixLift 2578013
  have htrace : WordTrace (prefixWord ++ tailWord_2578013) baseStart_2578013 baseEnd_2578013 := by
    simpa [prefixWord, tailWord_2578013, baseEnd_2578013] using wordTrace_append hprefix tailTrace_2578013
  have hstable : (prefixWord ++ tailWord_2578013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578013).length < 2 ^ (prefixWord ++ tailWord_2578013).sum := by decide
  have hdescent : baseEnd_2578013 < baseStart_2578013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578051 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 3]
def baseStart_2578051 : Nat := 118140960795 + 2578051 * 2 ^ 59
def prefixEnd_2578051 : Nat := 4983230072969 + 3 ^ 40 * 2578051 * 2
def baseEnd_2578051 : Nat := 1323779314804398097306265

theorem tailTrace_2578051 : CollatzResearch.WordTrace tailWord_2578051 prefixEnd_2578051 1323779314804398097306265 := by
  unfold tailWord_2578051
  simp only [CollatzResearch.WordTrace]
  refine ⟨94029244783168997902150007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62686163188779331934766671 94029244783168997902150007)
  ·
    refine ⟨141043867174753496853225011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94029244783168997902150007 141043867174753496853225011)
    ·
      refine ⟨211565800762130245279837517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141043867174753496853225011 211565800762130245279837517)
      ·
        refine ⟨79337175285798841979939069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211565800762130245279837517 79337175285798841979939069)
        ·
          refine ⟨29751440732174565742477151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79337175285798841979939069 29751440732174565742477151)
          ·
            refine ⟨44627161098261848613715727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29751440732174565742477151 44627161098261848613715727)
            ·
              refine ⟨66940741647392772920573591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44627161098261848613715727 66940741647392772920573591)
              ·
                refine ⟨100411112471089159380860387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66940741647392772920573591 100411112471089159380860387)
                ·
                  refine ⟨150616668706633739071290581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100411112471089159380860387 150616668706633739071290581)
                  ·
                    refine ⟨3530078172811728259483373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 150616668706633739071290581 3530078172811728259483373)
                    ·
                      refine ⟨1323779314804398097306265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3530078172811728259483373 1323779314804398097306265)
                      ·
                        rfl

theorem cell23_2578051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_2578051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578051 prefixEnd_2578051 := by exact prefixLift 2578051
  have htrace : WordTrace (prefixWord ++ tailWord_2578051) baseStart_2578051 baseEnd_2578051 := by
    simpa [prefixWord, tailWord_2578051, baseEnd_2578051] using wordTrace_append hprefix tailTrace_2578051
  have hstable : (prefixWord ++ tailWord_2578051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578051).length < 2 ^ (prefixWord ++ tailWord_2578051).sum := by decide
  have hdescent : baseEnd_2578051 < baseStart_2578051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578062 : List Nat := [4, 1, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_2578062 : Nat := 118140960795 + 2578062 * 2 ^ 59
def prefixEnd_2578062 : Nat := 4983230072969 + 3 ^ 40 * 2578062 * 2
def baseEnd_2578062 : Nat := 441261654363865851422905

theorem tailTrace_2578062 : CollatzResearch.WordTrace tailWord_2578062 prefixEnd_2578062 441261654363865851422905 := by
  unfold tailWord_2578062
  simp only [CollatzResearch.WordTrace]
  refine ⟨11753705748266143347600055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62686430657419431187200293 11753705748266143347600055)
  ·
    refine ⟨17630558622399215021400083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11753705748266143347600055 17630558622399215021400083)
    ·
      refine ⟨26445837933598822532100125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17630558622399215021400083 26445837933598822532100125)
      ·
        refine ⟨9917189225099558449537547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26445837933598822532100125 9917189225099558449537547)
        ·
          refine ⟨14875783837649337674306321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9917189225099558449537547 14875783837649337674306321)
          ·
            refine ⟨11156837878237003255729741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14875783837649337674306321 11156837878237003255729741)
            ·
              refine ⟨4183814204338876220898653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11156837878237003255729741 4183814204338876220898653)
              ·
                refine ⟨1568930326627078582836995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4183814204338876220898653 1568930326627078582836995)
                ·
                  refine ⟨2353395489940617874255493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568930326627078582836995 2353395489940617874255493)
                  ·
                    refine ⟨441261654363865851422905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353395489940617874255493 441261654363865851422905)
                    ·
                      rfl

theorem cell23_2578062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_2578062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578062 prefixEnd_2578062 := by exact prefixLift 2578062
  have htrace : WordTrace (prefixWord ++ tailWord_2578062) baseStart_2578062 baseEnd_2578062 := by
    simpa [prefixWord, tailWord_2578062, baseEnd_2578062] using wordTrace_append hprefix tailTrace_2578062
  have hstable : (prefixWord ++ tailWord_2578062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578062).length < 2 ^ (prefixWord ++ tailWord_2578062).sum := by decide
  have hdescent : baseEnd_2578062 < baseStart_2578062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578079 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 3, 4]
def baseStart_2578079 : Nat := 118140960795 + 2578079 * 2 ^ 59
def prefixEnd_2578079 : Nat := 4983230072969 + 3 ^ 40 * 2578079 * 2
def baseEnd_2578079 : Nat := 441264564087574662585379

theorem tailTrace_2578079 : CollatzResearch.WordTrace tailWord_2578079 prefixEnd_2578079 441264564087574662585379 := by
  unfold tailWord_2578079
  simp only [CollatzResearch.WordTrace]
  refine ⟨94030266027067558684169291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62686844018045039122779527 94030266027067558684169291)
  ·
    refine ⟨141045399040601338026253937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94030266027067558684169291 141045399040601338026253937)
    ·
      refine ⟨105784049280451003519690453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141045399040601338026253937 105784049280451003519690453)
      ·
        refine ⟨2479313655010570394992745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 105784049280451003519690453 2479313655010570394992745)
        ·
          refine ⟨1859485241257927796244559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2479313655010570394992745 1859485241257927796244559)
          ·
            refine ⟨2789227861886891694366839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1859485241257927796244559 2789227861886891694366839)
            ·
              refine ⟨4183841792830337541550259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789227861886891694366839 4183841792830337541550259)
              ·
                refine ⟨6275762689245506312325389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183841792830337541550259 6275762689245506312325389)
                ·
                  refine ⟨2353411008467064867122021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6275762689245506312325389 2353411008467064867122021)
                  ·
                    refine ⟨441264564087574662585379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353411008467064867122021 441264564087574662585379)
                    ·
                      rfl

theorem cell23_2578079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 3, 4].length) (baseStart_2578079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578079 prefixEnd_2578079 := by exact prefixLift 2578079
  have htrace : WordTrace (prefixWord ++ tailWord_2578079) baseStart_2578079 baseEnd_2578079 := by
    simpa [prefixWord, tailWord_2578079, baseEnd_2578079] using wordTrace_append hprefix tailTrace_2578079
  have hstable : (prefixWord ++ tailWord_2578079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578079).length < 2 ^ (prefixWord ++ tailWord_2578079).sum := by decide
  have hdescent : baseEnd_2578079 < baseStart_2578079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578085 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 3, 1, 3]
def baseStart_2578085 : Nat := 118140960795 + 2578085 * 2 ^ 59
def prefixEnd_2578085 : Nat := 4983230072969 + 3 ^ 40 * 2578085 * 2
def baseEnd_2578085 : Nat := 1323796773146650964281109

theorem tailTrace_2578085 : CollatzResearch.WordTrace tailWord_2578085 prefixEnd_2578085 1323796773146650964281109 := by
  unfold tailWord_2578085
  simp only [CollatzResearch.WordTrace]
  refine ⟨94030484865045821708887709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62686989910030547805925139 94030484865045821708887709)
  ·
    refine ⟨35261431824392183140832891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94030484865045821708887709 35261431824392183140832891)
    ·
      refine ⟨52892147736588274711249337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35261431824392183140832891 52892147736588274711249337)
      ·
        refine ⟨39669110802441206033437003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52892147736588274711249337 39669110802441206033437003)
        ·
          refine ⟨59503666203661809050155505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39669110802441206033437003 59503666203661809050155505)
          ·
            refine ⟨44627749652746356787616629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59503666203661809050155505 44627749652746356787616629)
            ·
              refine ⟨4183851529944970948839059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44627749652746356787616629 4183851529944970948839059)
              ·
                refine ⟨6275777294917456423258589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183851529944970948839059 6275777294917456423258589)
                ·
                  refine ⟨2353416485594046158721971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6275777294917456423258589 2353416485594046158721971)
                  ·
                    refine ⟨3530124728391069238082957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2353416485594046158721971 3530124728391069238082957)
                    ·
                      refine ⟨1323796773146650964281109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3530124728391069238082957 1323796773146650964281109)
                      ·
                        rfl

theorem cell23_2578085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_2578085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578085 prefixEnd_2578085 := by exact prefixLift 2578085
  have htrace : WordTrace (prefixWord ++ tailWord_2578085) baseStart_2578085 baseEnd_2578085 := by
    simpa [prefixWord, tailWord_2578085, baseEnd_2578085] using wordTrace_append hprefix tailTrace_2578085
  have hstable : (prefixWord ++ tailWord_2578085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578085).length < 2 ^ (prefixWord ++ tailWord_2578085).sum := by decide
  have hdescent : baseEnd_2578085 < baseStart_2578085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578122 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 1, 5]
def baseStart_2578122 : Nat := 118140960795 + 2578122 * 2 ^ 59
def prefixEnd_2578122 : Nat := 4983230072969 + 3 ^ 40 * 2578122 * 2
def baseEnd_2578122 : Nat := 441271923976955773172813

theorem tailTrace_2578122 : CollatzResearch.WordTrace tailWord_2578122 prefixEnd_2578122 441271923976955773172813 := by
  unfold tailWord_2578122
  simp only [CollatzResearch.WordTrace]
  refine ⟨23507958591477944256996155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62687889577274518018656413 23507958591477944256996155)
  ·
    refine ⟨35261937887216916385494233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23507958591477944256996155 35261937887216916385494233)
    ·
      refine ⟨26446453415412687289120675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35261937887216916385494233 26446453415412687289120675)
      ·
        refine ⟨39669680123119030933681013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26446453415412687289120675 39669680123119030933681013)
        ·
          refine ⟨3719032511542409150032595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39669680123119030933681013 3719032511542409150032595)
          ·
            refine ⟨5578548767313613725048893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719032511542409150032595 5578548767313613725048893)
            ·
              refine ⟨2091955787742605146893335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5578548767313613725048893 2091955787742605146893335)
              ·
                refine ⟨3137933681613907720340003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091955787742605146893335 3137933681613907720340003)
                ·
                  refine ⟨4706900522420861580510005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137933681613907720340003 4706900522420861580510005)
                  ·
                    refine ⟨441271923976955773172813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4706900522420861580510005 441271923976955773172813)
                    ·
                      rfl

theorem cell23_2578122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_2578122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578122 prefixEnd_2578122 := by exact prefixLift 2578122
  have htrace : WordTrace (prefixWord ++ tailWord_2578122) baseStart_2578122 baseEnd_2578122 := by
    simpa [prefixWord, tailWord_2578122, baseEnd_2578122] using wordTrace_append hprefix tailTrace_2578122
  have hstable : (prefixWord ++ tailWord_2578122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578122).length < 2 ^ (prefixWord ++ tailWord_2578122).sum := by decide
  have hdescent : baseEnd_2578122 < baseStart_2578122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578135 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 2, 4]
def baseStart_2578135 : Nat := 118140960795 + 2578135 * 2 ^ 59
def prefixEnd_2578135 : Nat := 4983230072969 + 3 ^ 40 * 2578135 * 2
def baseEnd_2578135 : Nat := 441274149059791922885293

theorem tailTrace_2578135 : CollatzResearch.WordTrace tailWord_2578135 prefixEnd_2578135 441274149059791922885293 := by
  unfold tailWord_2578135
  simp only [CollatzResearch.WordTrace]
  refine ⟨94032308514864680248207859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62688205676576453498805239 94032308514864680248207859)
  ·
    refine ⟨141048462772297020372311789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94032308514864680248207859 141048462772297020372311789)
    ·
      refine ⟨52893173539611382639616921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141048462772297020372311789 52893173539611382639616921)
      ·
        refine ⟨39669880154708536979712691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52893173539611382639616921 39669880154708536979712691)
        ·
          refine ⟨59504820232062805469569037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39669880154708536979712691 59504820232062805469569037)
          ·
            refine ⟨22314307587023552051088389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59504820232062805469569037 22314307587023552051088389)
            ·
              refine ⟨4183932672566916009579073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22314307587023552051088389 4183932672566916009579073)
              ·
                refine ⟨3137949504425187007184305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4183932672566916009579073 3137949504425187007184305)
                ·
                  refine ⟨2353462128318890255388229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3137949504425187007184305 2353462128318890255388229)
                  ·
                    refine ⟨441274149059791922885293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353462128318890255388229 441274149059791922885293)
                    ·
                      rfl

theorem cell23_2578135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_2578135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578135 prefixEnd_2578135 := by exact prefixLift 2578135
  have htrace : WordTrace (prefixWord ++ tailWord_2578135) baseStart_2578135 baseEnd_2578135 := by
    simpa [prefixWord, tailWord_2578135, baseEnd_2578135] using wordTrace_append hprefix tailTrace_2578135
  have hstable : (prefixWord ++ tailWord_2578135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578135).length < 2 ^ (prefixWord ++ tailWord_2578135).sum := by decide
  have hdescent : baseEnd_2578135 < baseStart_2578135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578206 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2578206 : Nat := 118140960795 + 2578206 * 2 ^ 59
def prefixEnd_2578206 : Nat := 4983230072969 + 3 ^ 40 * 2578206 * 2
def baseEnd_2578206 : Nat := 1323858904305844990868053

theorem tailTrace_2578206 : CollatzResearch.WordTrace tailWord_2578206 prefixEnd_2578206 1323858904305844990868053 := by
  unfold tailWord_2578206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11754362262200932421755309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62689932065071639582694981 11754362262200932421755309)
  ·
    refine ⟨4407885848325349658158241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11754362262200932421755309 4407885848325349658158241)
    ·
      refine ⟨3305914386244012243618681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4407885848325349658158241 3305914386244012243618681)
      ·
        refine ⟨2479435789683009182714011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3305914386244012243618681 2479435789683009182714011)
        ·
          refine ⟨3719153684524513774071017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2479435789683009182714011 3719153684524513774071017)
          ·
            refine ⟨2789365263393385330553263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3719153684524513774071017 2789365263393385330553263)
            ·
              refine ⟨4184047895090077995829895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789365263393385330553263 4184047895090077995829895)
              ·
                refine ⟨6276071842635116993744843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4184047895090077995829895 6276071842635116993744843)
                ·
                  refine ⟨9414107763952675490617265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6276071842635116993744843 9414107763952675490617265)
                  ·
                    refine ⟨7060580822964506617962949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9414107763952675490617265 7060580822964506617962949)
                    ·
                      refine ⟨1323858904305844990868053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7060580822964506617962949 1323858904305844990868053)
                      ·
                        rfl

theorem cell23_2578206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2578206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578206 prefixEnd_2578206 := by exact prefixLift 2578206
  have htrace : WordTrace (prefixWord ++ tailWord_2578206) baseStart_2578206 baseEnd_2578206 := by
    simpa [prefixWord, tailWord_2578206, baseEnd_2578206] using wordTrace_append hprefix tailTrace_2578206
  have hstable : (prefixWord ++ tailWord_2578206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578206).length < 2 ^ (prefixWord ++ tailWord_2578206).sum := by decide
  have hdescent : baseEnd_2578206 < baseStart_2578206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578208 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 2, 6]
def baseStart_2578208 : Nat := 118140960795 + 2578208 * 2 ^ 59
def prefixEnd_2578208 : Nat := 4983230072969 + 3 ^ 40 * 2578208 * 2
def baseEnd_2578208 : Nat := 441286643755717994347681

theorem tailTrace_2578208 : CollatzResearch.WordTrace tailWord_2578208 prefixEnd_2578208 441286643755717994347681 := by
  unfold tailWord_2578208
  simp only [CollatzResearch.WordTrace]
  refine ⟨47017485521800106857807639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62689980695733475810410185 47017485521800106857807639)
  ·
    refine ⟨70526228282700160286711459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47017485521800106857807639 70526228282700160286711459)
    ·
      refine ⟨105789342424050240430067189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70526228282700160286711459 105789342424050240430067189)
      ·
        refine ⟨9917750852254710040318799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105789342424050240430067189 9917750852254710040318799)
        ·
          refine ⟨14876626278382065060478199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9917750852254710040318799 14876626278382065060478199)
          ·
            refine ⟨22314939417573097590717299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14876626278382065060478199 22314939417573097590717299)
            ·
              refine ⟨33472409126359646386075949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22314939417573097590717299 33472409126359646386075949)
              ·
                refine ⟨12552153422384867394778481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33472409126359646386075949 12552153422384867394778481)
                ·
                  refine ⟨9414115066788650546083861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12552153422384867394778481 9414115066788650546083861)
                  ·
                    refine ⟨441286643755717994347681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9414115066788650546083861 441286643755717994347681)
                    ·
                      rfl

theorem cell23_2578208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_2578208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578208 prefixEnd_2578208 := by exact prefixLift 2578208
  have htrace : WordTrace (prefixWord ++ tailWord_2578208) baseStart_2578208 baseEnd_2578208 := by
    simpa [prefixWord, tailWord_2578208, baseEnd_2578208] using wordTrace_append hprefix tailTrace_2578208
  have hstable : (prefixWord ++ tailWord_2578208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578208).length < 2 ^ (prefixWord ++ tailWord_2578208).sum := by decide
  have hdescent : baseEnd_2578208 < baseStart_2578208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578209 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 2, 1, 3]
def baseStart_2578209 : Nat := 118140960795 + 2578209 * 2 ^ 59
def prefixEnd_2578209 : Nat := 4983230072969 + 3 ^ 40 * 2578209 * 2
def baseEnd_2578209 : Nat := 1323860444747808479130539

theorem tailTrace_2578209 : CollatzResearch.WordTrace tailWord_2578209 prefixEnd_2578209 1323860444747808479130539 := by
  unfold tailWord_2578209
  simp only [CollatzResearch.WordTrace]
  refine ⟨94035007516596590886401681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62690005011064393924267787 94035007516596590886401681)
  ·
    refine ⟨70526255637447443164801261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94035007516596590886401681 70526255637447443164801261)
    ·
      refine ⟨26447345864042791186800473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70526255637447443164801261 26447345864042791186800473)
      ·
        refine ⟨19835509398032093390100355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26447345864042791186800473 19835509398032093390100355)
        ·
          refine ⟨29753264097048140085150533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19835509398032093390100355 29753264097048140085150533)
          ·
            refine ⟨5578737018196526265965725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29753264097048140085150533 5578737018196526265965725)
            ·
              refine ⟨2092026381823697349737147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5578737018196526265965725 2092026381823697349737147)
              ·
                refine ⟨3138039572735546024605721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092026381823697349737147 3138039572735546024605721)
                ·
                  refine ⟨2353529679551659518454291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138039572735546024605721 2353529679551659518454291)
                  ·
                    refine ⟨3530294519327489277681437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2353529679551659518454291 3530294519327489277681437)
                    ·
                      refine ⟨1323860444747808479130539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3530294519327489277681437 1323860444747808479130539)
                      ·
                        rfl

theorem cell23_2578209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_2578209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578209 prefixEnd_2578209 := by exact prefixLift 2578209
  have htrace : WordTrace (prefixWord ++ tailWord_2578209) baseStart_2578209 baseEnd_2578209 := by
    simpa [prefixWord, tailWord_2578209, baseEnd_2578209] using wordTrace_append hprefix tailTrace_2578209
  have hstable : (prefixWord ++ tailWord_2578209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578209).length < 2 ^ (prefixWord ++ tailWord_2578209).sum := by decide
  have hdescent : baseEnd_2578209 < baseStart_2578209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578232 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 4, 2, 2]
def baseStart_2578232 : Nat := 118140960795 + 2578232 * 2 ^ 59
def prefixEnd_2578232 : Nat := 4983230072969 + 3 ^ 40 * 2578232 * 2
def baseEnd_2578232 : Nat := 1323872254802861889142933

theorem tailTrace_2578232 : CollatzResearch.WordTrace tailWord_2578232 prefixEnd_2578232 1323872254802861889142933 := by
  unfold tailWord_2578232
  simp only [CollatzResearch.WordTrace]
  refine ⟨47017923197756632907244475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62690564263675510542992633 47017923197756632907244475)
  ·
    refine ⟨70526884796634949360866713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47017923197756632907244475 70526884796634949360866713)
    ·
      refine ⟨52895163597476212020650035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70526884796634949360866713 52895163597476212020650035)
      ·
        refine ⟨79342745396214318030975053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52895163597476212020650035 79342745396214318030975053)
        ·
          refine ⟨29753529523580369261615645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79342745396214318030975053 29753529523580369261615645)
          ·
            refine ⟨11157573571342638473105867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29753529523580369261615645 11157573571342638473105867)
            ·
              refine ⟨16736360357013957709658801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11157573571342638473105867 16736360357013957709658801)
              ·
                refine ⟨12552270267760468282244101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16736360357013957709658801 12552270267760468282244101)
                ·
                  refine ⟨2353550675205087802920769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12552270267760468282244101 2353550675205087802920769)
                  ·
                    refine ⟨1765163006403815852190577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2353550675205087802920769 1765163006403815852190577)
                    ·
                      refine ⟨1323872254802861889142933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1765163006403815852190577 1323872254802861889142933)
                      ·
                        rfl

theorem cell23_2578232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_2578232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578232 prefixEnd_2578232 := by exact prefixLift 2578232
  have htrace : WordTrace (prefixWord ++ tailWord_2578232) baseStart_2578232 baseEnd_2578232 := by
    simpa [prefixWord, tailWord_2578232, baseEnd_2578232] using wordTrace_append hprefix tailTrace_2578232
  have hstable : (prefixWord ++ tailWord_2578232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578232).length < 2 ^ (prefixWord ++ tailWord_2578232).sum := by decide
  have hdescent : baseEnd_2578232 < baseStart_2578232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578285 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_2578285 : Nat := 118140960795 + 2578285 * 2 ^ 59
def prefixEnd_2578285 : Nat := 4983230072969 + 3 ^ 40 * 2578285 * 2
def baseEnd_2578285 : Nat := 441299823092516727260063

theorem tailTrace_2578285 : CollatzResearch.WordTrace tailWord_2578285 prefixEnd_2578285 441299823092516727260063 := by
  unfold tailWord_2578285
  simp only [CollatzResearch.WordTrace]
  refine ⟨94037779464321255866168309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62691852976214170577445539 94037779464321255866168309)
  ·
    refine ⟨8816041824780117737453279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94037779464321255866168309 8816041824780117737453279)
    ·
      refine ⟨13224062737170176606179919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8816041824780117737453279 13224062737170176606179919)
      ·
        refine ⟨19836094105755264909269879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13224062737170176606179919 19836094105755264909269879)
        ·
          refine ⟨29754141158632897363904819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19836094105755264909269879 29754141158632897363904819)
          ·
            refine ⟨44631211737949346045857229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29754141158632897363904819 44631211737949346045857229)
            ·
              refine ⟨16736704401731004767196461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44631211737949346045857229 16736704401731004767196461)
              ·
                refine ⟨6276264150649126787698673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16736704401731004767196461 6276264150649126787698673)
                ·
                  refine ⟨4707198112986845090774005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6276264150649126787698673 4707198112986845090774005)
                  ·
                    refine ⟨441299823092516727260063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4707198112986845090774005 441299823092516727260063)
                    ·
                      rfl

theorem cell23_2578285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_2578285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578285 prefixEnd_2578285 := by exact prefixLift 2578285
  have htrace : WordTrace (prefixWord ++ tailWord_2578285) baseStart_2578285 baseEnd_2578285 := by
    simpa [prefixWord, tailWord_2578285, baseEnd_2578285] using wordTrace_append hprefix tailTrace_2578285
  have hstable : (prefixWord ++ tailWord_2578285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578285).length < 2 ^ (prefixWord ++ tailWord_2578285).sum := by decide
  have hdescent : baseEnd_2578285 < baseStart_2578285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578315 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 3, 4]
def baseStart_2578315 : Nat := 118140960795 + 2578315 * 2 ^ 59
def prefixEnd_2578315 : Nat := 4983230072969 + 3 ^ 40 * 2578315 * 2
def baseEnd_2578315 : Nat := 441304957899061688135017

theorem tailTrace_2578315 : CollatzResearch.WordTrace tailWord_2578315 prefixEnd_2578315 441304957899061688135017 := by
  unfold tailWord_2578315
  simp only [CollatzResearch.WordTrace]
  refine ⟨94038873654212570989760399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62692582436141713993173599 94038873654212570989760399)
  ·
    refine ⟨141058310481318856484640599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94038873654212570989760399 141058310481318856484640599)
    ·
      refine ⟨211587465721978284726960899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141058310481318856484640599 211587465721978284726960899)
      ·
        refine ⟨317381198582967427090441349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211587465721978284726960899 317381198582967427090441349)
        ·
          refine ⟨59508974734306392579457753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 317381198582967427090441349 59508974734306392579457753)
          ·
            refine ⟨44631731050729794434593315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59508974734306392579457753 44631731050729794434593315)
            ·
              refine ⟨66947596576094691651889973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44631731050729794434593315 66947596576094691651889973)
              ·
                refine ⟨6276337179008877342364685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66947596576094691651889973 6276337179008877342364685)
                ·
                  refine ⟨2353626442128329003386757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6276337179008877342364685 2353626442128329003386757)
                  ·
                    refine ⟨441304957899061688135017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353626442128329003386757 441304957899061688135017)
                    ·
                      rfl

theorem cell23_2578315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 4].length) (baseStart_2578315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578315 prefixEnd_2578315 := by exact prefixLift 2578315
  have htrace : WordTrace (prefixWord ++ tailWord_2578315) baseStart_2578315 baseEnd_2578315 := by
    simpa [prefixWord, tailWord_2578315, baseEnd_2578315] using wordTrace_append hprefix tailTrace_2578315
  have hstable : (prefixWord ++ tailWord_2578315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578315).length < 2 ^ (prefixWord ++ tailWord_2578315).sum := by decide
  have hdescent : baseEnd_2578315 < baseStart_2578315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578325 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_2578325 : Nat := 118140960795 + 2578325 * 2 ^ 59
def prefixEnd_2578325 : Nat := 4983230072969 + 3 ^ 40 * 2578325 * 2
def baseEnd_2578325 : Nat := 1323920008503730025280005

theorem tailTrace_2578325 : CollatzResearch.WordTrace tailWord_2578325 prefixEnd_2578325 1323920008503730025280005 := by
  unfold tailWord_2578325
  simp only [CollatzResearch.WordTrace]
  refine ⟨94039238384176342697624429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62692825589450895131749619 94039238384176342697624429)
  ·
    refine ⟨35264714394066128511609161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94039238384176342697624429 35264714394066128511609161)
    ·
      refine ⟨26448535795549596383706871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35264714394066128511609161 26448535795549596383706871)
      ·
        refine ⟨39672803693324394575560307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26448535795549596383706871 39672803693324394575560307)
        ·
          refine ⟨59509205539986591863340461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39672803693324394575560307 59509205539986591863340461)
          ·
            refine ⟨22315952077494971948752673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59509205539986591863340461 22315952077494971948752673)
            ·
              refine ⟨16736964058121228961564505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22315952077494971948752673 16736964058121228961564505)
              ·
                refine ⟨12552723043590921721173379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16736964058121228961564505 12552723043590921721173379)
                ·
                  refine ⟨18829084565386382581760069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12552723043590921721173379 18829084565386382581760069)
                  ·
                    refine ⟨3530453356009946734080013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18829084565386382581760069 3530453356009946734080013)
                    ·
                      refine ⟨1323920008503730025280005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3530453356009946734080013 1323920008503730025280005)
                      ·
                        rfl

theorem cell23_2578325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_2578325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578325 prefixEnd_2578325 := by exact prefixLift 2578325
  have htrace : WordTrace (prefixWord ++ tailWord_2578325) baseStart_2578325 baseEnd_2578325 := by
    simpa [prefixWord, tailWord_2578325, baseEnd_2578325] using wordTrace_append hprefix tailTrace_2578325
  have hstable : (prefixWord ++ tailWord_2578325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578325).length < 2 ^ (prefixWord ++ tailWord_2578325).sum := by decide
  have hdescent : baseEnd_2578325 < baseStart_2578325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578332 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_2578332 : Nat := 118140960795 + 2578332 * 2 ^ 59
def prefixEnd_2578332 : Nat := 4983230072969 + 3 ^ 40 * 2578332 * 2
def baseEnd_2578332 : Nat := 441307867622770499297491

theorem tailTrace_2578332 : CollatzResearch.WordTrace tailWord_2578332 prefixEnd_2578332 441307867622770499297491 := by
  unfold tailWord_2578332
  simp only [CollatzResearch.WordTrace]
  refine ⟨47019746847575491446564625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62692995796767321928752833 47019746847575491446564625)
  ·
    refine ⟨35264810135681618584923469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47019746847575491446564625 35264810135681618584923469)
    ·
      refine ⟨13224303800880606969346301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35264810135681618584923469 13224303800880606969346301)
      ·
        refine ⟨4959113925330227613504863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13224303800880606969346301 4959113925330227613504863)
        ·
          refine ⟨7438670887995341420257295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4959113925330227613504863 7438670887995341420257295)
          ·
            refine ⟨11158006331993012130385943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7438670887995341420257295 11158006331993012130385943)
            ·
              refine ⟨16737009497989518195578915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11158006331993012130385943 16737009497989518195578915)
              ·
                refine ⟨25105514246984277293368373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16737009497989518195578915 25105514246984277293368373)
                ·
                  refine ⟨2353641960654775996253285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25105514246984277293368373 2353641960654775996253285)
                  ·
                    refine ⟨441307867622770499297491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353641960654775996253285 441307867622770499297491)
                    ·
                      rfl

theorem cell23_2578332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_2578332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578332 prefixEnd_2578332 := by exact prefixLift 2578332
  have htrace : WordTrace (prefixWord ++ tailWord_2578332) baseStart_2578332 baseEnd_2578332 := by
    simpa [prefixWord, tailWord_2578332, baseEnd_2578332] using wordTrace_append hprefix tailTrace_2578332
  have hstable : (prefixWord ++ tailWord_2578332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578332).length < 2 ^ (prefixWord ++ tailWord_2578332).sum := by decide
  have hdescent : baseEnd_2578332 < baseStart_2578332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578348 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2578348 : Nat := 118140960795 + 2578348 * 2 ^ 59
def prefixEnd_2578348 : Nat := 4983230072969 + 3 ^ 40 * 2578348 * 2
def baseEnd_2578348 : Nat := 1323931818558783435292399

theorem tailTrace_2578348 : CollatzResearch.WordTrace tailWord_2578348 prefixEnd_2578348 1323931818558783435292399 := by
  unfold tailWord_2578348
  simp only [CollatzResearch.WordTrace]
  refine ⟨47020038631546508812855849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62693384842062011750474465 47020038631546508812855849)
  ·
    refine ⟨35265028973659881609641887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47020038631546508812855849 35265028973659881609641887)
    ·
      refine ⟨52897543460489822414462831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35265028973659881609641887 52897543460489822414462831)
      ·
        refine ⟨79346315190734733621694247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52897543460489822414462831 79346315190734733621694247)
        ·
          refine ⟨119019472786102100432541371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79346315190734733621694247 119019472786102100432541371)
          ·
            refine ⟨178529209179153150648812057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119019472786102100432541371 178529209179153150648812057)
            ·
              refine ⟨133896906884364862986609043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178529209179153150648812057 133896906884364862986609043)
              ·
                refine ⟨200845360326547294479913565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133896906884364862986609043 200845360326547294479913565)
                ·
                  refine ⟨75317010122455235429967587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200845360326547294479913565 75317010122455235429967587)
                  ·
                    refine ⟨112975515183682853144951381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75317010122455235429967587 112975515183682853144951381)
                    ·
                      refine ⟨1323931818558783435292399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 112975515183682853144951381 1323931818558783435292399)
                      ·
                        rfl

theorem cell23_2578348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2578348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578348 prefixEnd_2578348 := by exact prefixLift 2578348
  have htrace : WordTrace (prefixWord ++ tailWord_2578348) baseStart_2578348 baseEnd_2578348 := by
    simpa [prefixWord, tailWord_2578348, baseEnd_2578348] using wordTrace_append hprefix tailTrace_2578348
  have hstable : (prefixWord ++ tailWord_2578348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578348).length < 2 ^ (prefixWord ++ tailWord_2578348).sum := by decide
  have hdescent : baseEnd_2578348 < baseStart_2578348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578365 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2578365 : Nat := 118140960795 + 2578365 * 2 ^ 59
def prefixEnd_2578365 : Nat := 4983230072969 + 3 ^ 40 * 2578365 * 2
def baseEnd_2578365 : Nat := 1323940547729909868779821

theorem tailTrace_2578365 : CollatzResearch.WordTrace tailWord_2578365 prefixEnd_2578365 1323940547729909868779821 := by
  unfold tailWord_2578365
  simp only [CollatzResearch.WordTrace]
  refine ⟨94040697304031429529080549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62693798202687619686053699 94040697304031429529080549)
  ·
    refine ⟨17632630744505893036702603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94040697304031429529080549 17632630744505893036702603)
    ·
      refine ⟨26448946116758839555053905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17632630744505893036702603 26448946116758839555053905)
      ·
        refine ⟨19836709587569129666290429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26448946116758839555053905 19836709587569129666290429)
        ·
          refine ⟨7438766095338423624858911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19836709587569129666290429 7438766095338423624858911)
          ·
            refine ⟨11158149143007635437288367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7438766095338423624858911 11158149143007635437288367)
            ·
              refine ⟨16737223714511453155932551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11158149143007635437288367 16737223714511453155932551)
              ·
                refine ⟨25105835571767179733898827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16737223714511453155932551 25105835571767179733898827)
                ·
                  refine ⟨37658753357650769600848241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25105835571767179733898827 37658753357650769600848241)
                  ·
                    refine ⟨28244065018238077200636181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37658753357650769600848241 28244065018238077200636181)
                    ·
                      refine ⟨1323940547729909868779821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28244065018238077200636181 1323940547729909868779821)
                      ·
                        rfl

theorem cell23_2578365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2578365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578365 prefixEnd_2578365 := by exact prefixLift 2578365
  have htrace : WordTrace (prefixWord ++ tailWord_2578365) baseStart_2578365 baseEnd_2578365 := by
    simpa [prefixWord, tailWord_2578365, baseEnd_2578365] using wordTrace_append hprefix tailTrace_2578365
  have hstable : (prefixWord ++ tailWord_2578365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578365).length < 2 ^ (prefixWord ++ tailWord_2578365).sum := by decide
  have hdescent : baseEnd_2578365 < baseStart_2578365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578382 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2]
def baseStart_2578382 : Nat := 118140960795 + 2578382 * 2 ^ 59
def prefixEnd_2578382 : Nat := 4983230072969 + 3 ^ 40 * 2578382 * 2
def baseEnd_2578382 : Nat := 1323949276901036302267243

theorem tailTrace_2578382 : CollatzResearch.WordTrace tailWord_2578382 prefixEnd_2578382 1323949276901036302267243 := by
  unfold tailWord_2578382
  simp only [CollatzResearch.WordTrace]
  refine ⟨11755164668121230179056175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62694211563313227621632933 11755164668121230179056175)
  ·
    refine ⟨17632747002181845268584263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11755164668121230179056175 17632747002181845268584263)
    ·
      refine ⟨26449120503272767902876395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17632747002181845268584263 26449120503272767902876395)
      ·
        refine ⟨39673680754909151854314593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26449120503272767902876395 39673680754909151854314593)
        ·
          refine ⟨29755260566181863890735945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39673680754909151854314593 29755260566181863890735945)
          ·
            refine ⟨22316445424636397918051959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29755260566181863890735945 22316445424636397918051959)
            ·
              refine ⟨33474668136954596877077939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22316445424636397918051959 33474668136954596877077939)
              ·
                refine ⟨50212002205431895315616909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33474668136954596877077939 50212002205431895315616909)
                ·
                  refine ⟨18829500827036960743356341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50212002205431895315616909 18829500827036960743356341)
                  ·
                    refine ⟨1765265702534715069689657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18829500827036960743356341 1765265702534715069689657)
                    ·
                      refine ⟨1323949276901036302267243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1765265702534715069689657 1323949276901036302267243)
                      ·
                        rfl

theorem cell23_2578382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_2578382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578382 prefixEnd_2578382 := by exact prefixLift 2578382
  have htrace : WordTrace (prefixWord ++ tailWord_2578382) baseStart_2578382 baseEnd_2578382 := by
    simpa [prefixWord, tailWord_2578382, baseEnd_2578382] using wordTrace_append hprefix tailTrace_2578382
  have hstable : (prefixWord ++ tailWord_2578382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578382).length < 2 ^ (prefixWord ++ tailWord_2578382).sum := by decide
  have hdescent : baseEnd_2578382 < baseStart_2578382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578389 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_2578389 : Nat := 118140960795 + 2578389 * 2 ^ 59
def prefixEnd_2578389 : Nat := 4983230072969 + 3 ^ 40 * 2578389 * 2
def baseEnd_2578389 : Nat := 1323952871265617774879711

theorem tailTrace_2578389 : CollatzResearch.WordTrace tailWord_2578389 prefixEnd_2578389 1323952871265617774879711 := by
  unfold tailWord_2578389
  simp only [CollatzResearch.WordTrace]
  refine ⟨94041572655944481627954221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62694381770629654418636147 94041572655944481627954221)
  ·
    refine ⟨35265589745979180610482833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94041572655944481627954221 35265589745979180610482833)
    ·
      refine ⟨26449192309484385457862125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35265589745979180610482833 26449192309484385457862125)
      ·
        refine ⟨9918447116056644546698297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26449192309484385457862125 9918447116056644546698297)
        ·
          refine ⟨7438835337042483410023723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9918447116056644546698297 7438835337042483410023723)
          ·
            refine ⟨11158253005563725115035585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7438835337042483410023723 11158253005563725115035585)
            ·
              refine ⟨8368689754172793836276689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11158253005563725115035585 8368689754172793836276689)
              ·
                refine ⟨6276517315629595377207517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8368689754172793836276689 6276517315629595377207517)
                ·
                  refine ⟨2353693993361098266452819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6276517315629595377207517 2353693993361098266452819)
                  ·
                    refine ⟨3530540990041647399679229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2353693993361098266452819 3530540990041647399679229)
                    ·
                      refine ⟨1323952871265617774879711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3530540990041647399679229 1323952871265617774879711)
                      ·
                        rfl

theorem cell23_2578389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_2578389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578389 prefixEnd_2578389 := by exact prefixLift 2578389
  have htrace : WordTrace (prefixWord ++ tailWord_2578389) baseStart_2578389 baseEnd_2578389 := by
    simpa [prefixWord, tailWord_2578389, baseEnd_2578389] using wordTrace_append hprefix tailTrace_2578389
  have hstable : (prefixWord ++ tailWord_2578389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578389).length < 2 ^ (prefixWord ++ tailWord_2578389).sum := by decide
  have hdescent : baseEnd_2578389 < baseStart_2578389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578392 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 1, 5]
def baseStart_2578392 : Nat := 118140960795 + 2578392 * 2 ^ 59
def prefixEnd_2578392 : Nat := 4983230072969 + 3 ^ 40 * 2578392 * 2
def baseEnd_2578392 : Nat := 441318137235860421047399

theorem tailTrace_2578392 : CollatzResearch.WordTrace tailWord_2578392 prefixEnd_2578392 441318137235860421047399 := by
  unfold tailWord_2578392
  simp only [CollatzResearch.WordTrace]
  refine ⟨47020841037466806570156715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62694454716622408760208953 47020841037466806570156715)
  ·
    refine ⟨70531261556200209855235073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47020841037466806570156715 70531261556200209855235073)
    ·
      refine ⟨52898446167150157391426305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70531261556200209855235073 52898446167150157391426305)
      ·
        refine ⟨39673834625362618043569729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52898446167150157391426305 39673834625362618043569729)
        ·
          refine ⟨29755375969021963532677297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39673834625362618043569729 29755375969021963532677297)
          ·
            refine ⟨22316531976766472649507973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29755375969021963532677297 22316531976766472649507973)
            ·
              refine ⟨4184349745643713621782745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22316531976766472649507973 4184349745643713621782745)
              ·
                refine ⟨3138262309232785216337059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4184349745643713621782745 3138262309232785216337059)
                ·
                  refine ⟨4707393463849177824505589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3138262309232785216337059 4707393463849177824505589)
                  ·
                    refine ⟨441318137235860421047399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4707393463849177824505589 441318137235860421047399)
                    ·
                      rfl

theorem cell23_2578392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_2578392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578392 prefixEnd_2578392 := by exact prefixLift 2578392
  have htrace : WordTrace (prefixWord ++ tailWord_2578392) baseStart_2578392 baseEnd_2578392 := by
    simpa [prefixWord, tailWord_2578392, baseEnd_2578392] using wordTrace_append hprefix tailTrace_2578392
  have hstable : (prefixWord ++ tailWord_2578392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578392).length < 2 ^ (prefixWord ++ tailWord_2578392).sum := by decide
  have hdescent : baseEnd_2578392 < baseStart_2578392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578425 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_2578425 : Nat := 118140960795 + 2578425 * 2 ^ 59
def prefixEnd_2578425 : Nat := 4983230072969 + 3 ^ 40 * 2578425 * 2
def baseEnd_2578425 : Nat := 1323971356569179634029545

theorem tailTrace_2578425 : CollatzResearch.WordTrace tailWord_2578425 prefixEnd_2578425 1323971356569179634029545 := by
  unfold tailWord_2578425
  simp only [CollatzResearch.WordTrace]
  refine ⟨94042885683814059776264729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62695257122542706517509819 94042885683814059776264729)
  ·
    refine ⟨70532164262860544832198547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94042885683814059776264729 70532164262860544832198547)
    ·
      refine ⟨105798246394290817248297821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70532164262860544832198547 105798246394290817248297821)
      ·
        refine ⟨39674342397859056468111683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105798246394290817248297821 39674342397859056468111683)
        ·
          refine ⟨59511513596788584702167525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39674342397859056468111683 59511513596788584702167525)
          ·
            refine ⟨11158408799397859631656411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59511513596788584702167525 11158408799397859631656411)
            ·
              refine ⟨16737613199096789447484617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11158408799397859631656411 16737613199096789447484617)
              ·
                refine ⟨12553209899322592085613463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16737613199096789447484617 12553209899322592085613463)
                ·
                  refine ⟨18829814848983888128420195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12553209899322592085613463 18829814848983888128420195)
                  ·
                    refine ⟨28244722273475832192630293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18829814848983888128420195 28244722273475832192630293)
                    ·
                      refine ⟨1323971356569179634029545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28244722273475832192630293 1323971356569179634029545)
                      ·
                        rfl

theorem cell23_2578425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_2578425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578425 prefixEnd_2578425 := by exact prefixLift 2578425
  have htrace : WordTrace (prefixWord ++ tailWord_2578425) baseStart_2578425 baseEnd_2578425 := by
    simpa [prefixWord, tailWord_2578425, baseEnd_2578425] using wordTrace_append hprefix tailTrace_2578425
  have hstable : (prefixWord ++ tailWord_2578425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578425).length < 2 ^ (prefixWord ++ tailWord_2578425).sum := by decide
  have hdescent : baseEnd_2578425 < baseStart_2578425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578439 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 2, 4]
def baseStart_2578439 : Nat := 118140960795 + 2578439 * 2 ^ 59
def prefixEnd_2578439 : Nat := 4983230072969 + 3 ^ 40 * 2578439 * 2
def baseEnd_2578439 : Nat := 441326181766114193084827

theorem tailTrace_2578439 : CollatzResearch.WordTrace tailWord_2578439 prefixEnd_2578439 441326181766114193084827 := by
  unfold tailWord_2578439
  simp only [CollatzResearch.WordTrace]
  refine ⟨94043396305763340167274371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62695597537175560111516247 94043396305763340167274371)
  ·
    refine ⟨141065094458645010250911557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94043396305763340167274371 141065094458645010250911557)
    ·
      refine ⟨26449705210995939422045917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141065094458645010250911557 26449705210995939422045917)
      ·
        refine ⟨9918639454123477283267219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26449705210995939422045917 9918639454123477283267219)
        ·
          refine ⟨14877959181185215924900829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9918639454123477283267219 14877959181185215924900829)
          ·
            refine ⟨5579234692944455971837811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14877959181185215924900829 5579234692944455971837811)
            ·
              refine ⟨8368852039416683957756717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5579234692944455971837811 8368852039416683957756717)
              ·
                refine ⟨3138319514781256484158769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8368852039416683957756717 3138319514781256484158769)
                ·
                  refine ⟨2353739636085942363119077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138319514781256484158769 2353739636085942363119077)
                  ·
                    refine ⟨441326181766114193084827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353739636085942363119077 441326181766114193084827)
                    ·
                      rfl

theorem cell23_2578439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_2578439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578439 prefixEnd_2578439 := by exact prefixLift 2578439
  have htrace : WordTrace (prefixWord ++ tailWord_2578439) baseStart_2578439 baseEnd_2578439 := by
    simpa [prefixWord, tailWord_2578439, baseEnd_2578439] using wordTrace_append hprefix tailTrace_2578439
  have hstable : (prefixWord ++ tailWord_2578439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578439).length < 2 ^ (prefixWord ++ tailWord_2578439).sum := by decide
  have hdescent : baseEnd_2578439 < baseStart_2578439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578466 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_2578466 : Nat := 118140960795 + 2578466 * 2 ^ 59
def prefixEnd_2578466 : Nat := 4983230072969 + 3 ^ 40 * 2578466 * 2
def baseEnd_2578466 : Nat := 1323992409276013973616857

theorem tailTrace_2578466 : CollatzResearch.WordTrace tailWord_2578466 prefixEnd_2578466 1323992409276013973616857 := by
  unfold tailWord_2578466
  simp only [CollatzResearch.WordTrace]
  refine ⟨23511095269166380944626813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62696254051110349185671501 23511095269166380944626813)
  ·
    refine ⟨8816660725937392854235055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23511095269166380944626813 8816660725937392854235055)
    ·
      refine ⟨13224991088906089281352583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8816660725937392854235055 13224991088906089281352583)
      ·
        refine ⟨19837486633359133922028875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13224991088906089281352583 19837486633359133922028875)
        ·
          refine ⟨29756229950038700883043313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19837486633359133922028875 29756229950038700883043313)
          ·
            refine ⟨22317172462529025662282485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29756229950038700883043313 22317172462529025662282485)
            ·
              refine ⟨2092234918362096155838983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22317172462529025662282485 2092234918362096155838983)
              ·
                refine ⟨3138352377543144233758475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092234918362096155838983 3138352377543144233758475)
                ·
                  refine ⟨4707528566314716350637713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3138352377543144233758475 4707528566314716350637713)
                  ·
                    refine ⟨3530646424736037262978285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4707528566314716350637713 3530646424736037262978285)
                    ·
                      refine ⟨1323992409276013973616857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3530646424736037262978285 1323992409276013973616857)
                      ·
                        rfl

theorem cell23_2578466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_2578466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578466 prefixEnd_2578466 := by exact prefixLift 2578466
  have htrace : WordTrace (prefixWord ++ tailWord_2578466) baseStart_2578466 baseEnd_2578466 := by
    simpa [prefixWord, tailWord_2578466, baseEnd_2578466] using wordTrace_append hprefix tailTrace_2578466
  have hstable : (prefixWord ++ tailWord_2578466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578466).length < 2 ^ (prefixWord ++ tailWord_2578466).sum := by decide
  have hdescent : baseEnd_2578466 < baseStart_2578466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578480 : List Nat := [2, 1, 1, 1, 2, 7, 2, 2, 1, 2, 2]
def baseStart_2578480 : Nat := 118140960795 + 2578480 * 2 ^ 59
def prefixEnd_2578480 : Nat := 4983230072969 + 3 ^ 40 * 2578480 * 2
def baseEnd_2578480 : Nat := 1323999598005176918841793

theorem tailTrace_2578480 : CollatzResearch.WordTrace tailWord_2578480 prefixEnd_2578480 1323999598005176918841793 := by
  unfold tailWord_2578480
  simp only [CollatzResearch.WordTrace]
  refine ⟨47022445849307402084758447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62696594465743202779677929 47022445849307402084758447)
  ·
    refine ⟨70533668773961103127137671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47022445849307402084758447 70533668773961103127137671)
    ·
      refine ⟨105800503160941654690706507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70533668773961103127137671 105800503160941654690706507)
      ·
        refine ⟨158700754741412482036059761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105800503160941654690706507 158700754741412482036059761)
        ·
          refine ⟨119025566056059361527044821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158700754741412482036059761 119025566056059361527044821)
          ·
            refine ⟨2789661704438891285790113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 119025566056059361527044821 2789661704438891285790113)
            ·
              refine ⟨2092246278329168464342585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2789661704438891285790113 2092246278329168464342585)
              ·
                refine ⟨1569184708746876348256939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092246278329168464342585 1569184708746876348256939)
                ·
                  refine ⟨2353777063120314522385409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569184708746876348256939 2353777063120314522385409)
                  ·
                    refine ⟨1765332797340235891789057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2353777063120314522385409 1765332797340235891789057)
                    ·
                      refine ⟨1323999598005176918841793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1765332797340235891789057 1323999598005176918841793)
                      ·
                        rfl

theorem cell23_2578480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 1, 2, 2].length) (baseStart_2578480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578480 prefixEnd_2578480 := by exact prefixLift 2578480
  have htrace : WordTrace (prefixWord ++ tailWord_2578480) baseStart_2578480 baseEnd_2578480 := by
    simpa [prefixWord, tailWord_2578480, baseEnd_2578480] using wordTrace_append hprefix tailTrace_2578480
  have hstable : (prefixWord ++ tailWord_2578480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578480).length < 2 ^ (prefixWord ++ tailWord_2578480).sum := by decide
  have hdescent : baseEnd_2578480 < baseStart_2578480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578495 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 1, 8]
def baseStart_2578495 : Nat := 118140960795 + 2578495 * 2 ^ 59
def prefixEnd_2578495 : Nat := 4983230072969 + 3 ^ 40 * 2578495 * 2
def baseEnd_2578495 : Nat := 441335766738331453384741

theorem tailTrace_2578495 : CollatzResearch.WordTrace tailWord_2578495 prefixEnd_2578495 441335766738331453384741 := by
  unfold tailWord_2578495
  simp only [CollatzResearch.WordTrace]
  refine ⟨94045438793560461731312939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62696959195706974487541959 94045438793560461731312939)
  ·
    refine ⟨141068158190340692596969409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94045438793560461731312939 141068158190340692596969409)
    ·
      refine ⟨105801118642755519447727057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141068158190340692596969409 105801118642755519447727057)
      ·
        refine ⟨79350838982066639585795293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105801118642755519447727057 79350838982066639585795293)
        ·
          refine ⟨29756564618274989844673235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79350838982066639585795293 29756564618274989844673235)
          ·
            refine ⟨44634846927412484767009853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29756564618274989844673235 44634846927412484767009853)
            ·
              refine ⟨16738067597779681787628695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44634846927412484767009853 16738067597779681787628695)
              ·
                refine ⟨25107101396669522681443043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16738067597779681787628695 25107101396669522681443043)
                ·
                  refine ⟨37660652095004284022164565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25107101396669522681443043 37660652095004284022164565)
                  ·
                    refine ⟨441335766738331453384741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37660652095004284022164565 441335766738331453384741)
                    ·
                      rfl

theorem cell23_2578495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_2578495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578495 prefixEnd_2578495 := by exact prefixLift 2578495
  have htrace : WordTrace (prefixWord ++ tailWord_2578495) baseStart_2578495 baseEnd_2578495 := by
    simpa [prefixWord, tailWord_2578495, baseEnd_2578495] using wordTrace_append hprefix tailTrace_2578495
  have hstable : (prefixWord ++ tailWord_2578495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578495).length < 2 ^ (prefixWord ++ tailWord_2578495).sum := by decide
  have hdescent : baseEnd_2578495 < baseStart_2578495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578519 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 1, 4, 2]
def baseStart_2578519 : Nat := 118140960795 + 2578519 * 2 ^ 59
def prefixEnd_2578519 : Nat := 4983230072969 + 3 ^ 40 * 2578519 * 2
def baseEnd_2578519 : Nat := 1324019623750702266254113

theorem tailTrace_2578519 : CollatzResearch.WordTrace tailWord_2578519 prefixEnd_2578519 1324019623750702266254113 := by
  unfold tailWord_2578519
  simp only [CollatzResearch.WordTrace]
  refine ⟨94046314145473513830186611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62697542763649009220124407 94046314145473513830186611)
  ·
    refine ⟨141069471218210270745279917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94046314145473513830186611 141069471218210270745279917)
    ·
      refine ⟨52901051706828851529479969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141069471218210270745279917 52901051706828851529479969)
      ·
        refine ⟨39675788780121638647109977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52901051706828851529479969 39675788780121638647109977)
        ·
          refine ⟨29756841585091228985332483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39675788780121638647109977 29756841585091228985332483)
          ·
            refine ⟨44635262377636843477998725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29756841585091228985332483 44635262377636843477998725)
            ·
              refine ⟨8369111695806908152124761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44635262377636843477998725 8369111695806908152124761)
              ·
                refine ⟨6276833771855181114093571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8369111695806908152124761 6276833771855181114093571)
                ·
                  refine ⟨9415250657782771671140357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6276833771855181114093571 9415250657782771671140357)
                  ·
                    refine ⟨1765359498334269688338817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9415250657782771671140357 1765359498334269688338817)
                    ·
                      refine ⟨1324019623750702266254113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1765359498334269688338817 1324019623750702266254113)
                      ·
                        rfl

theorem cell23_2578519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_2578519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578519 prefixEnd_2578519 := by exact prefixLift 2578519
  have htrace : WordTrace (prefixWord ++ tailWord_2578519) baseStart_2578519 baseEnd_2578519 := by
    simpa [prefixWord, tailWord_2578519, baseEnd_2578519] using wordTrace_append hprefix tailTrace_2578519
  have hstable : (prefixWord ++ tailWord_2578519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578519).length < 2 ^ (prefixWord ++ tailWord_2578519).sum := by decide
  have hdescent : baseEnd_2578519 < baseStart_2578519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578530 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2578530 : Nat := 118140960795 + 2578530 * 2 ^ 59
def prefixEnd_2578530 : Nat := 4983230072969 + 3 ^ 40 * 2578530 * 2
def baseEnd_2578530 : Nat := 1324025272037901723216563

theorem tailTrace_2578530 : CollatzResearch.WordTrace tailWord_2578530 prefixEnd_2578530 1324025272037901723216563 := by
  unfold tailWord_2578530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23511678837108415677209261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62697810232289108472558029 23511678837108415677209261)
  ·
    refine ⟨8816879563915655878953473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23511678837108415677209261 8816879563915655878953473)
    ·
      refine ⟨6612659672936741909215105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8816879563915655878953473 6612659672936741909215105)
      ·
        refine ⟨4959494754702556431911329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6612659672936741909215105 4959494754702556431911329)
        ·
          refine ⟨3719621066026917323933497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959494754702556431911329 3719621066026917323933497)
          ·
            refine ⟨2789715799520187992950123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3719621066026917323933497 2789715799520187992950123)
            ·
              refine ⟨4184573699280281989425185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789715799520187992950123 4184573699280281989425185)
              ·
                refine ⟨3138430274460211492068889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4184573699280281989425185 3138430274460211492068889)
                ·
                  refine ⟨2353822705845158619051667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138430274460211492068889 2353822705845158619051667)
                  ·
                    refine ⟨3530734058767737928577501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2353822705845158619051667 3530734058767737928577501)
                    ·
                      refine ⟨1324025272037901723216563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3530734058767737928577501 1324025272037901723216563)
                      ·
                        rfl

theorem cell23_2578530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2578530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578530 prefixEnd_2578530 := by exact prefixLift 2578530
  have htrace : WordTrace (prefixWord ++ tailWord_2578530) baseStart_2578530 baseEnd_2578530 := by
    simpa [prefixWord, tailWord_2578530, baseEnd_2578530] using wordTrace_append hprefix tailTrace_2578530
  have hstable : (prefixWord ++ tailWord_2578530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578530).length < 2 ^ (prefixWord ++ tailWord_2578530).sum := by decide
  have hdescent : baseEnd_2578530 < baseStart_2578530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578532 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_2578532 : Nat := 118140960795 + 2578532 * 2 ^ 59
def prefixEnd_2578532 : Nat := 4983230072969 + 3 ^ 40 * 2578532 * 2
def baseEnd_2578532 : Nat := 1324026298999210715391553

theorem tailTrace_2578532 : CollatzResearch.WordTrace tailWord_2578532 prefixEnd_2578532 1324026298999210715391553 := by
  unfold tailWord_2578532
  simp only [CollatzResearch.WordTrace]
  refine ⟨47023394147213208525204925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62697858862950944700273233 47023394147213208525204925)
  ·
    refine ⟨17633772805204953196951847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47023394147213208525204925 17633772805204953196951847)
    ·
      refine ⟨26450659207807429795427771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17633772805204953196951847 26450659207807429795427771)
      ·
        refine ⟨39675988811711144693141657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26450659207807429795427771 39675988811711144693141657)
        ·
          refine ⟨29756991608783358519856243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39675988811711144693141657 29756991608783358519856243)
          ·
            refine ⟨44635487413175037779784365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29756991608783358519856243 44635487413175037779784365)
            ·
              refine ⟨16738307779940639167419137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44635487413175037779784365 16738307779940639167419137)
              ·
                refine ⟨12553730834955479375564353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16738307779940639167419137 12553730834955479375564353)
                ·
                  refine ⟨9415298126216609531673265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12553730834955479375564353 9415298126216609531673265)
                  ·
                    refine ⟨7061473594662457148754949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9415298126216609531673265 7061473594662457148754949)
                    ·
                      refine ⟨1324026298999210715391553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7061473594662457148754949 1324026298999210715391553)
                      ·
                        rfl

theorem cell23_2578532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_2578532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578532 prefixEnd_2578532 := by exact prefixLift 2578532
  have htrace : WordTrace (prefixWord ++ tailWord_2578532) baseStart_2578532 baseEnd_2578532 := by
    simpa [prefixWord, tailWord_2578532, baseEnd_2578532] using wordTrace_append hprefix tailTrace_2578532
  have hstable : (prefixWord ++ tailWord_2578532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578532).length < 2 ^ (prefixWord ++ tailWord_2578532).sum := by decide
  have hdescent : baseEnd_2578532 < baseStart_2578532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578589 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2578589 : Nat := 118140960795 + 2578589 * 2 ^ 59
def prefixEnd_2578589 : Nat := 4983230072969 + 3 ^ 40 * 2578589 * 2
def baseEnd_2578589 : Nat := 441351855798838997459597

theorem tailTrace_2578589 : CollatzResearch.WordTrace tailWord_2578589 prefixEnd_2578589 441351855798838997459597 := by
  unfold tailWord_2578589
  simp only [CollatzResearch.WordTrace]
  refine ⟨94048867255219915785234821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62699244836813277190156547 94048867255219915785234821)
  ·
    refine ⟨17634162610353734209731529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94048867255219915785234821 17634162610353734209731529)
    ·
      refine ⟨13225621957765300657298647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17634162610353734209731529 13225621957765300657298647)
      ·
        refine ⟨19838432936647950985947971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13225621957765300657298647 19838432936647950985947971)
        ·
          refine ⟨29757649404971926478921957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19838432936647950985947971 29757649404971926478921957)
          ·
            refine ⟨5579559263432236214797867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29757649404971926478921957 5579559263432236214797867)
            ·
              refine ⟨8369338895148354322196801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5579559263432236214797867 8369338895148354322196801)
              ·
                refine ⟨6277004171361265741647601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8369338895148354322196801 6277004171361265741647601)
                ·
                  refine ⟨4707753128520949306235701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6277004171361265741647601 4707753128520949306235701)
                  ·
                    refine ⟨441351855798838997459597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4707753128520949306235701 441351855798838997459597)
                    ·
                      rfl

theorem cell23_2578589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2578589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578589 prefixEnd_2578589 := by exact prefixLift 2578589
  have htrace : WordTrace (prefixWord ++ tailWord_2578589) baseStart_2578589 baseEnd_2578589 := by
    simpa [prefixWord, tailWord_2578589, baseEnd_2578589] using wordTrace_append hprefix tailTrace_2578589
  have hstable : (prefixWord ++ tailWord_2578589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578589).length < 2 ^ (prefixWord ++ tailWord_2578589).sum := by decide
  have hdescent : baseEnd_2578589 < baseStart_2578589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578629 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 2, 2, 3]
def baseStart_2578629 : Nat := 118140960795 + 2578629 * 2 ^ 59
def prefixEnd_2578629 : Nat := 4983230072969 + 3 ^ 40 * 2578629 * 2
def baseEnd_2578629 : Nat := 1324076106622696835878607

theorem tailTrace_2578629 : CollatzResearch.WordTrace tailWord_2578629 prefixEnd_2578629 1324076106622696835878607 := by
  unfold tailWord_2578629
  simp only [CollatzResearch.WordTrace]
  refine ⟨94050326175075002616690941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62700217450050001744460627 94050326175075002616690941)
  ·
    refine ⟨35268872315653125981259103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94050326175075002616690941 35268872315653125981259103)
    ·
      refine ⟨52903308473479688971888655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35268872315653125981259103 52903308473479688971888655)
      ·
        refine ⟨79354962710219533457832983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52903308473479688971888655 79354962710219533457832983)
        ·
          refine ⟨119032444065329300186749475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79354962710219533457832983 119032444065329300186749475)
          ·
            refine ⟨178548666097993950280124213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119032444065329300186749475 178548666097993950280124213)
            ·
              refine ⟨16738937446686932838761645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178548666097993950280124213 16738937446686932838761645)
              ·
                refine ⟨6277101542507599814535617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16738937446686932838761645 6277101542507599814535617)
                ·
                  refine ⟨4707826156880699860901713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6277101542507599814535617 4707826156880699860901713)
                  ·
                    refine ⟨3530869617660524895676285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4707826156880699860901713 3530869617660524895676285)
                    ·
                      refine ⟨1324076106622696835878607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3530869617660524895676285 1324076106622696835878607)
                      ·
                        rfl

theorem cell23_2578629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_2578629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578629 prefixEnd_2578629 := by exact prefixLift 2578629
  have htrace : WordTrace (prefixWord ++ tailWord_2578629) baseStart_2578629 baseEnd_2578629 := by
    simpa [prefixWord, tailWord_2578629, baseEnd_2578629] using wordTrace_append hprefix tailTrace_2578629
  have hstable : (prefixWord ++ tailWord_2578629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578629).length < 2 ^ (prefixWord ++ tailWord_2578629).sum := by decide
  have hdescent : baseEnd_2578629 < baseStart_2578629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578696 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 1, 5]
def baseStart_2578696 : Nat := 118140960795 + 2578696 * 2 ^ 59
def prefixEnd_2578696 : Nat := 4983230072969 + 3 ^ 40 * 2578696 * 2
def baseEnd_2578696 : Nat := 441370169942182691246933

theorem tailTrace_2578696 : CollatzResearch.WordTrace tailWord_2578696 prefixEnd_2578696 441370169942182691246933 := by
  unfold tailWord_2578696
  simp only [CollatzResearch.WordTrace]
  refine ⟨47026384932916136529689971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62701846577221515372919961 47026384932916136529689971)
  ·
    refine ⟨70539577399374204794534957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47026384932916136529689971 70539577399374204794534957)
    ·
      refine ⟨26452341524765326797950609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70539577399374204794534957 26452341524765326797950609)
      ·
        refine ⟨19839256143573995098462957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26452341524765326797950609 19839256143573995098462957)
        ·
          refine ⟨7439721053840248161923609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19839256143573995098462957 7439721053840248161923609)
          ·
            refine ⟨5579790790380186121442707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7439721053840248161923609 5579790790380186121442707)
            ·
              refine ⟨8369686185570279182164061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5579790790380186121442707 8369686185570279182164061)
              ·
                refine ⟨3138632319588854693311523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8369686185570279182164061 3138632319588854693311523)
                ·
                  refine ⟨4707948479383282039967285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3138632319588854693311523 4707948479383282039967285)
                  ·
                    refine ⟨441370169942182691246933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4707948479383282039967285 441370169942182691246933)
                    ·
                      rfl

theorem cell23_2578696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_2578696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578696 prefixEnd_2578696 := by exact prefixLift 2578696
  have htrace : WordTrace (prefixWord ++ tailWord_2578696) baseStart_2578696 baseEnd_2578696 := by
    simpa [prefixWord, tailWord_2578696, baseEnd_2578696] using wordTrace_append hprefix tailTrace_2578696
  have hstable : (prefixWord ++ tailWord_2578696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578696).length < 2 ^ (prefixWord ++ tailWord_2578696).sum := by decide
  have hdescent : baseEnd_2578696 < baseStart_2578696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578719 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_2578719 : Nat := 118140960795 + 2578719 * 2 ^ 59
def prefixEnd_2578719 : Nat := 4983230072969 + 3 ^ 40 * 2578719 * 2
def baseEnd_2578719 : Nat := 1324122319881601483753193

theorem tailTrace_2578719 : CollatzResearch.WordTrace tailWord_2578719 prefixEnd_2578719 1324122319881601483753193 := by
  unfold tailWord_2578719
  simp only [CollatzResearch.WordTrace]
  refine ⟨94053608744748947987467211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62702405829832631991644807 94053608744748947987467211)
  ·
    refine ⟨141080413117123421981200817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94053608744748947987467211 141080413117123421981200817)
    ·
      refine ⟨105810309837842566485900613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141080413117123421981200817 105810309837842566485900613)
      ·
        refine ⟨19839433094595481216106365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105810309837842566485900613 19839433094595481216106365)
        ·
          refine ⟨7439787410473305456039887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19839433094595481216106365 7439787410473305456039887)
          ·
            refine ⟨11159681115709958184059831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7439787410473305456039887 11159681115709958184059831)
            ·
              refine ⟨16739521673564937276089747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11159681115709958184059831 16739521673564937276089747)
              ·
                refine ⟨25109282510347405914134621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16739521673564937276089747 25109282510347405914134621)
                ·
                  refine ⟨9415980941380277217800483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25109282510347405914134621 9415980941380277217800483)
                  ·
                    refine ⟨14123971412070415826700725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9415980941380277217800483 14123971412070415826700725)
                    ·
                      refine ⟨1324122319881601483753193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14123971412070415826700725 1324122319881601483753193)
                      ·
                        rfl

theorem cell23_2578719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_2578719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578719 prefixEnd_2578719 := by exact prefixLift 2578719
  have htrace : WordTrace (prefixWord ++ tailWord_2578719) baseStart_2578719 baseEnd_2578719 := by
    simpa [prefixWord, tailWord_2578719, baseEnd_2578719] using wordTrace_append hprefix tailTrace_2578719
  have hstable : (prefixWord ++ tailWord_2578719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578719).length < 2 ^ (prefixWord ++ tailWord_2578719).sum := by decide
  have hdescent : baseEnd_2578719 < baseStart_2578719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578753 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2578753 : Nat := 118140960795 + 2578753 * 2 ^ 59
def prefixEnd_2578753 : Nat := 4983230072969 + 3 ^ 40 * 2578753 * 2
def baseEnd_2578753 : Nat := 1324139778223854350728037

theorem tailTrace_2578753 : CollatzResearch.WordTrace tailWord_2578753 prefixEnd_2578753 1324139778223854350728037 := by
  unfold tailWord_2578753
  simp only [CollatzResearch.WordTrace]
  refine ⟨94054848826625771794204913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62703232551083847862803275 94054848826625771794204913)
  ·
    refine ⟨70541136619969328845653685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94054848826625771794204913 70541136619969328845653685)
    ·
      refine ⟨6613231558122124579280033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70541136619969328845653685 6613231558122124579280033)
      ·
        refine ⟨4959923668591593434460025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6613231558122124579280033 4959923668591593434460025)
        ·
          refine ⟨3719942751443695075845019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959923668591593434460025 3719942751443695075845019)
          ·
            refine ⟨5579914127165542613767529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719942751443695075845019 5579914127165542613767529)
            ·
              refine ⟨4184935595374156960325647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5579914127165542613767529 4184935595374156960325647)
              ·
                refine ⟨6277403393061235440488471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4184935595374156960325647 6277403393061235440488471)
                ·
                  refine ⟨9416105089591853160732707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6277403393061235440488471 9416105089591853160732707)
                  ·
                    refine ⟨14124157634387779741099061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9416105089591853160732707 14124157634387779741099061)
                    ·
                      refine ⟨1324139778223854350728037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14124157634387779741099061 1324139778223854350728037)
                      ·
                        rfl

theorem cell23_2578753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2578753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578753 prefixEnd_2578753 := by exact prefixLift 2578753
  have htrace : WordTrace (prefixWord ++ tailWord_2578753) baseStart_2578753 baseEnd_2578753 := by
    simpa [prefixWord, tailWord_2578753, baseEnd_2578753] using wordTrace_append hprefix tailTrace_2578753
  have hstable : (prefixWord ++ tailWord_2578753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578753).length < 2 ^ (prefixWord ++ tailWord_2578753).sum := by decide
  have hdescent : baseEnd_2578753 < baseStart_2578753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578818 : List Nat := [3, 4, 2, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_2578818 : Nat := 118140960795 + 2578818 * 2 ^ 59
def prefixEnd_2578818 : Nat := 4983230072969 + 3 ^ 40 * 2578818 * 2
def baseEnd_2578818 : Nat := 1324173154466396596415239

theorem tailTrace_2578818 : CollatzResearch.WordTrace tailWord_2578818 prefixEnd_2578818 1324173154466396596415239 := by
  unfold tailWord_2578818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23514304892847571973830277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62704813047593525263547405 23514304892847571973830277)
  ·
    refine ⟨4408932167408919745093177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23514304892847571973830277 4408932167408919745093177)
    ·
      refine ⟨3306699125556689808819883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4408932167408919745093177 3306699125556689808819883)
      ·
        refine ⟨4960048688335034713229825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306699125556689808819883 4960048688335034713229825)
        ·
          refine ⟨3720036516251276034922369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4960048688335034713229825 3720036516251276034922369)
          ·
            refine ⟨2790027387188457026191777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3720036516251276034922369 2790027387188457026191777)
            ·
              refine ⟨2092520540391342769643833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2790027387188457026191777 2092520540391342769643833)
              ·
                refine ⟨1569390405293507077232875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092520540391342769643833 1569390405293507077232875)
                ·
                  refine ⟨2354085607940260615849313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569390405293507077232875 2354085607940260615849313)
                  ·
                    refine ⟨1765564205955195461886985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2354085607940260615849313 1765564205955195461886985)
                    ·
                      refine ⟨1324173154466396596415239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1765564205955195461886985 1324173154466396596415239)
                      ·
                        rfl

theorem cell23_2578818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_2578818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578818 prefixEnd_2578818 := by exact prefixLift 2578818
  have htrace : WordTrace (prefixWord ++ tailWord_2578818) baseStart_2578818 baseEnd_2578818 := by
    simpa [prefixWord, tailWord_2578818, baseEnd_2578818] using wordTrace_append hprefix tailTrace_2578818
  have hstable : (prefixWord ++ tailWord_2578818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578818).length < 2 ^ (prefixWord ++ tailWord_2578818).sum := by decide
  have hdescent : baseEnd_2578818 < baseStart_2578818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578840 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 1, 4, 2]
def baseStart_2578840 : Nat := 118140960795 + 2578840 * 2 ^ 59
def prefixEnd_2578840 : Nat := 4983230072969 + 3 ^ 40 * 2578840 * 2
def baseEnd_2578840 : Nat := 1324184451040795510340137

theorem tailTrace_2578840 : CollatzResearch.WordTrace tailWord_2578840 prefixEnd_2578840 1324184451040795510340137 := by
  unfold tailWord_2578840
  simp only [CollatzResearch.WordTrace]
  refine ⟨47029010988655292826310987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62705347984873723768414649 47029010988655292826310987)
  ·
    refine ⟨70543516482982939239466481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47029010988655292826310987 70543516482982939239466481)
    ·
      refine ⟨52907637362237204429599861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70543516482982939239466481 52907637362237204429599861)
      ·
        refine ⟨4960091002709737915274987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52907637362237204429599861 4960091002709737915274987)
        ·
          refine ⟨7440136504064606872912481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4960091002709737915274987 7440136504064606872912481)
          ·
            refine ⟨5580102378048455154684361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7440136504064606872912481 5580102378048455154684361)
            ·
              refine ⟨4185076783536341366013271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5580102378048455154684361 4185076783536341366013271)
              ·
                refine ⟨6277615175304512049019907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185076783536341366013271 6277615175304512049019907)
                ·
                  refine ⟨9416422762956768073529861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6277615175304512049019907 9416422762956768073529861)
                  ·
                    refine ⟨1765579268054394013786849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9416422762956768073529861 1765579268054394013786849)
                    ·
                      refine ⟨1324184451040795510340137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1765579268054394013786849 1324184451040795510340137)
                      ·
                        rfl

theorem cell23_2578840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_2578840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578840 prefixEnd_2578840 := by exact prefixLift 2578840
  have htrace : WordTrace (prefixWord ++ tailWord_2578840) baseStart_2578840 baseEnd_2578840 := by
    simpa [prefixWord, tailWord_2578840, baseEnd_2578840] using wordTrace_append hprefix tailTrace_2578840
  have hstable : (prefixWord ++ tailWord_2578840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578840).length < 2 ^ (prefixWord ++ tailWord_2578840).sum := by decide
  have hdescent : baseEnd_2578840 < baseStart_2578840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578861 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_2578861 : Nat := 118140960795 + 2578861 * 2 ^ 59
def prefixEnd_2578861 : Nat := 4983230072969 + 3 ^ 40 * 2578861 * 2
def baseEnd_2578861 : Nat := 1324195234134539928177541

theorem tailTrace_2578861 : CollatzResearch.WordTrace tailWord_2578861 prefixEnd_2578861 1324195234134539928177541 := by
  unfold tailWord_2578861
  simp only [CollatzResearch.WordTrace]
  refine ⟨94058787910234506239136437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62705858606823004159424291 94058787910234506239136437)
  ·
    refine ⟨8818011366584484959919041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94058787910234506239136437 8818011366584484959919041)
    ·
      refine ⟨6613508524938363719939281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8818011366584484959919041 6613508524938363719939281)
      ·
        refine ⟨4960131393703772789954461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6613508524938363719939281 4960131393703772789954461)
        ·
          refine ⟨1860049272638914796232923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4960131393703772789954461 1860049272638914796232923)
          ·
            refine ⟨2790073908958372194349385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860049272638914796232923 2790073908958372194349385)
            ·
              refine ⟨2092555431718779145762039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2790073908958372194349385 2092555431718779145762039)
              ·
                refine ⟨3138833147578168718643059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092555431718779145762039 3138833147578168718643059)
                ·
                  refine ⟨4708249721367253077964589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3138833147578168718643059 4708249721367253077964589)
                  ·
                    refine ⟨1765593645512719904236721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4708249721367253077964589 1765593645512719904236721)
                    ·
                      refine ⟨1324195234134539928177541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1765593645512719904236721 1324195234134539928177541)
                      ·
                        rfl

theorem cell23_2578861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_2578861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578861 prefixEnd_2578861 := by exact prefixLift 2578861
  have htrace : WordTrace (prefixWord ++ tailWord_2578861) baseStart_2578861 baseEnd_2578861 := by
    simpa [prefixWord, tailWord_2578861, baseEnd_2578861] using wordTrace_append hprefix tailTrace_2578861
  have hstable : (prefixWord ++ tailWord_2578861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578861).length < 2 ^ (prefixWord ++ tailWord_2578861).sum := by decide
  have hdescent : baseEnd_2578861 < baseStart_2578861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578899 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 5]
def baseStart_2578899 : Nat := 118140960795 + 2578899 * 2 ^ 59
def prefixEnd_2578899 : Nat := 4983230072969 + 3 ^ 40 * 2578899 * 2
def baseEnd_2578899 : Nat := 1324214746399410779502365

theorem tailTrace_2578899 : CollatzResearch.WordTrace tailWord_2578899 prefixEnd_2578899 1324214746399410779502365 := by
  unfold tailWord_2578899
  simp only [CollatzResearch.WordTrace]
  refine ⟨94060173884096838729019751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62706782589397892486013167 94060173884096838729019751)
  ·
    refine ⟨141090260826145258093529627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94060173884096838729019751 141090260826145258093529627)
    ·
      refine ⟨211635391239217887140294441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141090260826145258093529627 211635391239217887140294441)
      ·
        refine ⟨158726543429413415355220831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211635391239217887140294441 158726543429413415355220831)
        ·
          refine ⟨238089815144120123032831247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158726543429413415355220831 238089815144120123032831247)
          ·
            refine ⟨357134722716180184549246871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238089815144120123032831247 357134722716180184549246871)
            ·
              refine ⟨535702084074270276823870307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357134722716180184549246871 535702084074270276823870307)
              ·
                refine ⟨803553126111405415235805461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535702084074270276823870307 803553126111405415235805461)
                ·
                  refine ⟨37666552786472128839178381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 803553126111405415235805461 37666552786472128839178381)
                  ·
                    refine ⟨14124957294927048314691893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37666552786472128839178381 14124957294927048314691893)
                    ·
                      refine ⟨1324214746399410779502365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14124957294927048314691893 1324214746399410779502365)
                      ·
                        rfl

theorem cell23_2578899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_2578899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578899 prefixEnd_2578899 := by exact prefixLift 2578899
  have htrace : WordTrace (prefixWord ++ tailWord_2578899) baseStart_2578899 baseEnd_2578899 := by
    simpa [prefixWord, tailWord_2578899, baseEnd_2578899] using wordTrace_append hprefix tailTrace_2578899
  have hstable : (prefixWord ++ tailWord_2578899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578899).length < 2 ^ (prefixWord ++ tailWord_2578899).sum := by decide
  have hdescent : baseEnd_2578899 < baseStart_2578899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578914 : List Nat := [3, 3, 3, 2, 1, 2, 1, 3, 5]
def baseStart_2578914 : Nat := 118140960795 + 2578914 * 2 ^ 59
def prefixEnd_2578914 : Nat := 4983230072969 + 3 ^ 40 * 2578914 * 2
def baseEnd_2578914 : Nat := 147135827623247580090533

theorem tailTrace_2578914 : CollatzResearch.WordTrace tailWord_2578914 prefixEnd_2578914 147135827623247580090533 := by
  unfold tailWord_2578914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23515180244760624072703949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62707147319361664193877197 23515180244760624072703949)
  ·
    refine ⟨8818192591785234027263981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23515180244760624072703949 8818192591785234027263981)
    ·
      refine ⟨3306822221919462760223993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8818192591785234027263981 3306822221919462760223993)
      ·
        refine ⟨2480116666439597070167995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3306822221919462760223993 2480116666439597070167995)
        ·
          refine ⟨3720174999659395605251993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480116666439597070167995 3720174999659395605251993)
          ·
            refine ⟨2790131249744546703938995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3720174999659395605251993 2790131249744546703938995)
            ·
              refine ⟨4185196874616820055908493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790131249744546703938995 4185196874616820055908493)
              ·
                refine ⟨1569448827981307520965685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4185196874616820055908493 1569448827981307520965685)
                ·
                  refine ⟨147135827623247580090533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1569448827981307520965685 147135827623247580090533)
                  ·
                    rfl

theorem cell23_2578914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_2578914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578914 prefixEnd_2578914 := by exact prefixLift 2578914
  have htrace : WordTrace (prefixWord ++ tailWord_2578914) baseStart_2578914 baseEnd_2578914 := by
    simpa [prefixWord, tailWord_2578914, baseEnd_2578914] using wordTrace_append hprefix tailTrace_2578914
  have hstable : (prefixWord ++ tailWord_2578914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578914).length < 2 ^ (prefixWord ++ tailWord_2578914).sum := by decide
  have hdescent : baseEnd_2578914 < baseStart_2578914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578930 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2578930 : Nat := 118140960795 + 2578930 * 2 ^ 59
def prefixEnd_2578930 : Nat := 4983230072969 + 3 ^ 40 * 2578930 * 2
def baseEnd_2578930 : Nat := 1324230664299700158214723

theorem tailTrace_2578930 : CollatzResearch.WordTrace tailWord_2578930 prefixEnd_2578930 1324230664299700158214723 := by
  unfold tailWord_2578930
  simp only [CollatzResearch.WordTrace]
  refine ⟨23515326136746132755849561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62707536364656354015598829 23515326136746132755849561)
  ·
    refine ⟨17636494602559599566887171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23515326136746132755849561 17636494602559599566887171)
    ·
      refine ⟨26454741903839399350330757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17636494602559599566887171 26454741903839399350330757)
      ·
        refine ⟨4960264106969887378187017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26454741903839399350330757 4960264106969887378187017)
        ·
          refine ⟨3720198080227415533640263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4960264106969887378187017 3720198080227415533640263)
          ·
            refine ⟨5580297120341123300460395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720198080227415533640263 5580297120341123300460395)
            ·
              refine ⟨8370445680511684950690593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5580297120341123300460395 8370445680511684950690593)
              ·
                refine ⟨6277834260383763713017945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8370445680511684950690593 6277834260383763713017945)
                ·
                  refine ⟨4708375695287822784763459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6277834260383763713017945 4708375695287822784763459)
                  ·
                    refine ⟨7062563542931734177145189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4708375695287822784763459 7062563542931734177145189)
                    ·
                      refine ⟨1324230664299700158214723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7062563542931734177145189 1324230664299700158214723)
                      ·
                        rfl

theorem cell23_2578930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2578930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578930 prefixEnd_2578930 := by exact prefixLift 2578930
  have htrace : WordTrace (prefixWord ++ tailWord_2578930) baseStart_2578930 baseEnd_2578930 := by
    simpa [prefixWord, tailWord_2578930, baseEnd_2578930] using wordTrace_append hprefix tailTrace_2578930
  have hstable : (prefixWord ++ tailWord_2578930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578930).length < 2 ^ (prefixWord ++ tailWord_2578930).sum := by decide
  have hdescent : baseEnd_2578930 < baseStart_2578930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578936 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 6]
def baseStart_2578936 : Nat := 118140960795 + 2578936 * 2 ^ 59
def prefixEnd_2578936 : Nat := 4983230072969 + 3 ^ 40 * 2578936 * 2
def baseEnd_2578936 : Nat := 147137082798180792748855

theorem tailTrace_2578936 : CollatzResearch.WordTrace tailWord_2578936 prefixEnd_2578936 147137082798180792748855 := by
  unfold tailWord_2578936
  simp only [CollatzResearch.WordTrace]
  refine ⟨47030761692481397024058331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62707682256641862698744441 47030761692481397024058331)
  ·
    refine ⟨70546142538722095536087497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47030761692481397024058331 70546142538722095536087497)
    ·
      refine ⟨52909606904041571652065623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70546142538722095536087497 52909606904041571652065623)
      ·
        refine ⟨79364410356062357478098435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52909606904041571652065623 79364410356062357478098435)
        ·
          refine ⟨119046615534093536217147653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79364410356062357478098435 119046615534093536217147653)
          ·
            refine ⟨22321240412642538040715185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119046615534093536217147653 22321240412642538040715185)
            ·
              refine ⟨16740930309481903530536389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22321240412642538040715185 16740930309481903530536389)
              ·
                refine ⟨3138924433027856911975573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16740930309481903530536389 3138924433027856911975573)
                ·
                  refine ⟨147137082798180792748855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3138924433027856911975573 147137082798180792748855)
                  ·
                    rfl

theorem cell23_2578936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 6].length) (baseStart_2578936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578936 prefixEnd_2578936 := by exact prefixLift 2578936
  have htrace : WordTrace (prefixWord ++ tailWord_2578936) baseStart_2578936 baseEnd_2578936 := by
    simpa [prefixWord, tailWord_2578936, baseEnd_2578936] using wordTrace_append hprefix tailTrace_2578936
  have hstable : (prefixWord ++ tailWord_2578936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578936).length < 2 ^ (prefixWord ++ tailWord_2578936).sum := by decide
  have hdescent : baseEnd_2578936 < baseStart_2578936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578963 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 5, 1, 3]
def baseStart_2578963 : Nat := 118140960795 + 2578963 * 2 ^ 59
def prefixEnd_2578963 : Nat := 4983230072969 + 3 ^ 40 * 2578963 * 2
def baseEnd_2578963 : Nat := 1324247609161298529102071

theorem tailTrace_2578963 : CollatzResearch.WordTrace tailWord_2578963 prefixEnd_2578963 1324247609161298529102071 := by
  unfold tailWord_2578963
  simp only [CollatzResearch.WordTrace]
  refine ⟨94062508155864977659349543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62708338770576651772899695 94062508155864977659349543)
  ·
    refine ⟨141093762233797466489024315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94062508155864977659349543 141093762233797466489024315)
    ·
      refine ⟨211640643350696199733536473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141093762233797466489024315 211640643350696199733536473)
      ·
        refine ⟨158730482513022149800152355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211640643350696199733536473 158730482513022149800152355)
        ·
          refine ⟨238095723769533224700228533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158730482513022149800152355 238095723769533224700228533)
          ·
            refine ⟨22321474103393739815646425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 238095723769533224700228533 22321474103393739815646425)
            ·
              refine ⟨16741105577545304861734819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22321474103393739815646425 16741105577545304861734819)
              ·
                refine ⟨25111658366317957292602229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16741105577545304861734819 25111658366317957292602229)
                ·
                  refine ⟨2354217971842308496181459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25111658366317957292602229 2354217971842308496181459)
                  ·
                    refine ⟨3531326957763462744272189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2354217971842308496181459 3531326957763462744272189)
                    ·
                      refine ⟨1324247609161298529102071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3531326957763462744272189 1324247609161298529102071)
                      ·
                        rfl

theorem cell23_2578963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 1, 3].length) (baseStart_2578963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578963 prefixEnd_2578963 := by exact prefixLift 2578963
  have htrace : WordTrace (prefixWord ++ tailWord_2578963) baseStart_2578963 baseEnd_2578963 := by
    simpa [prefixWord, tailWord_2578963, baseEnd_2578963] using wordTrace_append hprefix tailTrace_2578963
  have hstable : (prefixWord ++ tailWord_2578963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578963).length < 2 ^ (prefixWord ++ tailWord_2578963).sum := by decide
  have hdescent : baseEnd_2578963 < baseStart_2578963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578967 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2578967 : Nat := 118140960795 + 2578967 * 2 ^ 59
def prefixEnd_2578967 : Nat := 4983230072969 + 3 ^ 40 * 2578967 * 2
def baseEnd_2578967 : Nat := 1324249663083916513452053

theorem tailTrace_2578967 : CollatzResearch.WordTrace tailWord_2578967 prefixEnd_2578967 1324249663083916513452053 := by
  unfold tailWord_2578967
  simp only [CollatzResearch.WordTrace]
  refine ⟨94062654047850486342495155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62708436031900324228330103 94062654047850486342495155)
  ·
    refine ⟨141093981071775729513742733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94062654047850486342495155 141093981071775729513742733)
    ·
      refine ⟨52910242901915898567653525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141093981071775729513742733 52910242901915898567653525)
      ·
        refine ⟨2480167636027307745358759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52910242901915898567653525 2480167636027307745358759)
        ·
          refine ⟨3720251454040961618038139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480167636027307745358759 3720251454040961618038139)
          ·
            refine ⟨5580377181061442427057209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720251454040961618038139 5580377181061442427057209)
            ·
              refine ⟨4185282885796081820292907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5580377181061442427057209 4185282885796081820292907)
              ·
                refine ⟨6277924328694122730439361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185282885796081820292907 6277924328694122730439361)
                ·
                  refine ⟨4708443246520592047829521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6277924328694122730439361 4708443246520592047829521)
                  ·
                    refine ⟨3531332434890444035872141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4708443246520592047829521 3531332434890444035872141)
                    ·
                      refine ⟨1324249663083916513452053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3531332434890444035872141 1324249663083916513452053)
                      ·
                        rfl

theorem cell23_2578967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2578967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578967 prefixEnd_2578967 := by exact prefixLift 2578967
  have htrace : WordTrace (prefixWord ++ tailWord_2578967) baseStart_2578967 baseEnd_2578967 := by
    simpa [prefixWord, tailWord_2578967, baseEnd_2578967] using wordTrace_append hprefix tailTrace_2578967
  have hstable : (prefixWord ++ tailWord_2578967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578967).length < 2 ^ (prefixWord ++ tailWord_2578967).sum := by decide
  have hdescent : baseEnd_2578967 < baseStart_2578967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578997 : List Nat := [1, 3, 3, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_2578997 : Nat := 118140960795 + 2578997 * 2 ^ 59
def prefixEnd_2578997 : Nat := 4983230072969 + 3 ^ 40 * 2578997 * 2
def baseEnd_2578997 : Nat := 1324265067503551396076915

theorem tailTrace_2578997 : CollatzResearch.WordTrace tailWord_2578997 prefixEnd_2578997 1324265067503551396076915 := by
  unfold tailWord_2578997
  simp only [CollatzResearch.WordTrace]
  refine ⟨94063748237741801466087245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62709165491827867644058163 94063748237741801466087245)
  ·
    refine ⟨35273905589153175549782717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94063748237741801466087245 35273905589153175549782717)
    ·
      refine ⟨13227714595932440831168519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35273905589153175549782717 13227714595932440831168519)
      ·
        refine ⟨19841571893898661246752779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13227714595932440831168519 19841571893898661246752779)
        ·
          refine ⟨29762357840847991870129169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19841571893898661246752779 29762357840847991870129169)
          ·
            refine ⟨22321768380635993902596877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29762357840847991870129169 22321768380635993902596877)
            ·
              refine ⟨8370663142738497713473829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22321768380635993902596877 8370663142738497713473829)
              ·
                refine ⟨1569499339263468321276343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8370663142738497713473829 1569499339263468321276343)
                ·
                  refine ⟨2354249008895202481914515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569499339263468321276343 2354249008895202481914515)
                  ·
                    refine ⟨3531373513342803722871773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2354249008895202481914515 3531373513342803722871773)
                    ·
                      refine ⟨1324265067503551396076915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3531373513342803722871773 1324265067503551396076915)
                      ·
                        rfl

theorem cell23_2578997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_2578997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2578997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2578997 prefixEnd_2578997 := by exact prefixLift 2578997
  have htrace : WordTrace (prefixWord ++ tailWord_2578997) baseStart_2578997 baseEnd_2578997 := by
    simpa [prefixWord, tailWord_2578997, baseEnd_2578997] using wordTrace_append hprefix tailTrace_2578997
  have hstable : (prefixWord ++ tailWord_2578997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578997).length < 2 ^ (prefixWord ++ tailWord_2578997).sum := by decide
  have hdescent : baseEnd_2578997 < baseStart_2578997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579013 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_2579013 : Nat := 118140960795 + 2579013 * 2 ^ 59
def prefixEnd_2579013 : Nat := 4983230072969 + 3 ^ 40 * 2579013 * 2
def baseEnd_2579013 : Nat := 441424427731341111158947

theorem tailTrace_2579013 : CollatzResearch.WordTrace tailWord_2579013 prefixEnd_2579013 441424427731341111158947 := by
  unfold tailWord_2579013
  simp only [CollatzResearch.WordTrace]
  refine ⟨94064331805683836198669693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62709554537122557465779795 94064331805683836198669693)
  ·
    refine ⟨35274124427131438574501135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94064331805683836198669693 35274124427131438574501135)
    ·
      refine ⟨52911186640697157861751703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35274124427131438574501135 52911186640697157861751703)
      ·
        refine ⟨79366779961045736792627555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52911186640697157861751703 79366779961045736792627555)
        ·
          refine ⟨119050169941568605188941333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79366779961045736792627555 119050169941568605188941333)
          ·
            refine ⟨5580476716011028368231625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119050169941568605188941333 5580476716011028368231625)
            ·
              refine ⟨4185357537008271276173719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5580476716011028368231625 4185357537008271276173719)
              ·
                refine ⟨6278036305512406914260579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185357537008271276173719 6278036305512406914260579)
                ·
                  refine ⟨9417054458268610371390869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6278036305512406914260579 9417054458268610371390869)
                  ·
                    refine ⟨441424427731341111158947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9417054458268610371390869 441424427731341111158947)
                    ·
                      rfl

theorem cell23_2579013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_2579013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579013 prefixEnd_2579013 := by exact prefixLift 2579013
  have htrace : WordTrace (prefixWord ++ tailWord_2579013) baseStart_2579013 baseEnd_2579013 := by
    simpa [prefixWord, tailWord_2579013, baseEnd_2579013] using wordTrace_append hprefix tailTrace_2579013
  have hstable : (prefixWord ++ tailWord_2579013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579013).length < 2 ^ (prefixWord ++ tailWord_2579013).sum := by decide
  have hdescent : baseEnd_2579013 < baseStart_2579013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579014 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2579014 : Nat := 118140960795 + 2579014 * 2 ^ 59
def prefixEnd_2579014 : Nat := 4983230072969 + 3 ^ 40 * 2579014 * 2
def baseEnd_2579014 : Nat := 1324273796674677829564337

theorem tailTrace_2579014 : CollatzResearch.WordTrace tailWord_2579014 prefixEnd_2579014 1324273796674677829564337 := by
  unfold tailWord_2579014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939511508708756667795503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62709578852453475579637397 2939511508708756667795503)
  ·
    refine ⟨4409267263063135001693255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2939511508708756667795503 4409267263063135001693255)
    ·
      refine ⟨6613900894594702502539883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4409267263063135001693255 6613900894594702502539883)
      ·
        refine ⟨9920851341892053753809825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6613900894594702502539883 9920851341892053753809825)
        ·
          refine ⟨7440638506419040315357369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9920851341892053753809825 7440638506419040315357369)
          ·
            refine ⟨5580478879814280236518027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7440638506419040315357369 5580478879814280236518027)
            ·
              refine ⟨8370718319721420354777041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5580478879814280236518027 8370718319721420354777041)
              ·
                refine ⟨6278038739791065266082781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8370718319721420354777041 6278038739791065266082781)
                ·
                  refine ⟨2354264527421649474781043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6278038739791065266082781 2354264527421649474781043)
                  ·
                    refine ⟨3531396791132474212171565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2354264527421649474781043 3531396791132474212171565)
                    ·
                      refine ⟨1324273796674677829564337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3531396791132474212171565 1324273796674677829564337)
                      ·
                        rfl

theorem cell23_2579014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2579014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579014 prefixEnd_2579014 := by exact prefixLift 2579014
  have htrace : WordTrace (prefixWord ++ tailWord_2579014) baseStart_2579014 baseEnd_2579014 := by
    simpa [prefixWord, tailWord_2579014, baseEnd_2579014] using wordTrace_append hprefix tailTrace_2579014
  have hstable : (prefixWord ++ tailWord_2579014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579014).length < 2 ^ (prefixWord ++ tailWord_2579014).sum := by decide
  have hdescent : baseEnd_2579014 < baseStart_2579014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579016 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_2579016 : Nat := 118140960795 + 2579016 * 2 ^ 59
def prefixEnd_2579016 : Nat := 4983230072969 + 3 ^ 40 * 2579016 * 2
def baseEnd_2579016 : Nat := 1324274823635986821739327

theorem tailTrace_2579016 : CollatzResearch.WordTrace tailWord_2579016 prefixEnd_2579016 1324274823635986821739327 := by
  unfold tailWord_2579016
  simp only [CollatzResearch.WordTrace]
  refine ⟨47032220612336483855514451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62709627483115311807352601 47032220612336483855514451)
  ·
    refine ⟨70548330918504725783271677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47032220612336483855514451 70548330918504725783271677)
    ·
      refine ⟨26455624094439272168726879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70548330918504725783271677 26455624094439272168726879)
      ·
        refine ⟨39683436141658908253090319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26455624094439272168726879 39683436141658908253090319)
        ·
          refine ⟨59525154212488362379635479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39683436141658908253090319 59525154212488362379635479)
          ·
            refine ⟨89287731318732543569453219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59525154212488362379635479 89287731318732543569453219)
            ·
              refine ⟨133931596978098815354179829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89287731318732543569453219 133931596978098815354179829)
              ·
                refine ⟨12556087216696763939454359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133931596978098815354179829 12556087216696763939454359)
                ·
                  refine ⟨18834130825045145909181539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12556087216696763939454359 18834130825045145909181539)
                  ·
                    refine ⟨28251196237567718863772309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18834130825045145909181539 28251196237567718863772309)
                    ·
                      refine ⟨1324274823635986821739327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28251196237567718863772309 1324274823635986821739327)
                      ·
                        rfl

theorem cell23_2579016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_2579016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579016 prefixEnd_2579016 := by exact prefixLift 2579016
  have htrace : WordTrace (prefixWord ++ tailWord_2579016) baseStart_2579016 baseEnd_2579016 := by
    simpa [prefixWord, tailWord_2579016, baseEnd_2579016] using wordTrace_append hprefix tailTrace_2579016
  have hstable : (prefixWord ++ tailWord_2579016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579016).length < 2 ^ (prefixWord ++ tailWord_2579016).sum := by decide
  have hdescent : baseEnd_2579016 < baseStart_2579016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579023 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 3]
def baseStart_2579023 : Nat := 118140960795 + 2579023 * 2 ^ 59
def prefixEnd_2579023 : Nat := 4983230072969 + 3 ^ 40 * 2579023 * 2
def baseEnd_2579023 : Nat := 1324278418000568294351795

theorem tailTrace_2579023 : CollatzResearch.WordTrace tailWord_2579023 prefixEnd_2579023 1324278418000568294351795 := by
  unfold tailWord_2579023
  simp only [CollatzResearch.WordTrace]
  refine ⟨94064696535647607906533723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62709797690431738604355815 94064696535647607906533723)
  ·
    refine ⟨141097044803471411859800585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94064696535647607906533723 141097044803471411859800585)
    ·
      refine ⟨105822783602603558894850439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141097044803471411859800585 105822783602603558894850439)
      ·
        refine ⟨158734175403905338342275659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105822783602603558894850439 158734175403905338342275659)
        ·
          refine ⟨238101263105858007513413489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158734175403905338342275659 238101263105858007513413489)
          ·
            refine ⟨178575947329393505635060117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238101263105858007513413489 178575947329393505635060117)
            ·
              refine ⟨8370747531065320576643443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 178575947329393505635060117 8370747531065320576643443)
              ·
                refine ⟨12556121296597980864965165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8370747531065320576643443 12556121296597980864965165)
                ·
                  refine ⟨4708545486224242824361937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12556121296597980864965165 4708545486224242824361937)
                  ·
                    refine ⟨3531409114668182118271453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4708545486224242824361937 3531409114668182118271453)
                    ·
                      refine ⟨1324278418000568294351795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3531409114668182118271453 1324278418000568294351795)
                      ·
                        rfl

theorem cell23_2579023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 3].length) (baseStart_2579023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579023 prefixEnd_2579023 := by exact prefixLift 2579023
  have htrace : WordTrace (prefixWord ++ tailWord_2579023) baseStart_2579023 baseEnd_2579023 := by
    simpa [prefixWord, tailWord_2579023, baseEnd_2579023] using wordTrace_append hprefix tailTrace_2579023
  have hstable : (prefixWord ++ tailWord_2579023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579023).length < 2 ^ (prefixWord ++ tailWord_2579023).sum := by decide
  have hdescent : baseEnd_2579023 < baseStart_2579023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579054 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_2579054 : Nat := 118140960795 + 2579054 * 2 ^ 59
def prefixEnd_2579054 : Nat := 4983230072969 + 3 ^ 40 * 2579054 * 2
def baseEnd_2579054 : Nat := 1324294335900857673064153

theorem tailTrace_2579054 : CollatzResearch.WordTrace tailWord_2579054 prefixEnd_2579054 1324294335900857673064153 := by
  unfold tailWord_2579054
  simp only [CollatzResearch.WordTrace]
  refine ⟨11758228399816912525114027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62710551465690200133941477 11758228399816912525114027)
  ·
    refine ⟨17637342599725368787671041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11758228399816912525114027 17637342599725368787671041)
    ·
      refine ⟨13228006949794026590753281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17637342599725368787671041 13228006949794026590753281)
      ·
        refine ⟨9921005212345519943064961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13228006949794026590753281 9921005212345519943064961)
        ·
          refine ⟨7440753909259139957298721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9921005212345519943064961 7440753909259139957298721)
          ·
            refine ⟨5580565431944354967974041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7440753909259139957298721 5580565431944354967974041)
            ·
              refine ⟨4185424073958266225980531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5580565431944354967974041 4185424073958266225980531)
              ·
                refine ⟨6278136110937399338970797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185424073958266225980531 6278136110937399338970797)
                ·
                  refine ⟨2354301041601524752114049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6278136110937399338970797 2354301041601524752114049)
                  ·
                    refine ⟨1765725781201143564085537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2354301041601524752114049 1765725781201143564085537)
                    ·
                      refine ⟨1324294335900857673064153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1765725781201143564085537 1324294335900857673064153)
                      ·
                        rfl

theorem cell23_2579054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_2579054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579054 prefixEnd_2579054 := by exact prefixLift 2579054
  have htrace : WordTrace (prefixWord ++ tailWord_2579054) baseStart_2579054 baseEnd_2579054 := by
    simpa [prefixWord, tailWord_2579054, baseEnd_2579054] using wordTrace_append hprefix tailTrace_2579054
  have hstable : (prefixWord ++ tailWord_2579054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579054).length < 2 ^ (prefixWord ++ tailWord_2579054).sum := by decide
  have hdescent : baseEnd_2579054 < baseStart_2579054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579143 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_2579143 : Nat := 118140960795 + 2579143 * 2 ^ 59
def prefixEnd_2579143 : Nat := 4983230072969 + 3 ^ 40 * 2579143 * 2
def baseEnd_2579143 : Nat := 1324340035679107824851243

theorem tailTrace_2579143 : CollatzResearch.WordTrace tailWord_2579143 prefixEnd_2579143 1324340035679107824851243 := by
  unfold tailWord_2579143
  simp only [CollatzResearch.WordTrace]
  refine ⟨94069073295212868400902083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62712715530141912267268055 94069073295212868400902083)
  ·
    refine ⟨141103609942819302601353125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94069073295212868400902083 141103609942819302601353125)
    ·
      refine ⟨26456926864278619237753711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141103609942819302601353125 26456926864278619237753711)
      ·
        refine ⟨39685390296417928856630567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26456926864278619237753711 39685390296417928856630567)
        ·
          refine ⟨59528085444626893284945851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39685390296417928856630567 59528085444626893284945851)
          ·
            refine ⟨89292128166940339927418777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59528085444626893284945851 89292128166940339927418777)
            ·
              refine ⟨66969096125205254945564083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89292128166940339927418777 66969096125205254945564083)
              ·
                refine ⟨100453644187807882418346125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66969096125205254945564083 100453644187807882418346125)
                ·
                  refine ⟨37670116570427955906879797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100453644187807882418346125 37670116570427955906879797)
                  ·
                    refine ⟨3531573428477620866269981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37670116570427955906879797 3531573428477620866269981)
                    ·
                      refine ⟨1324340035679107824851243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3531573428477620866269981 1324340035679107824851243)
                      ·
                        rfl

theorem cell23_2579143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_2579143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579143 prefixEnd_2579143 := by exact prefixLift 2579143
  have htrace : WordTrace (prefixWord ++ tailWord_2579143) baseStart_2579143 baseEnd_2579143 := by
    simpa [prefixWord, tailWord_2579143, baseEnd_2579143] using wordTrace_append hprefix tailTrace_2579143
  have hstable : (prefixWord ++ tailWord_2579143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579143).length < 2 ^ (prefixWord ++ tailWord_2579143).sum := by decide
  have hdescent : baseEnd_2579143 < baseStart_2579143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579167 : List Nat := [1, 1, 2, 3, 2, 3, 4, 2, 5]
def baseStart_2579167 : Nat := 118140960795 + 2579167 * 2 ^ 59
def prefixEnd_2579167 : Nat := 4983230072969 + 3 ^ 40 * 2579167 * 2
def baseEnd_2579167 : Nat := 147150262134979525661237

theorem tailTrace_2579167 : CollatzResearch.WordTrace tailWord_2579167 prefixEnd_2579167 147150262134979525661237 := by
  unfold tailWord_2579167
  simp only [CollatzResearch.WordTrace]
  refine ⟨94069948647125920499775755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62713299098083946999850503 94069948647125920499775755)
  ·
    refine ⟨141104922970688880749663633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94069948647125920499775755 141104922970688880749663633)
    ·
      refine ⟨105828692228016660562247725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141104922970688880749663633 105828692228016660562247725)
      ·
        refine ⟨39685759585506247710842897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105828692228016660562247725 39685759585506247710842897)
        ·
          refine ⟨29764319689129685783132173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39685759585506247710842897 29764319689129685783132173)
          ·
            refine ⟨11161619883423632168674565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29764319689129685783132173 11161619883423632168674565)
            ·
              refine ⟨2092803728141931031626481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11161619883423632168674565 2092803728141931031626481)
              ·
                refine ⟨1569602796106448273719861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092803728141931031626481 1569602796106448273719861)
                ·
                  refine ⟨147150262134979525661237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1569602796106448273719861 147150262134979525661237)
                  ·
                    rfl

theorem cell23_2579167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 5].length) (baseStart_2579167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579167 prefixEnd_2579167 := by exact prefixLift 2579167
  have htrace : WordTrace (prefixWord ++ tailWord_2579167) baseStart_2579167 baseEnd_2579167 := by
    simpa [prefixWord, tailWord_2579167, baseEnd_2579167] using wordTrace_append hprefix tailTrace_2579167
  have hstable : (prefixWord ++ tailWord_2579167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579167).length < 2 ^ (prefixWord ++ tailWord_2579167).sum := by decide
  have hdescent : baseEnd_2579167 < baseStart_2579167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579200 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 6, 4, 2]
def baseStart_2579200 : Nat := 118140960795 + 2579200 * 2 ^ 59
def prefixEnd_2579200 : Nat := 4983230072969 + 3 ^ 40 * 2579200 * 2
def baseEnd_2579200 : Nat := 1324369304076414101838481

theorem tailTrace_2579200 : CollatzResearch.WordTrace tailWord_2579200 prefixEnd_2579200 1324369304076414101838481 := by
  unfold tailWord_2579200
  simp only [CollatzResearch.WordTrace]
  refine ⟨47035576128003183567863527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62714101504004244757151369 47035576128003183567863527)
  ·
    refine ⟨70553364192004775351795291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47035576128003183567863527 70553364192004775351795291)
    ·
      refine ⟨105830046288007163027692937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70553364192004775351795291 105830046288007163027692937)
      ·
        refine ⟨79372534716005372270769703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105830046288007163027692937 79372534716005372270769703)
        ·
          refine ⟨119058802074008058406154555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79372534716005372270769703 119058802074008058406154555)
          ·
            refine ⟨178588203111012087609231833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119058802074008058406154555 178588203111012087609231833)
            ·
              refine ⟨133941152333259065706923875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178588203111012087609231833 133941152333259065706923875)
              ·
                refine ⟨200911728499888598560385813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133941152333259065706923875 200911728499888598560385813)
                ·
                  refine ⟨9417737273432278057518085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 200911728499888598560385813 9417737273432278057518085)
                  ·
                    refine ⟨1765825738768552135784641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9417737273432278057518085 1765825738768552135784641)
                    ·
                      refine ⟨1324369304076414101838481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1765825738768552135784641 1324369304076414101838481)
                      ·
                        rfl

theorem cell23_2579200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_2579200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579200 prefixEnd_2579200 := by exact prefixLift 2579200
  have htrace : WordTrace (prefixWord ++ tailWord_2579200) baseStart_2579200 baseEnd_2579200 := by
    simpa [prefixWord, tailWord_2579200, baseEnd_2579200] using wordTrace_append hprefix tailTrace_2579200
  have hstable : (prefixWord ++ tailWord_2579200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579200).length < 2 ^ (prefixWord ++ tailWord_2579200).sum := by decide
  have hdescent : baseEnd_2579200 < baseStart_2579200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579210 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_2579210 : Nat := 118140960795 + 2579210 * 2 ^ 59
def prefixEnd_2579210 : Nat := 4983230072969 + 3 ^ 40 * 2579210 * 2
def baseEnd_2579210 : Nat := 441458146294319687571145

theorem tailTrace_2579210 : CollatzResearch.WordTrace tailWord_2579210 prefixEnd_2579210 441458146294319687571145 := by
  unfold tailWord_2579210
  simp only [CollatzResearch.WordTrace]
  refine ⟨23517879246492534710897771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62714344657313425895727389 23517879246492534710897771)
  ·
    refine ⟨35276818869738802066346657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23517879246492534710897771 35276818869738802066346657)
    ·
      refine ⟨26457614152304101549759993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35276818869738802066346657 26457614152304101549759993)
      ·
        refine ⟨19843210614228076162319995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26457614152304101549759993 19843210614228076162319995)
        ·
          refine ⟨29764815921342114243479993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19843210614228076162319995 29764815921342114243479993)
          ·
            refine ⟨22323611941006585682609995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29764815921342114243479993 22323611941006585682609995)
            ·
              refine ⟨33485417911509878523914993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22323611941006585682609995 33485417911509878523914993)
              ·
                refine ⟨25114063433632408892936245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33485417911509878523914993 25114063433632408892936245)
                ·
                  refine ⟨2354443446903038333712773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25114063433632408892936245 2354443446903038333712773)
                  ·
                    refine ⟨441458146294319687571145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2354443446903038333712773 441458146294319687571145)
                    ·
                      rfl

theorem cell23_2579210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_2579210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579210 prefixEnd_2579210 := by exact prefixLift 2579210
  have htrace : WordTrace (prefixWord ++ tailWord_2579210) baseStart_2579210 baseEnd_2579210 := by
    simpa [prefixWord, tailWord_2579210, baseEnd_2579210] using wordTrace_append hprefix tailTrace_2579210
  have hstable : (prefixWord ++ tailWord_2579210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579210).length < 2 ^ (prefixWord ++ tailWord_2579210).sum := by decide
  have hdescent : baseEnd_2579210 < baseStart_2579210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579250 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_2579250 : Nat := 118140960795 + 2579250 * 2 ^ 59
def prefixEnd_2579250 : Nat := 4983230072969 + 3 ^ 40 * 2579250 * 2
def baseEnd_2579250 : Nat := 1324394978109138906213251

theorem tailTrace_2579250 : CollatzResearch.WordTrace tailWord_2579250 prefixEnd_2579250 1324394978109138906213251 := by
  unfold tailWord_2579250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23518243976456306418761801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62715317270550150450031469 23518243976456306418761801)
  ·
    refine ⟨17638682982342229814071351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23518243976456306418761801 17638682982342229814071351)
    ·
      refine ⟨26458024473513344721107027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17638682982342229814071351 26458024473513344721107027)
      ·
        refine ⟨39687036710270017081660541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26458024473513344721107027 39687036710270017081660541)
        ·
          refine ⟨14882638766351256405622703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39687036710270017081660541 14882638766351256405622703)
          ·
            refine ⟨22323958149526884608434055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14882638766351256405622703 22323958149526884608434055)
            ·
              refine ⟨33485937224290326912651083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22323958149526884608434055 33485937224290326912651083)
              ·
                refine ⟨50228905836435490368976625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33485937224290326912651083 50228905836435490368976625)
                ·
                  refine ⟨37671679377326617776732469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50228905836435490368976625 37671679377326617776732469)
                  ·
                    refine ⟨3531719941624370416568669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37671679377326617776732469 3531719941624370416568669)
                    ·
                      refine ⟨1324394978109138906213251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3531719941624370416568669 1324394978109138906213251)
                      ·
                        rfl

theorem cell23_2579250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_2579250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579250 prefixEnd_2579250 := by exact prefixLift 2579250
  have htrace : WordTrace (prefixWord ++ tailWord_2579250) baseStart_2579250 baseEnd_2579250 := by
    simpa [prefixWord, tailWord_2579250, baseEnd_2579250] using wordTrace_append hprefix tailTrace_2579250
  have hstable : (prefixWord ++ tailWord_2579250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579250).length < 2 ^ (prefixWord ++ tailWord_2579250).sum := by decide
  have hdescent : baseEnd_2579250 < baseStart_2579250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579304 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 1, 5]
def baseStart_2579304 : Nat := 118140960795 + 2579304 * 2 ^ 59
def prefixEnd_2579304 : Nat := 4983230072969 + 3 ^ 40 * 2579304 * 2
def baseEnd_2579304 : Nat := 441474235354827231646001

theorem tailTrace_2579304 : CollatzResearch.WordTrace tailWord_2579304 prefixEnd_2579304 441474235354827231646001 := by
  unfold tailWord_2579304
  simp only [CollatzResearch.WordTrace]
  refine ⟨47037472723814796448756483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62716630298419728598341977 47037472723814796448756483)
  ·
    refine ⟨70556209085722194673134725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47037472723814796448756483 70556209085722194673134725)
    ·
      refine ⟨13229289203572911501212761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70556209085722194673134725 13229289203572911501212761)
      ·
        refine ⟨9921966902679683625909571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13229289203572911501212761 9921966902679683625909571)
        ·
          refine ⟨14882950354019525438864357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9921966902679683625909571 14882950354019525438864357)
          ·
            refine ⟨2790553191378661019787067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14882950354019525438864357 2790553191378661019787067)
            ·
              refine ⟨4185829787067991529680601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790553191378661019787067 4185829787067991529680601)
              ·
                refine ⟨3139372340300993647260451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4185829787067991529680601 3139372340300993647260451)
                ·
                  refine ⟨4709058510451490470890677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139372340300993647260451 4709058510451490470890677)
                  ·
                    refine ⟨441474235354827231646001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4709058510451490470890677 441474235354827231646001)
                    ·
                      rfl

theorem cell23_2579304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_2579304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579304 prefixEnd_2579304 := by exact prefixLift 2579304
  have htrace : WordTrace (prefixWord ++ tailWord_2579304) baseStart_2579304 baseEnd_2579304 := by
    simpa [prefixWord, tailWord_2579304, baseEnd_2579304] using wordTrace_append hprefix tailTrace_2579304
  have hstable : (prefixWord ++ tailWord_2579304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579304).length < 2 ^ (prefixWord ++ tailWord_2579304).sum := by decide
  have hdescent : baseEnd_2579304 < baseStart_2579304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579307 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 4]
def baseStart_2579307 : Nat := 118140960795 + 2579307 * 2 ^ 59
def prefixEnd_2579307 : Nat := 4983230072969 + 3 ^ 40 * 2579307 * 2
def baseEnd_2579307 : Nat := 1324424246506445183200489

theorem tailTrace_2579307 : CollatzResearch.WordTrace tailWord_2579307 prefixEnd_2579307 1324424246506445183200489 := by
  unfold tailWord_2579307
  simp only [CollatzResearch.WordTrace]
  refine ⟨94075054866618724409872175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62716703244412482939914783 94075054866618724409872175)
  ·
    refine ⟨141112582299928086614808263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94075054866618724409872175 141112582299928086614808263)
    ·
      refine ⟨211668873449892129922212395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141112582299928086614808263 211668873449892129922212395)
      ·
        refine ⟨317503310174838194883318593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211668873449892129922212395 317503310174838194883318593)
        ·
          refine ⟨238127482631128646162488945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317503310174838194883318593 238127482631128646162488945)
          ·
            refine ⟨178595611973346484621866709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238127482631128646162488945 178595611973346484621866709)
            ·
              refine ⟨4185834655625308233325001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 178595611973346484621866709 4185834655625308233325001)
              ·
                refine ⟨3139375991718981174993751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4185834655625308233325001 3139375991718981174993751)
                ·
                  refine ⟨4709063987578471762490627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139375991718981174993751 4709063987578471762490627)
                  ·
                    refine ⟨7063595981367707643735941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4709063987578471762490627 7063595981367707643735941)
                    ·
                      refine ⟨1324424246506445183200489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7063595981367707643735941 1324424246506445183200489)
                      ·
                        rfl

theorem cell23_2579307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 4].length) (baseStart_2579307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579307 prefixEnd_2579307 := by exact prefixLift 2579307
  have htrace : WordTrace (prefixWord ++ tailWord_2579307) baseStart_2579307 baseEnd_2579307 := by
    simpa [prefixWord, tailWord_2579307, baseEnd_2579307] using wordTrace_append hprefix tailTrace_2579307
  have hstable : (prefixWord ++ tailWord_2579307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579307).length < 2 ^ (prefixWord ++ tailWord_2579307).sum := by decide
  have hdescent : baseEnd_2579307 < baseStart_2579307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579317 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2579317 : Nat := 118140960795 + 2579317 * 2 ^ 59
def prefixEnd_2579317 : Nat := 4983230072969 + 3 ^ 40 * 2579317 * 2
def baseEnd_2579317 : Nat := 441476460437663381358481

theorem tailTrace_2579317 : CollatzResearch.WordTrace tailWord_2579317 prefixEnd_2579317 441476460437663381358481 := by
  unfold tailWord_2579317
  simp only [CollatzResearch.WordTrace]
  refine ⟨94075419596582496117736205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62716946397721664078490803 94075419596582496117736205)
  ·
    refine ⟨35278282348718436044151077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94075419596582496117736205 35278282348718436044151077)
    ·
      refine ⟨6614677940384706758278327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35278282348718436044151077 6614677940384706758278327)
      ·
        refine ⟨9922016910577060137417491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6614677940384706758278327 9922016910577060137417491)
        ·
          refine ⟨14883025365865590206126237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9922016910577060137417491 14883025365865590206126237)
          ·
            refine ⟨5581134512199596327297339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14883025365865590206126237 5581134512199596327297339)
            ·
              refine ⟨8371701768299394490946009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5581134512199596327297339 8371701768299394490946009)
              ·
                refine ⟨6278776326224545868209507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8371701768299394490946009 6278776326224545868209507)
                ·
                  refine ⟨9418164489336818802314261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6278776326224545868209507 9418164489336818802314261)
                  ·
                    refine ⟨441476460437663381358481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9418164489336818802314261 441476460437663381358481)
                    ·
                      rfl

theorem cell23_2579317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2579317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579317 prefixEnd_2579317 := by exact prefixLift 2579317
  have htrace : WordTrace (prefixWord ++ tailWord_2579317) baseStart_2579317 baseEnd_2579317 := by
    simpa [prefixWord, tailWord_2579317, baseEnd_2579317] using wordTrace_append hprefix tailTrace_2579317
  have hstable : (prefixWord ++ tailWord_2579317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579317).length < 2 ^ (prefixWord ++ tailWord_2579317).sum := by decide
  have hdescent : baseEnd_2579317 < baseStart_2579317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579327 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 1, 2, 3]
def baseStart_2579327 : Nat := 118140960795 + 2579327 * 2 ^ 59
def prefixEnd_2579327 : Nat := 4983230072969 + 3 ^ 40 * 2579327 * 2
def baseEnd_2579327 : Nat := 1324434516119535104950397

theorem tailTrace_2579327 : CollatzResearch.WordTrace tailWord_2579327 prefixEnd_2579327 1324434516119535104950397 := by
  unfold tailWord_2579327
  simp only [CollatzResearch.WordTrace]
  refine ⟨94075784326546267825600235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62717189551030845217066823 94075784326546267825600235)
  ·
    refine ⟨141113676489819401738400353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94075784326546267825600235 141113676489819401738400353)
    ·
      refine ⟨105835257367364551303800265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141113676489819401738400353 105835257367364551303800265)
      ·
        refine ⟨79376443025523413477850199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105835257367364551303800265 79376443025523413477850199)
        ·
          refine ⟨119064664538285120216775299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79376443025523413477850199 119064664538285120216775299)
          ·
            refine ⟨178596996807427680325162949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119064664538285120216775299 178596996807427680325162949)
            ·
              refine ⟨33486936901392690060968053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178596996807427680325162949 33486936901392690060968053)
              ·
                refine ⟨3139400334505564693215755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33486936901392690060968053 3139400334505564693215755)
                ·
                  refine ⟨4709100501758347039823633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139400334505564693215755 4709100501758347039823633)
                  ·
                    refine ⟨3531825376318760279867725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4709100501758347039823633 3531825376318760279867725)
                    ·
                      refine ⟨1324434516119535104950397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3531825376318760279867725 1324434516119535104950397)
                      ·
                        rfl

theorem cell23_2579327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_2579327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579327 prefixEnd_2579327 := by exact prefixLift 2579327
  have htrace : WordTrace (prefixWord ++ tailWord_2579327) baseStart_2579327 baseEnd_2579327 := by
    simpa [prefixWord, tailWord_2579327, baseEnd_2579327] using wordTrace_append hprefix tailTrace_2579327
  have hstable : (prefixWord ++ tailWord_2579327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579327).length < 2 ^ (prefixWord ++ tailWord_2579327).sum := by decide
  have hdescent : baseEnd_2579327 < baseStart_2579327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579354 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2579354 : Nat := 118140960795 + 2579354 * 2 ^ 59
def prefixEnd_2579354 : Nat := 4983230072969 + 3 ^ 40 * 2579354 * 2
def baseEnd_2579354 : Nat := 1324448380097206499312773

theorem tailTrace_2579354 : CollatzResearch.WordTrace tailWord_2579354 prefixEnd_2579354 1324448380097206499312773 := by
  unfold tailWord_2579354
  simp only [CollatzResearch.WordTrace]
  refine ⟨23519192274362112859208279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62717846064965634291222077 23519192274362112859208279)
  ·
    refine ⟨35278788411543169288812419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23519192274362112859208279 35278788411543169288812419)
    ·
      refine ⟨52918182617314753933218629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35278788411543169288812419 52918182617314753933218629)
      ·
        refine ⟨9922159240746516362478493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52918182617314753933218629 9922159240746516362478493)
        ·
          refine ⟨3720809715279943635929435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9922159240746516362478493 3720809715279943635929435)
          ·
            refine ⟨5581214572919915453894153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720809715279943635929435 5581214572919915453894153)
            ·
              refine ⟨4185910929689936590420615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5581214572919915453894153 4185910929689936590420615)
              ·
                refine ⟨6278866394534904885630923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185910929689936590420615 6278866394534904885630923)
                ·
                  refine ⟨9418299591802357328446385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6278866394534904885630923 9418299591802357328446385)
                  ·
                    refine ⟨7063724693851767996334789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9418299591802357328446385 7063724693851767996334789)
                    ·
                      refine ⟨1324448380097206499312773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7063724693851767996334789 1324448380097206499312773)
                      ·
                        rfl

theorem cell23_2579354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2579354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579354 prefixEnd_2579354 := by exact prefixLift 2579354
  have htrace : WordTrace (prefixWord ++ tailWord_2579354) baseStart_2579354 baseEnd_2579354 := by
    simpa [prefixWord, tailWord_2579354, baseEnd_2579354] using wordTrace_append hprefix tailTrace_2579354
  have hstable : (prefixWord ++ tailWord_2579354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579354).length < 2 ^ (prefixWord ++ tailWord_2579354).sum := by decide
  have hdescent : baseEnd_2579354 < baseStart_2579354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579405 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2579405 : Nat := 118140960795 + 2579405 * 2 ^ 59
def prefixEnd_2579405 : Nat := 4983230072969 + 3 ^ 40 * 2579405 * 2
def baseEnd_2579405 : Nat := 1324474567610585799775039

theorem tailTrace_2579405 : CollatzResearch.WordTrace tailWord_2579405 prefixEnd_2579405 1324474567610585799775039 := by
  unfold tailWord_2579405
  simp only [CollatzResearch.WordTrace]
  refine ⟨94078629220263687146939669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62719086146842458097959779 94078629220263687146939669)
  ·
    refine ⟨4409935744699860335012797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94078629220263687146939669 4409935744699860335012797)
    ·
      refine ⟨1653725904262447625629799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4409935744699860335012797 1653725904262447625629799)
      ·
        refine ⟨2480588856393671438444699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1653725904262447625629799 2480588856393671438444699)
        ·
          refine ⟨3720883284590507157667049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480588856393671438444699 3720883284590507157667049)
          ·
            refine ⟨2790662463442880368250287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3720883284590507157667049 2790662463442880368250287)
            ·
              refine ⟨4185993695164320552375431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790662463442880368250287 4185993695164320552375431)
              ·
                refine ⟨6278990542746480828563147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185993695164320552375431 6278990542746480828563147)
                ·
                  refine ⟨9418485814119721242844721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6278990542746480828563147 9418485814119721242844721)
                  ·
                    refine ⟨7063864360589790932133541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9418485814119721242844721 7063864360589790932133541)
                    ·
                      refine ⟨1324474567610585799775039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7063864360589790932133541 1324474567610585799775039)
                      ·
                        rfl

theorem cell23_2579405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2579405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579405 prefixEnd_2579405 := by exact prefixLift 2579405
  have htrace : WordTrace (prefixWord ++ tailWord_2579405) baseStart_2579405 baseEnd_2579405 := by
    simpa [prefixWord, tailWord_2579405, baseEnd_2579405] using wordTrace_append hprefix tailTrace_2579405
  have hstable : (prefixWord ++ tailWord_2579405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579405).length < 2 ^ (prefixWord ++ tailWord_2579405).sum := by decide
  have hdescent : baseEnd_2579405 < baseStart_2579405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579431 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_2579431 : Nat := 118140960795 + 2579431 * 2 ^ 59
def prefixEnd_2579431 : Nat := 4983230072969 + 3 ^ 40 * 2579431 * 2
def baseEnd_2579431 : Nat := 1324487918107602698049919

theorem tailTrace_2579431 : CollatzResearch.WordTrace tailWord_2579431 prefixEnd_2579431 1324487918107602698049919 := by
  unfold tailWord_2579431
  simp only [CollatzResearch.WordTrace]
  refine ⟨94079577518169493587386147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62719718345446329058257431 94079577518169493587386147)
  ·
    refine ⟨141119366277254240381079221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94079577518169493587386147 141119366277254240381079221)
    ·
      refine ⟨13229940588492585035726177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141119366277254240381079221 13229940588492585035726177)
      ·
        refine ⟨9922455441369438776794633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13229940588492585035726177 9922455441369438776794633)
        ·
          refine ⟨7441841581027079082595975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9922455441369438776794633 7441841581027079082595975)
          ·
            refine ⟨11162762371540618623893963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7441841581027079082595975 11162762371540618623893963)
            ·
              refine ⟨16744143557310927935840945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11162762371540618623893963 16744143557310927935840945)
              ·
                refine ⟨12558107667983195951880709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16744143557310927935840945 12558107667983195951880709)
                ·
                  refine ⟨2354645187746849240977633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12558107667983195951880709 2354645187746849240977633)
                  ·
                    refine ⟨1765983890810136930733225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2354645187746849240977633 1765983890810136930733225)
                    ·
                      refine ⟨1324487918107602698049919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1765983890810136930733225 1324487918107602698049919)
                      ·
                        rfl

theorem cell23_2579431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_2579431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579431 prefixEnd_2579431 := by exact prefixLift 2579431
  have htrace : WordTrace (prefixWord ++ tailWord_2579431) baseStart_2579431 baseEnd_2579431 := by
    simpa [prefixWord, tailWord_2579431, baseEnd_2579431] using wordTrace_append hprefix tailTrace_2579431
  have hstable : (prefixWord ++ tailWord_2579431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579431).length < 2 ^ (prefixWord ++ tailWord_2579431).sum := by decide
  have hdescent : baseEnd_2579431 < baseStart_2579431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579504 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 2, 4, 2]
def baseStart_2579504 : Nat := 118140960795 + 2579504 * 2 ^ 59
def prefixEnd_2579504 : Nat := 4983230072969 + 3 ^ 40 * 2579504 * 2
def baseEnd_2579504 : Nat := 1324525402195380912437083

theorem tailTrace_2579504 : CollatzResearch.WordTrace tailWord_2579504 prefixEnd_2579504 1324525402195380912437083 := by
  unfold tailWord_2579504
  simp only [CollatzResearch.WordTrace]
  refine ⟨47041120023452513527396783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62721493364603351369862377 47041120023452513527396783)
  ·
    refine ⟨70561680035178770291095175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47041120023452513527396783 70561680035178770291095175)
    ·
      refine ⟨105842520052768155436642763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70561680035178770291095175 105842520052768155436642763)
      ·
        refine ⟨158763780079152233154964145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105842520052768155436642763 158763780079152233154964145)
        ·
          refine ⟨119072835059364174866223109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158763780079152233154964145 119072835059364174866223109)
          ·
            refine ⟨22326156573630782787416833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119072835059364174866223109 22326156573630782787416833)
            ·
              refine ⟨16744617430223087090562625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22326156573630782787416833 16744617430223087090562625)
              ·
                refine ⟨12558463072667315317921969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16744617430223087090562625 12558463072667315317921969)
                ·
                  refine ⟨9418847304500486488441477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12558463072667315317921969 9418847304500486488441477)
                  ·
                    refine ⟨1766033869593841216582777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9418847304500486488441477 1766033869593841216582777)
                    ·
                      refine ⟨1324525402195380912437083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766033869593841216582777 1324525402195380912437083)
                      ·
                        rfl

theorem cell23_2579504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 4, 2].length) (baseStart_2579504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579504 prefixEnd_2579504 := by exact prefixLift 2579504
  have htrace : WordTrace (prefixWord ++ tailWord_2579504) baseStart_2579504 baseEnd_2579504 := by
    simpa [prefixWord, tailWord_2579504, baseEnd_2579504] using wordTrace_append hprefix tailTrace_2579504
  have hstable : (prefixWord ++ tailWord_2579504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579504).length < 2 ^ (prefixWord ++ tailWord_2579504).sum := by decide
  have hdescent : baseEnd_2579504 < baseStart_2579504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579507 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 3]
def baseStart_2579507 : Nat := 118140960795 + 2579507 * 2 ^ 59
def prefixEnd_2579507 : Nat := 4983230072969 + 3 ^ 40 * 2579507 * 2
def baseEnd_2579507 : Nat := 1324526942637344400699569

theorem tailTrace_2579507 : CollatzResearch.WordTrace tailWord_2579507 prefixEnd_2579507 1324526942637344400699569 := by
  unfold tailWord_2579507
  simp only [CollatzResearch.WordTrace]
  refine ⟨94082349465894158567152775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62721566310596105711435183 94082349465894158567152775)
  ·
    refine ⟨141123524198841237850729163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94082349465894158567152775 141123524198841237850729163)
    ·
      refine ⟨211685286298261856776093745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141123524198841237850729163 211685286298261856776093745)
      ·
        refine ⟨158763964723696392582070309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211685286298261856776093745 158763964723696392582070309)
        ·
          refine ⟨29768243385693073609138183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158763964723696392582070309 29768243385693073609138183)
          ·
            refine ⟨44652365078539610413707275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29768243385693073609138183 44652365078539610413707275)
            ·
              refine ⟨66978547617809415620560913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44652365078539610413707275 66978547617809415620560913)
              ·
                refine ⟨50233910713357061715420685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66978547617809415620560913 50233910713357061715420685)
                ·
                  refine ⟨18837716517508898143282757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50233910713357061715420685 18837716517508898143282757)
                  ·
                    refine ⟨3532071847032918401865517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18837716517508898143282757 3532071847032918401865517)
                    ·
                      refine ⟨1324526942637344400699569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3532071847032918401865517 1324526942637344400699569)
                      ·
                        rfl

theorem cell23_2579507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 3].length) (baseStart_2579507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579507 prefixEnd_2579507 := by exact prefixLift 2579507
  have htrace : WordTrace (prefixWord ++ tailWord_2579507) baseStart_2579507 baseEnd_2579507 := by
    simpa [prefixWord, tailWord_2579507, baseEnd_2579507] using wordTrace_append hprefix tailTrace_2579507
  have hstable : (prefixWord ++ tailWord_2579507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579507).length < 2 ^ (prefixWord ++ tailWord_2579507).sum := by decide
  have hdescent : baseEnd_2579507 < baseStart_2579507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579548 : List Nat := [2, 2, 4, 1, 1, 1, 4, 3, 1, 4]
def baseStart_2579548 : Nat := 118140960795 + 2579548 * 2 ^ 59
def prefixEnd_2579548 : Nat := 4983230072969 + 3 ^ 40 * 2579548 * 2
def baseEnd_2579548 : Nat := 441515998448059580095627

theorem tailTrace_2579548 : CollatzResearch.WordTrace tailWord_2579548 prefixEnd_2579548 441515998448059580095627 := by
  unfold tailWord_2579548
  simp only [CollatzResearch.WordTrace]
  refine ⟨47041922429372811284697649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62722563239163748379596865 47041922429372811284697649)
  ·
    refine ⟨35281441822029608463523237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47041922429372811284697649 35281441822029608463523237)
    ·
      refine ⟨6615270341630551586910607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35281441822029608463523237 6615270341630551586910607)
      ·
        refine ⟨9922905512445827380365911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6615270341630551586910607 9922905512445827380365911)
        ·
          refine ⟨14884358268668741070548867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9922905512445827380365911 14884358268668741070548867)
          ·
            refine ⟨22326537403003111605823301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14884358268668741070548867 22326537403003111605823301)
            ·
              refine ⟨4186225763063083426091869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22326537403003111605823301 4186225763063083426091869)
              ·
                refine ⟨1569834661148656284784451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4186225763063083426091869 1569834661148656284784451)
                ·
                  refine ⟨2354751991722984427176677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569834661148656284784451 2354751991722984427176677)
                  ·
                    refine ⟨441515998448059580095627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2354751991722984427176677 441515998448059580095627)
                    ·
                      rfl

theorem cell23_2579548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_2579548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579548 prefixEnd_2579548 := by exact prefixLift 2579548
  have htrace : WordTrace (prefixWord ++ tailWord_2579548) baseStart_2579548 baseEnd_2579548 := by
    simpa [prefixWord, tailWord_2579548, baseEnd_2579548] using wordTrace_append hprefix tailTrace_2579548
  have hstable : (prefixWord ++ tailWord_2579548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579548).length < 2 ^ (prefixWord ++ tailWord_2579548).sum := by decide
  have hdescent : baseEnd_2579548 < baseStart_2579548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579634 : List Nat := [3, 2, 1, 1, 1, 5, 2, 8]
def baseStart_2579634 : Nat := 118140960795 + 2579634 * 2 ^ 59
def prefixEnd_2579634 : Nat := 4983230072969 + 3 ^ 40 * 2579634 * 2
def baseEnd_2579634 : Nat := 49058968691869089030055

theorem tailTrace_2579634 : CollatzResearch.WordTrace tailWord_2579634 prefixEnd_2579634 49058968691869089030055 := by
  unfold tailWord_2579634
  simp only [CollatzResearch.WordTrace]
  refine ⟨23521745384108514814256489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62724654357622706171350637 23521745384108514814256489)
  ·
    refine ⟨17641309038081386110692367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23521745384108514814256489 17641309038081386110692367)
    ·
      refine ⟨26461963557122079166038551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17641309038081386110692367 26461963557122079166038551)
      ·
        refine ⟨39692945335683118749057827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26461963557122079166038551 39692945335683118749057827)
        ·
          refine ⟨59539418003524678123586741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39692945335683118749057827 59539418003524678123586741)
          ·
            refine ⟨5581820437830438574086257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59539418003524678123586741 5581820437830438574086257)
            ·
              refine ⟨4186365328372828930564693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5581820437830438574086257 4186365328372828930564693)
              ·
                refine ⟨49058968691869089030055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4186365328372828930564693 49058968691869089030055)
                ·
                  rfl

theorem cell23_2579634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 8].length) (baseStart_2579634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579634 prefixEnd_2579634 := by exact prefixLift 2579634
  have htrace : WordTrace (prefixWord ++ tailWord_2579634) baseStart_2579634 baseEnd_2579634 := by
    simpa [prefixWord, tailWord_2579634, baseEnd_2579634] using wordTrace_append hprefix tailTrace_2579634
  have hstable : (prefixWord ++ tailWord_2579634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579634).length < 2 ^ (prefixWord ++ tailWord_2579634).sum := by decide
  have hdescent : baseEnd_2579634 < baseStart_2579634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579657 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_2579657 : Nat := 118140960795 + 2579657 * 2 ^ 59
def prefixEnd_2579657 : Nat := 4983230072969 + 3 ^ 40 * 2579657 * 2
def baseEnd_2579657 : Nat := 1324603964735518813823879

theorem tailTrace_2579657 : CollatzResearch.WordTrace tailWord_2579657 prefixEnd_2579657 1324603964735518813823879 := by
  unfold tailWord_2579657
  simp only [CollatzResearch.WordTrace]
  refine ⟨94087820415350734185113225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62725213610233822790075483 94087820415350734185113225)
  ·
    refine ⟨70565865311513050638834919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94087820415350734185113225 70565865311513050638834919)
    ·
      refine ⟨105848797967269575958252379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70565865311513050638834919 105848797967269575958252379)
      ·
        refine ⟨158773196950904363937378569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105848797967269575958252379 158773196950904363937378569)
        ·
          refine ⟨119079897713178272953033927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158773196950904363937378569 119079897713178272953033927)
          ·
            refine ⟨178619846569767409429550891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119079897713178272953033927 178619846569767409429550891)
            ·
              refine ⟨267929769854651114144326337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178619846569767409429550891 267929769854651114144326337)
              ·
                refine ⟨200947327390988335608244753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267929769854651114144326337 200947327390988335608244753)
                ·
                  refine ⟨150710495543241251706183565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200947327390988335608244753 150710495543241251706183565)
                  ·
                    refine ⟨56516435828715469389818837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 150710495543241251706183565 56516435828715469389818837)
                    ·
                      refine ⟨1324603964735518813823879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56516435828715469389818837 1324603964735518813823879)
                      ·
                        rfl

theorem cell23_2579657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_2579657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579657 prefixEnd_2579657 := by exact prefixLift 2579657
  have htrace : WordTrace (prefixWord ++ tailWord_2579657) baseStart_2579657 baseEnd_2579657 := by
    simpa [prefixWord, tailWord_2579657, baseEnd_2579657] using wordTrace_append hprefix tailTrace_2579657
  have hstable : (prefixWord ++ tailWord_2579657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579657).length < 2 ^ (prefixWord ++ tailWord_2579657).sum := by decide
  have hdescent : baseEnd_2579657 < baseStart_2579657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579667 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 8]
def baseStart_2579667 : Nat := 118140960795 + 2579667 * 2 ^ 59
def prefixEnd_2579667 : Nat := 4983230072969 + 3 ^ 40 * 2579667 * 2
def baseEnd_2579667 : Nat := 1324609099542063774698833

theorem tailTrace_2579667 : CollatzResearch.WordTrace tailWord_2579667 prefixEnd_2579667 1324609099542063774698833 := by
  unfold tailWord_2579667
  simp only [CollatzResearch.WordTrace]
  refine ⟨94088185145314505892977255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62725456763543003928651503 94088185145314505892977255)
  ·
    refine ⟨141132277717971758839465883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94088185145314505892977255 141132277717971758839465883)
    ·
      refine ⟨211698416576957638259198825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141132277717971758839465883 211698416576957638259198825)
      ·
        refine ⟨158773812432718228694399119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211698416576957638259198825 158773812432718228694399119)
        ·
          refine ⟨238160718649077343041598679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158773812432718228694399119 238160718649077343041598679)
          ·
            refine ⟨357241077973616014562398019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238160718649077343041598679 357241077973616014562398019)
            ·
              refine ⟨535861616960424021843597029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357241077973616014562398019 535861616960424021843597029)
              ·
                refine ⟨100474053180079504095674443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535861616960424021843597029 100474053180079504095674443)
                ·
                  refine ⟨150711079770119256143511665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100474053180079504095674443 150711079770119256143511665)
                  ·
                    refine ⟨113033309827589442107633749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150711079770119256143511665 113033309827589442107633749)
                    ·
                      refine ⟨1324609099542063774698833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 113033309827589442107633749 1324609099542063774698833)
                      ·
                        rfl

theorem cell23_2579667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_2579667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579667 prefixEnd_2579667 := by exact prefixLift 2579667
  have htrace : WordTrace (prefixWord ++ tailWord_2579667) baseStart_2579667 baseEnd_2579667 := by
    simpa [prefixWord, tailWord_2579667, baseEnd_2579667] using wordTrace_append hprefix tailTrace_2579667
  have hstable : (prefixWord ++ tailWord_2579667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579667).length < 2 ^ (prefixWord ++ tailWord_2579667).sum := by decide
  have hdescent : baseEnd_2579667 < baseStart_2579667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579684 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_2579684 : Nat := 118140960795 + 2579684 * 2 ^ 59
def prefixEnd_2579684 : Nat := 4983230072969 + 3 ^ 40 * 2579684 * 2
def baseEnd_2579684 : Nat := 1324617828713190208186255

theorem tailTrace_2579684 : CollatzResearch.WordTrace tailWord_2579684 prefixEnd_2579684 1324617828713190208186255 := by
  unfold tailWord_2579684
  simp only [CollatzResearch.WordTrace]
  refine ⟨47044402593126458898173053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62725870124168611864230737 47044402593126458898173053)
  ·
    refine ⟨17641650972422422086814895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47044402593126458898173053 17641650972422422086814895)
    ·
      refine ⟨26462476458633633130222343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17641650972422422086814895 26462476458633633130222343)
      ·
        refine ⟨39693714687950449695333515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26462476458633633130222343 39693714687950449695333515)
        ·
          refine ⟨59540572031925674543000273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39693714687950449695333515 59540572031925674543000273)
          ·
            refine ⟨44655429023944255907250205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59540572031925674543000273 44655429023944255907250205)
            ·
              refine ⟨16745785883979095965218827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44655429023944255907250205 16745785883979095965218827)
              ·
                refine ⟨25118678825968643947828241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16745785883979095965218827 25118678825968643947828241)
                ·
                  refine ⟨18839009119476482960871181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25118678825968643947828241 18839009119476482960871181)
                  ·
                    refine ⟨7064628419803681110326693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18839009119476482960871181 7064628419803681110326693)
                    ·
                      refine ⟨1324617828713190208186255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7064628419803681110326693 1324617828713190208186255)
                      ·
                        rfl

theorem cell23_2579684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_2579684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579684 prefixEnd_2579684 := by exact prefixLift 2579684
  have htrace : WordTrace (prefixWord ++ tailWord_2579684) baseStart_2579684 baseEnd_2579684 := by
    simpa [prefixWord, tailWord_2579684, baseEnd_2579684] using wordTrace_append hprefix tailTrace_2579684
  have hstable : (prefixWord ++ tailWord_2579684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579684).length < 2 ^ (prefixWord ++ tailWord_2579684).sum := by decide
  have hdescent : baseEnd_2579684 < baseStart_2579684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579694 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2579694 : Nat := 118140960795 + 2579694 * 2 ^ 59
def prefixEnd_2579694 : Nat := 4983230072969 + 3 ^ 40 * 2579694 * 2
def baseEnd_2579694 : Nat := 441540987839911723020403

theorem tailTrace_2579694 : CollatzResearch.WordTrace tailWord_2579694 prefixEnd_2579694 441540987839911723020403 := by
  unfold tailWord_2579694
  simp only [CollatzResearch.WordTrace]
  refine ⟨11761146239527086188026267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62726113277477793002806757 11761146239527086188026267)
  ·
    refine ⟨17641719359290629282039401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11761146239527086188026267 17641719359290629282039401)
    ·
      refine ⟨13231289519467971961529551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17641719359290629282039401 13231289519467971961529551)
      ·
        refine ⟨19846934279201957942294327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13231289519467971961529551 19846934279201957942294327)
        ·
          refine ⟨29770401418802936913441491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19846934279201957942294327 29770401418802936913441491)
          ·
            refine ⟨44655602128204405370162237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29770401418802936913441491 44655602128204405370162237)
            ·
              refine ⟨16745850798076652013810839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44655602128204405370162237 16745850798076652013810839)
              ·
                refine ⟨25118776197114978020716259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16745850798076652013810839 25118776197114978020716259)
                ·
                  refine ⟨37678164295672467031074389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25118776197114978020716259 37678164295672467031074389)
                  ·
                    refine ⟨441540987839911723020403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37678164295672467031074389 441540987839911723020403)
                    ·
                      rfl

theorem cell23_2579694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2579694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579694 prefixEnd_2579694 := by exact prefixLift 2579694
  have htrace : WordTrace (prefixWord ++ tailWord_2579694) baseStart_2579694 baseEnd_2579694 := by
    simpa [prefixWord, tailWord_2579694, baseEnd_2579694] using wordTrace_append hprefix tailTrace_2579694
  have hstable : (prefixWord ++ tailWord_2579694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579694).length < 2 ^ (prefixWord ++ tailWord_2579694).sum := by decide
  have hdescent : baseEnd_2579694 < baseStart_2579694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579741 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 7]
def baseStart_2579741 : Nat := 118140960795 + 2579741 * 2 ^ 59
def prefixEnd_2579741 : Nat := 4983230072969 + 3 ^ 40 * 2579741 * 2
def baseEnd_2579741 : Nat := 147183010790055165019277

theorem tailTrace_2579741 : CollatzResearch.WordTrace tailWord_2579741 prefixEnd_2579741 147183010790055165019277 := by
  unfold tailWord_2579741
  simp only [CollatzResearch.WordTrace]
  refine ⟨94090884147046416531171077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62727256098030944354114051 94090884147046416531171077)
  ·
    refine ⟨17642040777571203099594577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94090884147046416531171077 17642040777571203099594577)
    ·
      refine ⟨13231530583178402324695933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17642040777571203099594577 13231530583178402324695933)
      ·
        refine ⟨4961823968691900871760975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13231530583178402324695933 4961823968691900871760975)
        ·
          refine ⟨7442735953037851307641463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961823968691900871760975 7442735953037851307641463)
          ·
            refine ⟨11164103929556776961462195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7442735953037851307641463 11164103929556776961462195)
            ·
              refine ⟨16746155894335165442193293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11164103929556776961462195 16746155894335165442193293)
              ·
                refine ⟨6279808460375687040822485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16746155894335165442193293 6279808460375687040822485)
                ·
                  refine ⟨147183010790055165019277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6279808460375687040822485 147183010790055165019277)
                  ·
                    rfl

theorem cell23_2579741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_2579741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579741 prefixEnd_2579741 := by exact prefixLift 2579741
  have htrace : WordTrace (prefixWord ++ tailWord_2579741) baseStart_2579741 baseEnd_2579741 := by
    simpa [prefixWord, tailWord_2579741, baseEnd_2579741] using wordTrace_append hprefix tailTrace_2579741
  have hstable : (prefixWord ++ tailWord_2579741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579741).length < 2 ^ (prefixWord ++ tailWord_2579741).sum := by decide
  have hdescent : baseEnd_2579741 < baseStart_2579741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579848 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 6]
def baseStart_2579848 : Nat := 118140960795 + 2579848 * 2 ^ 59
def prefixEnd_2579848 : Nat := 4983230072969 + 3 ^ 40 * 2579848 * 2
def baseEnd_2579848 : Nat := 147189115504503062948389

theorem tailTrace_2579848 : CollatzResearch.WordTrace tailWord_2579848 prefixEnd_2579848 147189115504503062948389 := by
  unfold tailWord_2579848
  simp only [CollatzResearch.WordTrace]
  refine ⟨47047393378829386902658099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62729857838439182536877465 47047393378829386902658099)
  ·
    refine ⟨70571090068244080353987149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47047393378829386902658099 70571090068244080353987149)
    ·
      refine ⟨26464158775591530132745181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70571090068244080353987149 26464158775591530132745181)
      ·
        refine ⟨9924059540846823799779443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26464158775591530132745181 9924059540846823799779443)
        ·
          refine ⟨14886089311270235699669165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9924059540846823799779443 14886089311270235699669165)
          ·
            refine ⟨5582283491726338387375937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14886089311270235699669165 5582283491726338387375937)
            ·
              refine ⟨4186712618794753790531953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5582283491726338387375937 4186712618794753790531953)
              ·
                refine ⟨3140034464096065342898965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4186712618794753790531953 3140034464096065342898965)
                ·
                  refine ⟨147189115504503062948389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3140034464096065342898965 147189115504503062948389)
                  ·
                    rfl

theorem cell23_2579848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 6].length) (baseStart_2579848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579848 prefixEnd_2579848 := by exact prefixLift 2579848
  have htrace : WordTrace (prefixWord ++ tailWord_2579848) baseStart_2579848 baseEnd_2579848 := by
    simpa [prefixWord, tailWord_2579848, baseEnd_2579848] using wordTrace_append hprefix tailTrace_2579848
  have hstable : (prefixWord ++ tailWord_2579848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579848).length < 2 ^ (prefixWord ++ tailWord_2579848).sum := by decide
  have hdescent : baseEnd_2579848 < baseStart_2579848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579861 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_2579861 : Nat := 118140960795 + 2579861 * 2 ^ 59
def prefixEnd_2579861 : Nat := 4983230072969 + 3 ^ 40 * 2579861 * 2
def baseEnd_2579861 : Nat := 441569571596345338557647

theorem tailTrace_2579861 : CollatzResearch.WordTrace tailWord_2579861 prefixEnd_2579861 441569571596345338557647 := by
  unfold tailWord_2579861
  simp only [CollatzResearch.WordTrace]
  refine ⟨94095260906611677025539437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62730173937741118017026291 94095260906611677025539437)
  ·
    refine ⟨35285722839979378884577289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94095260906611677025539437 35285722839979378884577289)
    ·
      refine ⟨26464292129984534163432967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35285722839979378884577289 26464292129984534163432967)
      ·
        refine ⟨39696438194976801245149451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26464292129984534163432967 39696438194976801245149451)
        ·
          refine ⟨59544657292465201867724177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39696438194976801245149451 59544657292465201867724177)
          ·
            refine ⟨44658492969348901400793133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59544657292465201867724177 44658492969348901400793133)
            ·
              refine ⟨16746934863505838025297425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44658492969348901400793133 16746934863505838025297425)
              ·
                refine ⟨12560201147629378518973069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16746934863505838025297425 12560201147629378518973069)
                ·
                  refine ⟨4710075430361016944614901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12560201147629378518973069 4710075430361016944614901)
                  ·
                    refine ⟨441569571596345338557647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4710075430361016944614901 441569571596345338557647)
                    ·
                      rfl

theorem cell23_2579861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_2579861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579861 prefixEnd_2579861 := by exact prefixLift 2579861
  have htrace : WordTrace (prefixWord ++ tailWord_2579861) baseStart_2579861 baseEnd_2579861 := by
    simpa [prefixWord, tailWord_2579861, baseEnd_2579861] using wordTrace_append hprefix tailTrace_2579861
  have hstable : (prefixWord ++ tailWord_2579861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579861).length < 2 ^ (prefixWord ++ tailWord_2579861).sum := by decide
  have hdescent : baseEnd_2579861 < baseStart_2579861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579911 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_2579911 : Nat := 118140960795 + 2579911 * 2 ^ 59
def prefixEnd_2579911 : Nat := 4983230072969 + 3 ^ 40 * 2579911 * 2
def baseEnd_2579911 : Nat := 1324734388821760820047711

theorem tailTrace_2579911 : CollatzResearch.WordTrace tailWord_2579911 prefixEnd_2579911 1324734388821760820047711 := by
  unfold tailWord_2579911
  simp only [CollatzResearch.WordTrace]
  refine ⟨94097084556430535564859587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62731389704287023709906391 94097084556430535564859587)
  ·
    refine ⟨141145626834645803347289381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94097084556430535564859587 141145626834645803347289381)
    ·
      refine ⟨26464805031496088127616759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141145626834645803347289381 26464805031496088127616759)
      ·
        refine ⟨39697207547244132191425139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26464805031496088127616759 39697207547244132191425139)
        ·
          refine ⟨59545811320866198287137709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39697207547244132191425139 59545811320866198287137709)
          ·
            refine ⟨22329679245324824357676641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59545811320866198287137709 22329679245324824357676641)
            ·
              refine ⟨16747259433993618268257481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22329679245324824357676641 16747259433993618268257481)
              ·
                refine ⟨12560444575495213701193111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16747259433993618268257481 12560444575495213701193111)
                ·
                  refine ⟨18840666863242820551789667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12560444575495213701193111 18840666863242820551789667)
                  ·
                    refine ⟨28261000294864230827684501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18840666863242820551789667 28261000294864230827684501)
                    ·
                      refine ⟨1324734388821760820047711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28261000294864230827684501 1324734388821760820047711)
                      ·
                        rfl

theorem cell23_2579911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_2579911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579911 prefixEnd_2579911 := by exact prefixLift 2579911
  have htrace : WordTrace (prefixWord ++ tailWord_2579911) baseStart_2579911 baseEnd_2579911 := by
    simpa [prefixWord, tailWord_2579911, baseEnd_2579911] using wordTrace_append hprefix tailTrace_2579911
  have hstable : (prefixWord ++ tailWord_2579911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579911).length < 2 ^ (prefixWord ++ tailWord_2579911).sum := by decide
  have hdescent : baseEnd_2579911 < baseStart_2579911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579915 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 3, 2, 2]
def baseStart_2579915 : Nat := 118140960795 + 2579915 * 2 ^ 59
def prefixEnd_2579915 : Nat := 4983230072969 + 3 ^ 40 * 2579915 * 2
def baseEnd_2579915 : Nat := 1324736442744378804397693

theorem tailTrace_2579915 : CollatzResearch.WordTrace tailWord_2579915 prefixEnd_2579915 1324736442744378804397693 := by
  unfold tailWord_2579915
  simp only [CollatzResearch.WordTrace]
  refine ⟨94097230448416044248005199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62731486965610696165336799 94097230448416044248005199)
  ·
    refine ⟨141145845672624066372007799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94097230448416044248005199 141145845672624066372007799)
    ·
      refine ⟨211718768508936099558011699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141145845672624066372007799 211718768508936099558011699)
      ·
        refine ⟨317578152763404149337017549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211718768508936099558011699 317578152763404149337017549)
        ·
          refine ⟨119091807286276556001381581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317578152763404149337017549 119091807286276556001381581)
          ·
            refine ⟨44659427732353708500518093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119091807286276556001381581 44659427732353708500518093)
            ·
              refine ⟨16747285399632640687694285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44659427732353708500518093 16747285399632640687694285)
              ·
                refine ⟨6280232024862240257885357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16747285399632640687694285 6280232024862240257885357)
                ·
                  refine ⟨2355087009323340096707009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6280232024862240257885357 2355087009323340096707009)
                  ·
                    refine ⟨1766315256992505072530257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2355087009323340096707009 1766315256992505072530257)
                    ·
                      refine ⟨1324736442744378804397693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766315256992505072530257 1324736442744378804397693)
                      ·
                        rfl

theorem cell23_2579915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 2, 2].length) (baseStart_2579915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579915 prefixEnd_2579915 := by exact prefixLift 2579915
  have htrace : WordTrace (prefixWord ++ tailWord_2579915) baseStart_2579915 baseEnd_2579915 := by
    simpa [prefixWord, tailWord_2579915, baseEnd_2579915] using wordTrace_append hprefix tailTrace_2579915
  have hstable : (prefixWord ++ tailWord_2579915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579915).length < 2 ^ (prefixWord ++ tailWord_2579915).sum := by decide
  have hdescent : baseEnd_2579915 < baseStart_2579915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579918 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_2579918 : Nat := 118140960795 + 2579918 * 2 ^ 59
def prefixEnd_2579918 : Nat := 4983230072969 + 3 ^ 40 * 2579918 * 2
def baseEnd_2579918 : Nat := 1324737983186342292660179

theorem tailTrace_2579918 : CollatzResearch.WordTrace tailWord_2579918 prefixEnd_2579918 1324737983186342292660179 := by
  unfold tailWord_2579918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11762167483425646970045551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62731559911603450506909605 11762167483425646970045551)
  ·
    refine ⟨17643251225138470455068327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11762167483425646970045551 17643251225138470455068327)
    ·
      refine ⟨26464876837707705682602491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17643251225138470455068327 26464876837707705682602491)
      ·
        refine ⟨39697315256561558523903737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26464876837707705682602491 39697315256561558523903737)
        ·
          refine ⟨29772986442421168892927803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39697315256561558523903737 29772986442421168892927803)
          ·
            refine ⟨44659479663631753339391705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29772986442421168892927803 44659479663631753339391705)
            ·
              refine ⟨33494609747723815004543779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44659479663631753339391705 33494609747723815004543779)
              ·
                refine ⟨50241914621585722506815669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33494609747723815004543779 50241914621585722506815669)
                ·
                  refine ⟨4710179495773661485013969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50241914621585722506815669 4710179495773661485013969)
                  ·
                    refine ⟨3532634621830246113760477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4710179495773661485013969 3532634621830246113760477)
                    ·
                      refine ⟨1324737983186342292660179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3532634621830246113760477 1324737983186342292660179)
                      ·
                        rfl

theorem cell23_2579918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_2579918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579918 prefixEnd_2579918 := by exact prefixLift 2579918
  have htrace : WordTrace (prefixWord ++ tailWord_2579918) baseStart_2579918 baseEnd_2579918 := by
    simpa [prefixWord, tailWord_2579918, baseEnd_2579918] using wordTrace_append hprefix tailTrace_2579918
  have hstable : (prefixWord ++ tailWord_2579918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579918).length < 2 ^ (prefixWord ++ tailWord_2579918).sum := by decide
  have hdescent : baseEnd_2579918 < baseStart_2579918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579928 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 1, 2, 4]
def baseStart_2579928 : Nat := 118140960795 + 2579928 * 2 ^ 59
def prefixEnd_2579928 : Nat := 4983230072969 + 3 ^ 40 * 2579928 * 2
def baseEnd_2579928 : Nat := 1324743117992887253535133

theorem tailTrace_2579928 : CollatzResearch.WordTrace tailWord_2579928 prefixEnd_2579928 1324743117992887253535133 := by
  unfold tailWord_2579928
  simp only [CollatzResearch.WordTrace]
  refine ⟨47048852298684473734114219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62731803064912631645485625 47048852298684473734114219)
  ·
    refine ⟨70573278448026710601171329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47048852298684473734114219 70573278448026710601171329)
    ·
      refine ⟨52929958836020032950878497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70573278448026710601171329 52929958836020032950878497)
      ·
        refine ⟨39697469127015024713158873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52929958836020032950878497 39697469127015024713158873)
        ·
          refine ⟨29773101845261268534869155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39697469127015024713158873 29773101845261268534869155)
          ·
            refine ⟨44659652767891902802303733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29773101845261268534869155 44659652767891902802303733)
            ·
              refine ⟨4186842446989865887715975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44659652767891902802303733 4186842446989865887715975)
              ·
                refine ⟨6280263670484798831573963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4186842446989865887715975 6280263670484798831573963)
                ·
                  refine ⟨9420395505727198247360945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6280263670484798831573963 9420395505727198247360945)
                  ·
                    refine ⟨7065296629295398685520709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9420395505727198247360945 7065296629295398685520709)
                    ·
                      refine ⟨1324743117992887253535133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7065296629295398685520709 1324743117992887253535133)
                      ·
                        rfl

theorem cell23_2579928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_2579928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579928 prefixEnd_2579928 := by exact prefixLift 2579928
  have htrace : WordTrace (prefixWord ++ tailWord_2579928) baseStart_2579928 baseEnd_2579928 := by
    simpa [prefixWord, tailWord_2579928, baseEnd_2579928] using wordTrace_append hprefix tailTrace_2579928
  have hstable : (prefixWord ++ tailWord_2579928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579928).length < 2 ^ (prefixWord ++ tailWord_2579928).sum := by decide
  have hdescent : baseEnd_2579928 < baseStart_2579928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579931 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 3]
def baseStart_2579931 : Nat := 118140960795 + 2579931 * 2 ^ 59
def prefixEnd_2579931 : Nat := 4983230072969 + 3 ^ 40 * 2579931 * 2
def baseEnd_2579931 : Nat := 1324744658434850741797619

theorem tailTrace_2579931 : CollatzResearch.WordTrace tailWord_2579931 prefixEnd_2579931 1324744658434850741797619 := by
  unfold tailWord_2579931
  simp only [CollatzResearch.WordTrace]
  refine ⟨94097814016358078980587647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62731876010905385987058431 94097814016358078980587647)
  ·
    refine ⟨141146721024537118470881471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94097814016358078980587647 141146721024537118470881471)
    ·
      refine ⟨211720081536805677706322207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141146721024537118470881471 211720081536805677706322207)
      ·
        refine ⟨317580122305208516559483311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211720081536805677706322207 317580122305208516559483311)
        ·
          refine ⟨476370183457812774839224967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317580122305208516559483311 476370183457812774839224967)
          ·
            refine ⟨714555275186719162258837451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476370183457812774839224967 714555275186719162258837451)
            ·
              refine ⟨1071832912780078743388256177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714555275186719162258837451 1071832912780078743388256177)
              ·
                refine ⟨803874684585059057541192133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071832912780078743388256177 803874684585059057541192133)
                ·
                  refine ⟨150726503359698573288973525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803874684585059057541192133 150726503359698573288973525)
                  ·
                    refine ⟨3532652422492935311460317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 150726503359698573288973525 3532652422492935311460317)
                    ·
                      refine ⟨1324744658434850741797619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3532652422492935311460317 1324744658434850741797619)
                      ·
                        rfl

theorem cell23_2579931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 3].length) (baseStart_2579931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579931 prefixEnd_2579931 := by exact prefixLift 2579931
  have htrace : WordTrace (prefixWord ++ tailWord_2579931) baseStart_2579931 baseEnd_2579931 := by
    simpa [prefixWord, tailWord_2579931, baseEnd_2579931] using wordTrace_append hprefix tailTrace_2579931
  have hstable : (prefixWord ++ tailWord_2579931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579931).length < 2 ^ (prefixWord ++ tailWord_2579931).sum := by decide
  have hdescent : baseEnd_2579931 < baseStart_2579931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579935 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 1, 2, 3]
def baseStart_2579935 : Nat := 118140960795 + 2579935 * 2 ^ 59
def prefixEnd_2579935 : Nat := 4983230072969 + 3 ^ 40 * 2579935 * 2
def baseEnd_2579935 : Nat := 1324746712357468726147601

theorem tailTrace_2579935 : CollatzResearch.WordTrace tailWord_2579935 prefixEnd_2579935 1324746712357468726147601 := by
  unfold tailWord_2579935
  simp only [CollatzResearch.WordTrace]
  refine ⟨94097959908343587663733259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62731973272229058442488839 94097959908343587663733259)
  ·
    refine ⟨141146939862515381495599889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94097959908343587663733259 141146939862515381495599889)
    ·
      refine ⟨105860204896886536121699917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141146939862515381495599889 105860204896886536121699917)
      ·
        refine ⟨39697576836332451045637469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105860204896886536121699917 39697576836332451045637469)
        ·
          refine ⟨14886591313624669142114051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39697576836332451045637469 14886591313624669142114051)
          ·
            refine ⟨22329886970437003713171077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14886591313624669142114051 22329886970437003713171077)
            ·
              refine ⟨4186853806956938196219577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22329886970437003713171077 4186853806956938196219577)
              ·
                refine ⟨3140140355217703647164683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4186853806956938196219577 3140140355217703647164683)
                ·
                  refine ⟨4710210532826555470747025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140140355217703647164683 4710210532826555470747025)
                  ·
                    refine ⟨3532657899619916603060269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4710210532826555470747025 3532657899619916603060269)
                    ·
                      refine ⟨1324746712357468726147601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3532657899619916603060269 1324746712357468726147601)
                      ·
                        rfl

theorem cell23_2579935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_2579935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579935 prefixEnd_2579935 := by exact prefixLift 2579935
  have htrace : WordTrace (prefixWord ++ tailWord_2579935) baseStart_2579935 baseEnd_2579935 := by
    simpa [prefixWord, tailWord_2579935, baseEnd_2579935] using wordTrace_append hprefix tailTrace_2579935
  have hstable : (prefixWord ++ tailWord_2579935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579935).length < 2 ^ (prefixWord ++ tailWord_2579935).sum := by decide
  have hdescent : baseEnd_2579935 < baseStart_2579935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579961 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_2579961 : Nat := 118140960795 + 2579961 * 2 ^ 59
def prefixEnd_2579961 : Nat := 4983230072969 + 3 ^ 40 * 2579961 * 2
def baseEnd_2579961 : Nat := 1324760062854485624422481

theorem tailTrace_2579961 : CollatzResearch.WordTrace tailWord_2579961 prefixEnd_2579961 1324760062854485624422481 := by
  unfold tailWord_2579961
  simp only [CollatzResearch.WordTrace]
  refine ⟨94098908206249394104179737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62732605470832929402786491 94098908206249394104179737)
  ·
    refine ⟨70574181154687045578134803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94098908206249394104179737 70574181154687045578134803)
    ·
      refine ⟨105861271732030568367202205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70574181154687045578134803 105861271732030568367202205)
      ·
        refine ⟨39697976899511463137700827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105861271732030568367202205 39697976899511463137700827)
        ·
          refine ⟨59546965349267194706551241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39697976899511463137700827 59546965349267194706551241)
          ·
            refine ⟨44660224011950396029913431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59546965349267194706551241 44660224011950396029913431)
            ·
              refine ⟨66990336017925594044870147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44660224011950396029913431 66990336017925594044870147)
              ·
                refine ⟨100485504026888391067305221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66990336017925594044870147 100485504026888391067305221)
                ·
                  refine ⟨18841032005041573325119729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100485504026888391067305221 18841032005041573325119729)
                  ·
                    refine ⟨14130774003781179993839797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18841032005041573325119729 14130774003781179993839797)
                    ·
                      refine ⟨1324760062854485624422481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14130774003781179993839797 1324760062854485624422481)
                      ·
                        rfl

theorem cell23_2579961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_2579961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579961 prefixEnd_2579961 := by exact prefixLift 2579961
  have htrace : WordTrace (prefixWord ++ tailWord_2579961) baseStart_2579961 baseEnd_2579961 := by
    simpa [prefixWord, tailWord_2579961, baseEnd_2579961] using wordTrace_append hprefix tailTrace_2579961
  have hstable : (prefixWord ++ tailWord_2579961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579961).length < 2 ^ (prefixWord ++ tailWord_2579961).sum := by decide
  have hdescent : baseEnd_2579961 < baseStart_2579961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579965 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_2579965 : Nat := 118140960795 + 2579965 * 2 ^ 59
def prefixEnd_2579965 : Nat := 4983230072969 + 3 ^ 40 * 2579965 * 2
def baseEnd_2579965 : Nat := 1324762116777103608772463

theorem tailTrace_2579965 : CollatzResearch.WordTrace tailWord_2579965 prefixEnd_2579965 1324762116777103608772463 := by
  unfold tailWord_2579965
  simp only [CollatzResearch.WordTrace]
  refine ⟨94099054098234902787325349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62732702732156601858216899 94099054098234902787325349)
  ·
    refine ⟨17643572643419044272623503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94099054098234902787325349 17643572643419044272623503)
    ·
      refine ⟨26465358965128566408935255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17643572643419044272623503 26465358965128566408935255)
      ·
        refine ⟨39698038447692849613402883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26465358965128566408935255 39698038447692849613402883)
        ·
          refine ⟨59547057671539274420104325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39698038447692849613402883 59547057671539274420104325)
          ·
            refine ⟨11165073313413613953769561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59547057671539274420104325 11165073313413613953769561)
            ·
              refine ⟨8373804985060210465327171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11165073313413613953769561 8373804985060210465327171)
              ·
                refine ⟨12560707477590315697990757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8373804985060210465327171 12560707477590315697990757)
                ·
                  refine ⟨2355132652048184193373267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12560707477590315697990757 2355132652048184193373267)
                  ·
                    refine ⟨3532698978072276290059901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2355132652048184193373267 3532698978072276290059901)
                    ·
                      refine ⟨1324762116777103608772463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3532698978072276290059901 1324762116777103608772463)
                      ·
                        rfl

theorem cell23_2579965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_2579965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579965 prefixEnd_2579965 := by exact prefixLift 2579965
  have htrace : WordTrace (prefixWord ++ tailWord_2579965) baseStart_2579965 baseEnd_2579965 := by
    simpa [prefixWord, tailWord_2579965, baseEnd_2579965] using wordTrace_append hprefix tailTrace_2579965
  have hstable : (prefixWord ++ tailWord_2579965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579965).length < 2 ^ (prefixWord ++ tailWord_2579965).sum := by decide
  have hdescent : baseEnd_2579965 < baseStart_2579965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579992 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 3, 3, 2]
def baseStart_2579992 : Nat := 118140960795 + 2579992 * 2 ^ 59
def prefixEnd_2579992 : Nat := 4983230072969 + 3 ^ 40 * 2579992 * 2
def baseEnd_2579992 : Nat := 1324775980754775003134839

theorem tailTrace_2579992 : CollatzResearch.WordTrace tailWord_2579992 prefixEnd_2579992 1324775980754775003134839 := by
  unfold tailWord_2579992
  simp only [CollatzResearch.WordTrace]
  refine ⟨47050019434568543199279115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62733359246091390932372153 47050019434568543199279115)
  ·
    refine ⟨70575029151852814798918673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47050019434568543199279115 70575029151852814798918673)
    ·
      refine ⟨52931271863889611099189005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70575029151852814798918673 52931271863889611099189005)
      ·
        refine ⟨19849226948958604162195877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52931271863889611099189005 19849226948958604162195877)
        ·
          refine ⟨3721730052929738280411727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19849226948958604162195877 3721730052929738280411727)
          ·
            refine ⟨5582595079394607420617591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3721730052929738280411727 5582595079394607420617591)
            ·
              refine ⟨8373892619091911130926387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5582595079394607420617591 8373892619091911130926387)
              ·
                refine ⟨12560838928637866696389581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8373892619091911130926387 12560838928637866696389581)
                ·
                  refine ⟨4710314598239200011146093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12560838928637866696389581 4710314598239200011146093)
                  ·
                    refine ⟨1766367974339700004179785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4710314598239200011146093 1766367974339700004179785)
                    ·
                      refine ⟨1324775980754775003134839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766367974339700004179785 1324775980754775003134839)
                      ·
                        rfl

theorem cell23_2579992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_2579992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2579992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2579992 prefixEnd_2579992 := by exact prefixLift 2579992
  have htrace : WordTrace (prefixWord ++ tailWord_2579992) baseStart_2579992 baseEnd_2579992 := by
    simpa [prefixWord, tailWord_2579992, baseEnd_2579992] using wordTrace_append hprefix tailTrace_2579992
  have hstable : (prefixWord ++ tailWord_2579992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579992).length < 2 ^ (prefixWord ++ tailWord_2579992).sum := by decide
  have hdescent : baseEnd_2579992 < baseStart_2579992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580018 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_2580018 : Nat := 118140960795 + 2580018 * 2 ^ 59
def prefixEnd_2580018 : Nat := 4983230072969 + 3 ^ 40 * 2580018 * 2
def baseEnd_2580018 : Nat := 1324789331251791901409719

theorem tailTrace_2580018 : CollatzResearch.WordTrace tailWord_2580018 prefixEnd_2580018 1324789331251791901409719 := by
  unfold tailWord_2580018
  simp only [CollatzResearch.WordTrace]
  refine ⟨23525246791760723209751177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62733991444695261892669805 23525246791760723209751177)
  ·
    refine ⟨17643935093820542407313383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23525246791760723209751177 17643935093820542407313383)
    ·
      refine ⟨26465902640730813610970075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17643935093820542407313383 26465902640730813610970075)
      ·
        refine ⟨39698853961096220416455113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26465902640730813610970075 39698853961096220416455113)
        ·
          refine ⟨29774140470822165312341335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39698853961096220416455113 29774140470822165312341335)
          ·
            refine ⟨44661210706233247968512003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29774140470822165312341335 44661210706233247968512003)
            ·
              refine ⟨66991816059349871952768005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44661210706233247968512003 66991816059349871952768005)
              ·
                refine ⟨12560965511128100991144001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66991816059349871952768005 12560965511128100991144001)
                ·
                  refine ⟨9420724133346075743358001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12560965511128100991144001 9420724133346075743358001)
                  ·
                    refine ⟨7065543100009556807518501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9420724133346075743358001 7065543100009556807518501)
                    ·
                      refine ⟨1324789331251791901409719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7065543100009556807518501 1324789331251791901409719)
                      ·
                        rfl

theorem cell23_2580018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_2580018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580018 prefixEnd_2580018 := by exact prefixLift 2580018
  have htrace : WordTrace (prefixWord ++ tailWord_2580018) baseStart_2580018 baseEnd_2580018 := by
    simpa [prefixWord, tailWord_2580018, baseEnd_2580018] using wordTrace_append hprefix tailTrace_2580018
  have hstable : (prefixWord ++ tailWord_2580018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580018).length < 2 ^ (prefixWord ++ tailWord_2580018).sum := by decide
  have hdescent : baseEnd_2580018 < baseStart_2580018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580105 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 3, 4]
def baseStart_2580105 : Nat := 118140960795 + 2580105 * 2 ^ 59
def prefixEnd_2580105 : Nat := 4983230072969 + 3 ^ 40 * 2580105 * 2
def baseEnd_2580105 : Nat := 441611334689577687007273

theorem tailTrace_2580105 : CollatzResearch.WordTrace tailWord_2580105 prefixEnd_2580105 441611334689577687007273 := by
  unfold tailWord_2580105
  simp only [CollatzResearch.WordTrace]
  refine ⟨94104160317727706697421769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62736106878485137798281179 94104160317727706697421769)
  ·
    refine ⟨70578120238295780023066327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94104160317727706697421769 70578120238295780023066327)
    ·
      refine ⟨105867180357443670034599491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70578120238295780023066327 105867180357443670034599491)
      ·
        refine ⟨158800770536165505051899237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105867180357443670034599491 158800770536165505051899237)
        ·
          refine ⟨29775144475531032197231107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158800770536165505051899237 29775144475531032197231107)
          ·
            refine ⟨44662716713296548295846661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29775144475531032197231107 44662716713296548295846661)
            ·
              refine ⟨8374259383743102805471249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44662716713296548295846661 8374259383743102805471249)
              ·
                refine ⟨6280694537807327104103437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8374259383743102805471249 6280694537807327104103437)
                ·
                  refine ⟨2355260451677747664038789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6280694537807327104103437 2355260451677747664038789)
                  ·
                    refine ⟨441611334689577687007273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2355260451677747664038789 441611334689577687007273)
                    ·
                      rfl

theorem cell23_2580105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 4].length) (baseStart_2580105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580105 prefixEnd_2580105 := by exact prefixLift 2580105
  have htrace : WordTrace (prefixWord ++ tailWord_2580105) baseStart_2580105 baseEnd_2580105 := by
    simpa [prefixWord, tailWord_2580105, baseEnd_2580105] using wordTrace_append hprefix tailTrace_2580105
  have hstable : (prefixWord ++ tailWord_2580105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580105).length < 2 ^ (prefixWord ++ tailWord_2580105).sum := by decide
  have hdescent : baseEnd_2580105 < baseStart_2580105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580108 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2580108 : Nat := 118140960795 + 2580108 * 2 ^ 59
def prefixEnd_2580108 : Nat := 4983230072969 + 3 ^ 40 * 2580108 * 2
def baseEnd_2580108 : Nat := 1324835544510696549284305

theorem tailTrace_2580108 : CollatzResearch.WordTrace tailWord_2580108 prefixEnd_2580108 1324835544510696549284305 := by
  unfold tailWord_2580108
  simp only [CollatzResearch.WordTrace]
  refine ⟨47052134868358419104890489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62736179824477892139853985 47052134868358419104890489)
  ·
    refine ⟨35289101151268814328667867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47052134868358419104890489 35289101151268814328667867)
    ·
      refine ⟨52933651726903221493001801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35289101151268814328667867 52933651726903221493001801)
      ·
        refine ⟨39700238795177416119751351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52933651726903221493001801 39700238795177416119751351)
        ·
          refine ⟨59550358192766124179627027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39700238795177416119751351 59550358192766124179627027)
          ·
            refine ⟨89325537289149186269440541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59550358192766124179627027 89325537289149186269440541)
            ·
              refine ⟨33497076483430944851040203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89325537289149186269440541 33497076483430944851040203)
              ·
                refine ⟨50245614725146417276560305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33497076483430944851040203 50245614725146417276560305)
                ·
                  refine ⟨37684211043859812957420229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50245614725146417276560305 37684211043859812957420229)
                  ·
                    refine ⟨7065789570723714929516293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37684211043859812957420229 7065789570723714929516293)
                    ·
                      refine ⟨1324835544510696549284305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7065789570723714929516293 1324835544510696549284305)
                      ·
                        rfl

theorem cell23_2580108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2580108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580108 prefixEnd_2580108 := by exact prefixLift 2580108
  have htrace : WordTrace (prefixWord ++ tailWord_2580108) baseStart_2580108 baseEnd_2580108 := by
    simpa [prefixWord, tailWord_2580108, baseEnd_2580108] using wordTrace_append hprefix tailTrace_2580108
  have hstable : (prefixWord ++ tailWord_2580108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580108).length < 2 ^ (prefixWord ++ tailWord_2580108).sum := by decide
  have hdescent : baseEnd_2580108 < baseStart_2580108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580132 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_2580132 : Nat := 118140960795 + 2580132 * 2 ^ 59
def prefixEnd_2580132 : Nat := 4983230072969 + 3 ^ 40 * 2580132 * 2
def baseEnd_2580132 : Nat := 1324847868046404455384195

theorem tailTrace_2580132 : CollatzResearch.WordTrace tailWord_2580132 prefixEnd_2580132 1324847868046404455384195 := by
  unfold tailWord_2580132
  simp only [CollatzResearch.WordTrace]
  refine ⟨47052572544314945154327325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62736763392419926872436433 47052572544314945154327325)
  ·
    refine ⟨17644714704118104432872747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47052572544314945154327325 17644714704118104432872747)
    ·
      refine ⟨26467072056177156649309121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17644714704118104432872747 26467072056177156649309121)
      ·
        refine ⟨19850304042132867486981841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26467072056177156649309121 19850304042132867486981841)
        ·
          refine ⟨14887728031599650615236381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19850304042132867486981841 14887728031599650615236381)
          ·
            refine ⟨5582898011849868980713643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14887728031599650615236381 5582898011849868980713643)
            ·
              refine ⟨8374347017774803471070465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5582898011849868980713643 8374347017774803471070465)
              ·
                refine ⟨6280760263331102603302849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8374347017774803471070465 6280760263331102603302849)
                ·
                  refine ⟨4710570197498326952477137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6280760263331102603302849 4710570197498326952477137)
                  ·
                    refine ⟨3532927648123745214357853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4710570197498326952477137 3532927648123745214357853)
                    ·
                      refine ⟨1324847868046404455384195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3532927648123745214357853 1324847868046404455384195)
                      ·
                        rfl

theorem cell23_2580132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_2580132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580132 prefixEnd_2580132 := by exact prefixLift 2580132
  have htrace : WordTrace (prefixWord ++ tailWord_2580132) baseStart_2580132 baseEnd_2580132 := by
    simpa [prefixWord, tailWord_2580132, baseEnd_2580132] using wordTrace_append hprefix tailTrace_2580132
  have hstable : (prefixWord ++ tailWord_2580132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580132).length < 2 ^ (prefixWord ++ tailWord_2580132).sum := by decide
  have hdescent : baseEnd_2580132 < baseStart_2580132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580155 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 3, 5, 2]
def baseStart_2580155 : Nat := 118140960795 + 2580155 * 2 ^ 59
def prefixEnd_2580155 : Nat := 4983230072969 + 3 ^ 40 * 2580155 * 2
def baseEnd_2580155 : Nat := 1324859678101457865396589

theorem tailTrace_2580155 : CollatzResearch.WordTrace tailWord_2580155 prefixEnd_2580155 1324859678101457865396589 := by
  unfold tailWord_2580155
  simp only [CollatzResearch.WordTrace]
  refine ⟨94105983967546565236741919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62737322645031043491161279 94105983967546565236741919)
  ·
    refine ⟨141158975951319847855112879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94105983967546565236741919 141158975951319847855112879)
    ·
      refine ⟨211738463926979771782669319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141158975951319847855112879 211738463926979771782669319)
      ·
        refine ⟨317607695890469657674003979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211738463926979771782669319 317607695890469657674003979)
        ·
          refine ⟨476411543835704486511005969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317607695890469657674003979 476411543835704486511005969)
          ·
            refine ⟨357308657876778364883254477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476411543835704486511005969 357308657876778364883254477)
            ·
              refine ⟨133990746703791886831220429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357308657876778364883254477 133990746703791886831220429)
              ·
                refine ⟨50246530013921957561707661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133990746703791886831220429 50246530013921957561707661)
                ·
                  refine ⟨18842448755220734085640373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50246530013921957561707661 18842448755220734085640373)
                  ·
                    refine ⟨1766479570801943820528785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18842448755220734085640373 1766479570801943820528785)
                    ·
                      refine ⟨1324859678101457865396589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766479570801943820528785 1324859678101457865396589)
                      ·
                        rfl

theorem cell23_2580155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 5, 2].length) (baseStart_2580155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580155 prefixEnd_2580155 := by exact prefixLift 2580155
  have htrace : WordTrace (prefixWord ++ tailWord_2580155) baseStart_2580155 baseEnd_2580155 := by
    simpa [prefixWord, tailWord_2580155, baseEnd_2580155] using wordTrace_append hprefix tailTrace_2580155
  have hstable : (prefixWord ++ tailWord_2580155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580155).length < 2 ^ (prefixWord ++ tailWord_2580155).sum := by decide
  have hdescent : baseEnd_2580155 < baseStart_2580155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580166 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2580166 : Nat := 118140960795 + 2580166 * 2 ^ 59
def prefixEnd_2580166 : Nat := 4983230072969 + 3 ^ 40 * 2580166 * 2
def baseEnd_2580166 : Nat := 1324865326388657322359039

theorem tailTrace_2580166 : CollatzResearch.WordTrace tailWord_2580166 prefixEnd_2580166 1324865326388657322359039 := by
  unfold tailWord_2580166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940824536578334816106011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62737590113671142743594901 2940824536578334816106011)
  ·
    refine ⟨4411236804867502224159017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2940824536578334816106011 4411236804867502224159017)
    ·
      refine ⟨3308427603650626668119263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4411236804867502224159017 3308427603650626668119263)
      ·
        refine ⟨4962641405475940002178895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3308427603650626668119263 4962641405475940002178895)
        ·
          refine ⟨7443962108213910003268343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4962641405475940002178895 7443962108213910003268343)
          ·
            refine ⟨11165943162320865004902515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7443962108213910003268343 11165943162320865004902515)
            ·
              refine ⟨16748914743481297507353773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11165943162320865004902515 16748914743481297507353773)
              ·
                refine ⟨6280843028805486565257665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16748914743481297507353773 6280843028805486565257665)
                ·
                  refine ⟨4710632271604114923943249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6280843028805486565257665 4710632271604114923943249)
                  ·
                    refine ⟨3532974203703086192957437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4710632271604114923943249 3532974203703086192957437)
                    ·
                      refine ⟨1324865326388657322359039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3532974203703086192957437 1324865326388657322359039)
                      ·
                        rfl

theorem cell23_2580166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2580166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580166 prefixEnd_2580166 := by exact prefixLift 2580166
  have htrace : WordTrace (prefixWord ++ tailWord_2580166) baseStart_2580166 baseEnd_2580166 := by
    simpa [prefixWord, tailWord_2580166, baseEnd_2580166] using wordTrace_append hprefix tailTrace_2580166
  have hstable : (prefixWord ++ tailWord_2580166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580166).length < 2 ^ (prefixWord ++ tailWord_2580166).sum := by decide
  have hdescent : baseEnd_2580166 < baseStart_2580166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580208 : List Nat := [2, 1, 1, 1, 3, 1, 2, 12]
def baseStart_2580208 : Nat := 118140960795 + 2580208 * 2 ^ 59
def prefixEnd_2580208 : Nat := 4983230072969 + 3 ^ 40 * 2580208 * 2
def baseEnd_2580208 : Nat := 49069884910227635482735

theorem tailTrace_2580208 : CollatzResearch.WordTrace tailWord_2580208 prefixEnd_2580208 49069884910227635482735 := by
  unfold tailWord_2580208
  simp only [CollatzResearch.WordTrace]
  refine ⟨47053958518177277644210639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62738611357569703525614185 47053958518177277644210639)
  ·
    refine ⟨70580937777265916466315959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47053958518177277644210639 70580937777265916466315959)
    ·
      refine ⟨105871406665898874699473939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70580937777265916466315959 105871406665898874699473939)
      ·
        refine ⟨158807109998848312049210909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105871406665898874699473939 158807109998848312049210909)
        ·
          refine ⟨59552666249568117018454091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158807109998848312049210909 59552666249568117018454091)
          ·
            refine ⟨89328999374352175527681137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59552666249568117018454091 89328999374352175527681137)
            ·
              refine ⟨66996749530764131645760853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89328999374352175527681137 66996749530764131645760853)
              ·
                refine ⟨49069884910227635482735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 66996749530764131645760853 49069884910227635482735)
                ·
                  rfl

theorem cell23_2580208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 12].length) (baseStart_2580208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580208 prefixEnd_2580208 := by exact prefixLift 2580208
  have htrace : WordTrace (prefixWord ++ tailWord_2580208) baseStart_2580208 baseEnd_2580208 := by
    simpa [prefixWord, tailWord_2580208, baseEnd_2580208] using wordTrace_append hprefix tailTrace_2580208
  have hstable : (prefixWord ++ tailWord_2580208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580208).length < 2 ^ (prefixWord ++ tailWord_2580208).sum := by decide
  have hdescent : baseEnd_2580208 < baseStart_2580208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580215 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_2580215 : Nat := 118140960795 + 2580215 * 2 ^ 59
def prefixEnd_2580215 : Nat := 4983230072969 + 3 ^ 40 * 2580215 * 2
def baseEnd_2580215 : Nat := 1324890486940727630646313

theorem tailTrace_2580215 : CollatzResearch.WordTrace tailWord_2580215 prefixEnd_2580215 1324890486940727630646313 := by
  unfold tailWord_2580215
  simp only [CollatzResearch.WordTrace]
  refine ⟨94108172347329195483926099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62738781564886130322617399 94108172347329195483926099)
  ·
    refine ⟨141162258520993793225889149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94108172347329195483926099 141162258520993793225889149)
    ·
      refine ⟨52935846945372672459708431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141162258520993793225889149 52935846945372672459708431)
      ·
        refine ⟨79403770418059008689562647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52935846945372672459708431 79403770418059008689562647)
        ·
          refine ⟨119105655627088513034343971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79403770418059008689562647 119105655627088513034343971)
          ·
            refine ⟨178658483440632769551515957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119105655627088513034343971 178658483440632769551515957)
            ·
              refine ⟨16749232822559322145454621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178658483440632769551515957 16749232822559322145454621)
              ·
                refine ⟨6280962308459745804545483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16749232822559322145454621 6280962308459745804545483)
                ·
                  refine ⟨9421443462689618706818225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6280962308459745804545483 9421443462689618706818225)
                  ·
                    refine ⟨7066082597017214030113669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9421443462689618706818225 7066082597017214030113669)
                    ·
                      refine ⟨1324890486940727630646313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7066082597017214030113669 1324890486940727630646313)
                      ·
                        rfl

theorem cell23_2580215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_2580215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580215 prefixEnd_2580215 := by exact prefixLift 2580215
  have htrace : WordTrace (prefixWord ++ tailWord_2580215) baseStart_2580215 baseEnd_2580215 := by
    simpa [prefixWord, tailWord_2580215, baseEnd_2580215] using wordTrace_append hprefix tailTrace_2580215
  have hstable : (prefixWord ++ tailWord_2580215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580215).length < 2 ^ (prefixWord ++ tailWord_2580215).sum := by decide
  have hdescent : baseEnd_2580215 < baseStart_2580215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580236 : List Nat := [2, 2, 1, 2, 2, 1, 3, 5, 1, 2, 2]
def baseStart_2580236 : Nat := 118140960795 + 2580236 * 2 ^ 59
def prefixEnd_2580236 : Nat := 4983230072969 + 3 ^ 40 * 2580236 * 2
def baseEnd_2580236 : Nat := 1324901270034472048483717

theorem tailTrace_2580236 : CollatzResearch.WordTrace tailWord_2580236 prefixEnd_2580236 1324901270034472048483717 := by
  unfold tailWord_2580236
  simp only [CollatzResearch.WordTrace]
  refine ⟨47054469140126558035220281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62739292186835410713627041 47054469140126558035220281)
  ·
    refine ⟨35290851855094918526415211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47054469140126558035220281 35290851855094918526415211)
    ·
      refine ⟨52936277782642377789622817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35290851855094918526415211 52936277782642377789622817)
      ·
        refine ⟨39702208336981783342217113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52936277782642377789622817 39702208336981783342217113)
        ·
          refine ⟨29776656252736337506662835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39702208336981783342217113 29776656252736337506662835)
          ·
            refine ⟨44664984379104506259994253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29776656252736337506662835 44664984379104506259994253)
            ·
              refine ⟨16749369142164189847497845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44664984379104506259994253 16749369142164189847497845)
              ·
                refine ⟨1570253357077892798202923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16749369142164189847497845 1570253357077892798202923)
                ·
                  refine ⟨2355380035616839197304385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570253357077892798202923 2355380035616839197304385)
                  ·
                    refine ⟨1766535026712629397978289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2355380035616839197304385 1766535026712629397978289)
                    ·
                      refine ⟨1324901270034472048483717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766535026712629397978289 1324901270034472048483717)
                      ·
                        rfl

theorem cell23_2580236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_2580236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580236 prefixEnd_2580236 := by exact prefixLift 2580236
  have htrace : WordTrace (prefixWord ++ tailWord_2580236) baseStart_2580236 baseEnd_2580236 := by
    simpa [prefixWord, tailWord_2580236, baseEnd_2580236] using wordTrace_append hprefix tailTrace_2580236
  have hstable : (prefixWord ++ tailWord_2580236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580236).length < 2 ^ (prefixWord ++ tailWord_2580236).sum := by decide
  have hdescent : baseEnd_2580236 < baseStart_2580236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580242 : List Nat := [3, 2, 4, 1, 1, 2, 10]
def baseStart_2580242 : Nat := 118140960795 + 2580242 * 2 ^ 59
def prefixEnd_2580242 : Nat := 4983230072969 + 3 ^ 40 * 2580242 * 2
def baseEnd_2580242 : Nat := 16356843838498753395169

theorem tailTrace_2580242 : CollatzResearch.WordTrace tailWord_2580242 prefixEnd_2580242 16356843838498753395169 := by
  unfold tailWord_2580242
  simp only [CollatzResearch.WordTrace]
  refine ⟨23527289279557844773789745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62739438078820919396772653 23527289279557844773789745)
  ·
    refine ⟨17645466959668383580342309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23527289279557844773789745 17645466959668383580342309)
    ·
      refine ⟨3308525054937821921314183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17645466959668383580342309 3308525054937821921314183)
      ·
        refine ⟨4962787582406732881971275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3308525054937821921314183 4962787582406732881971275)
        ·
          refine ⟨7444181373610099322956913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4962787582406732881971275 7444181373610099322956913)
          ·
            refine ⟨5583136030207574492217685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7444181373610099322956913 5583136030207574492217685)
            ·
              refine ⟨16356843838498753395169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5583136030207574492217685 16356843838498753395169)
              ·
                rfl

theorem cell23_2580242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 10].length) (baseStart_2580242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580242 prefixEnd_2580242 := by exact prefixLift 2580242
  have htrace : WordTrace (prefixWord ++ tailWord_2580242) baseStart_2580242 baseEnd_2580242 := by
    simpa [prefixWord, tailWord_2580242, baseEnd_2580242] using wordTrace_append hprefix tailTrace_2580242
  have hstable : (prefixWord ++ tailWord_2580242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580242).length < 2 ^ (prefixWord ++ tailWord_2580242).sum := by decide
  have hdescent : baseEnd_2580242 < baseStart_2580242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580295 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_2580295 : Nat := 118140960795 + 2580295 * 2 ^ 59
def prefixEnd_2580295 : Nat := 4983230072969 + 3 ^ 40 * 2580295 * 2
def baseEnd_2580295 : Nat := 1324931565393087317645945

theorem tailTrace_2580295 : CollatzResearch.WordTrace tailWord_2580295 prefixEnd_2580295 1324931565393087317645945 := by
  unfold tailWord_2580295
  simp only [CollatzResearch.WordTrace]
  refine ⟨94111090187039369146838339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62740726791359579431225559 94111090187039369146838339)
  ·
    refine ⟨141166635280559053720257509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94111090187039369146838339 141166635280559053720257509)
    ·
      refine ⟨26468744115104822572548283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141166635280559053720257509 26468744115104822572548283)
      ·
        refine ⟨39703116172657233858822425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26468744115104822572548283 39703116172657233858822425)
        ·
          refine ⟨29777337129492925394116819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39703116172657233858822425 29777337129492925394116819)
          ·
            refine ⟨44666005694239388091175229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29777337129492925394116819 44666005694239388091175229)
            ·
              refine ⟨16749752135339770534190711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44666005694239388091175229 16749752135339770534190711)
              ·
                refine ⟨25124628203009655801286067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16749752135339770534190711 25124628203009655801286067)
                ·
                  refine ⟨37686942304514483701929101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25124628203009655801286067 37686942304514483701929101)
                  ·
                    refine ⟨14132603364192931388223413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37686942304514483701929101 14132603364192931388223413)
                    ·
                      refine ⟨1324931565393087317645945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14132603364192931388223413 1324931565393087317645945)
                      ·
                        rfl

theorem cell23_2580295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_2580295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580295 prefixEnd_2580295 := by exact prefixLift 2580295
  have htrace : WordTrace (prefixWord ++ tailWord_2580295) baseStart_2580295 baseEnd_2580295 := by
    simpa [prefixWord, tailWord_2580295, baseEnd_2580295] using wordTrace_append hprefix tailTrace_2580295
  have hstable : (prefixWord ++ tailWord_2580295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580295).length < 2 ^ (prefixWord ++ tailWord_2580295).sum := by decide
  have hdescent : baseEnd_2580295 < baseStart_2580295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580330 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_2580330 : Nat := 118140960795 + 2580330 * 2 ^ 59
def prefixEnd_2580330 : Nat := 4983230072969 + 3 ^ 40 * 2580330 * 2
def baseEnd_2580330 : Nat := 1324949537215994680708285

theorem tailTrace_2580330 : CollatzResearch.WordTrace tailWord_2580330 prefixEnd_2580330 1324949537215994680708285 := by
  unfold tailWord_2580330
  simp only [CollatzResearch.WordTrace]
  refine ⟨23528091685478142531090611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62741577827941713416241629 23528091685478142531090611)
  ·
    refine ⟨35292137528217213796635917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23528091685478142531090611 35292137528217213796635917)
    ·
      refine ⟨13234551573081455173738469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35292137528217213796635917 13234551573081455173738469)
      ·
        refine ⟨2481478419952772845075963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13234551573081455173738469 2481478419952772845075963)
        ·
          refine ⟨3722217629929159267613945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481478419952772845075963 3722217629929159267613945)
          ·
            refine ⟨2791663222446869450710459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3722217629929159267613945 2791663222446869450710459)
            ·
              refine ⟨4187494833670304176065689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2791663222446869450710459 4187494833670304176065689)
              ·
                refine ⟨3140621125252728132049267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4187494833670304176065689 3140621125252728132049267)
                ·
                  refine ⟨4710931687879092198073901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140621125252728132049267 4710931687879092198073901)
                  ·
                    refine ⟨1766599382954659574277713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4710931687879092198073901 1766599382954659574277713)
                    ·
                      refine ⟨1324949537215994680708285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766599382954659574277713 1324949537215994680708285)
                      ·
                        rfl

theorem cell23_2580330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_2580330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580330 prefixEnd_2580330 := by exact prefixLift 2580330
  have htrace : WordTrace (prefixWord ++ tailWord_2580330) baseStart_2580330 baseEnd_2580330 := by
    simpa [prefixWord, tailWord_2580330, baseEnd_2580330] using wordTrace_append hprefix tailTrace_2580330
  have hstable : (prefixWord ++ tailWord_2580330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580330).length < 2 ^ (prefixWord ++ tailWord_2580330).sum := by decide
  have hdescent : baseEnd_2580330 < baseStart_2580330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580376 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2580376 : Nat := 118140960795 + 2580376 * 2 ^ 59
def prefixEnd_2580376 : Nat := 4983230072969 + 3 ^ 40 * 2580376 * 2
def baseEnd_2580376 : Nat := 1324973157326101500733073

theorem tailTrace_2580376 : CollatzResearch.WordTrace tailWord_2580376 prefixEnd_2580376 1324973157326101500733073 := by
  unfold tailWord_2580376
  simp only [CollatzResearch.WordTrace]
  refine ⟨47057022249872959990268491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62742696333163946653691321 47057022249872959990268491)
  ·
    refine ⟨70585533374809439985402737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47057022249872959990268491 70585533374809439985402737)
    ·
      refine ⟨52939150031107079989052053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70585533374809439985402737 52939150031107079989052053)
      ·
        refine ⟨2481522657708144374486815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52939150031107079989052053 2481522657708144374486815)
        ·
          refine ⟨3722283986562216561730223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481522657708144374486815 3722283986562216561730223)
          ·
            refine ⟨5583425979843324842595335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722283986562216561730223 5583425979843324842595335)
            ·
              refine ⟨8375138969764987263893003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583425979843324842595335 8375138969764987263893003)
              ·
                refine ⟨12562708454647480895839505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8375138969764987263893003 12562708454647480895839505)
                ·
                  refine ⟨9422031340985610671879629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12562708454647480895839505 9422031340985610671879629)
                  ·
                    refine ⟨3533261752869604001954861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9422031340985610671879629 3533261752869604001954861)
                    ·
                      refine ⟨1324973157326101500733073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3533261752869604001954861 1324973157326101500733073)
                      ·
                        rfl

theorem cell23_2580376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2580376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580376 prefixEnd_2580376 := by exact prefixLift 2580376
  have htrace : WordTrace (prefixWord ++ tailWord_2580376) baseStart_2580376 baseEnd_2580376 := by
    simpa [prefixWord, tailWord_2580376, baseEnd_2580376] using wordTrace_append hprefix tailTrace_2580376
  have hstable : (prefixWord ++ tailWord_2580376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580376).length < 2 ^ (prefixWord ++ tailWord_2580376).sum := by decide
  have hdescent : baseEnd_2580376 < baseStart_2580376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580395 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 6]
def baseStart_2580395 : Nat := 118140960795 + 2580395 * 2 ^ 59
def prefixEnd_2580395 : Nat := 4983230072969 + 3 ^ 40 * 2580395 * 2
def baseEnd_2580395 : Nat := 1324982913458536926395485

theorem tailTrace_2580395 : CollatzResearch.WordTrace tailWord_2580395 prefixEnd_2580395 1324982913458536926395485 := by
  unfold tailWord_2580395
  simp only [CollatzResearch.WordTrace]
  refine ⟨94114737486677086225478639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62743158324451390816985759 94114737486677086225478639)
  ·
    refine ⟨141172106230015629338217959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94114737486677086225478639 141172106230015629338217959)
    ·
      refine ⟨211758159345023444007326939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141172106230015629338217959 211758159345023444007326939)
      ·
        refine ⟨317637239017535166010990409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211758159345023444007326939 317637239017535166010990409)
        ·
          refine ⟨238227929263151374508242807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317637239017535166010990409 238227929263151374508242807)
          ·
            refine ⟨357341893894727061762364211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238227929263151374508242807 357341893894727061762364211)
            ·
              refine ⟨536012840842090592643546317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357341893894727061762364211 536012840842090592643546317)
              ·
                refine ⟨201004815315783972241329869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 536012840842090592643546317 201004815315783972241329869)
                ·
                  refine ⟨75376805743418989590498701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201004815315783972241329869 75376805743418989590498701)
                  ·
                    refine ⟨28266302153782121096437013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75376805743418989590498701 28266302153782121096437013)
                    ·
                      refine ⟨1324982913458536926395485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28266302153782121096437013 1324982913458536926395485)
                      ·
                        rfl

theorem cell23_2580395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_2580395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580395 prefixEnd_2580395 := by exact prefixLift 2580395
  have htrace : WordTrace (prefixWord ++ tailWord_2580395) baseStart_2580395 baseEnd_2580395 := by
    simpa [prefixWord, tailWord_2580395, baseEnd_2580395] using wordTrace_append hprefix tailTrace_2580395
  have hstable : (prefixWord ++ tailWord_2580395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580395).length < 2 ^ (prefixWord ++ tailWord_2580395).sum := by decide
  have hdescent : baseEnd_2580395 < baseStart_2580395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580426 : List Nat := [3, 1, 2, 1, 2, 1, 4, 4, 1, 4]
def baseStart_2580426 : Nat := 118140960795 + 2580426 * 2 ^ 59
def prefixEnd_2580426 : Nat := 4983230072969 + 3 ^ 40 * 2580426 * 2
def baseEnd_2580426 : Nat := 441666277119608768369281

theorem tailTrace_2580426 : CollatzResearch.WordTrace tailWord_2580426 prefixEnd_2580426 441666277119608768369281 := by
  unfold tailWord_2580426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23528967037391194629964283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62743912099709852346571421 23528967037391194629964283)
  ·
    refine ⟨35293450556086791944946425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23528967037391194629964283 35293450556086791944946425)
    ·
      refine ⟨26470087917065093958709819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35293450556086791944946425 26470087917065093958709819)
      ·
        refine ⟨39705131875597640938064729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26470087917065093958709819 39705131875597640938064729)
        ·
          refine ⟨29778848906698230703548547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39705131875597640938064729 29778848906698230703548547)
          ·
            refine ⟨44668273360047346055322821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29778848906698230703548547 44668273360047346055322821)
            ·
              refine ⟨8375301255008877385373029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44668273360047346055322821 8375301255008877385373029)
              ·
                refine ⟨1570368985314164509757443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8375301255008877385373029 1570368985314164509757443)
                ·
                  refine ⟨2355553477971246764636165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570368985314164509757443 2355553477971246764636165)
                  ·
                    refine ⟨441666277119608768369281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2355553477971246764636165 441666277119608768369281)
                    ·
                      rfl

theorem cell23_2580426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_2580426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580426 prefixEnd_2580426 := by exact prefixLift 2580426
  have htrace : WordTrace (prefixWord ++ tailWord_2580426) baseStart_2580426 baseEnd_2580426 := by
    simpa [prefixWord, tailWord_2580426, baseEnd_2580426] using wordTrace_append hprefix tailTrace_2580426
  have hstable : (prefixWord ++ tailWord_2580426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580426).length < 2 ^ (prefixWord ++ tailWord_2580426).sum := by decide
  have hdescent : baseEnd_2580426 < baseStart_2580426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580439 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 6]
def baseStart_2580439 : Nat := 118140960795 + 2580439 * 2 ^ 59
def prefixEnd_2580439 : Nat := 4983230072969 + 3 ^ 40 * 2580439 * 2
def baseEnd_2580439 : Nat := 147222834067481639360587

theorem tailTrace_2580439 : CollatzResearch.WordTrace tailWord_2580439 prefixEnd_2580439 147222834067481639360587 := by
  unfold tailWord_2580439
  simp only [CollatzResearch.WordTrace]
  refine ⟨94116342298517681740080371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62744228199011787826720247 94116342298517681740080371)
  ·
    refine ⟨141174513447776522610120557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94116342298517681740080371 141174513447776522610120557)
    ·
      refine ⟨52940442542916195978795209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141174513447776522610120557 52940442542916195978795209)
      ·
        refine ⟨39705331907187146984096407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52940442542916195978795209 39705331907187146984096407)
        ·
          refine ⟨59557997860780720476144611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39705331907187146984096407 59557997860780720476144611)
          ·
            refine ⟨89336996791171080714216917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59557997860780720476144611 89336996791171080714216917)
            ·
              refine ⟨2093835862293072204239459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 89336996791171080714216917 2093835862293072204239459)
              ·
                refine ⟨3140753793439608306359189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2093835862293072204239459 3140753793439608306359189)
                ·
                  refine ⟨147222834067481639360587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3140753793439608306359189 147222834067481639360587)
                  ·
                    rfl

theorem cell23_2580439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 6].length) (baseStart_2580439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580439 prefixEnd_2580439 := by exact prefixLift 2580439
  have htrace : WordTrace (prefixWord ++ tailWord_2580439) baseStart_2580439 baseEnd_2580439 := by
    simpa [prefixWord, tailWord_2580439, baseEnd_2580439] using wordTrace_append hprefix tailTrace_2580439
  have hstable : (prefixWord ++ tailWord_2580439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580439).length < 2 ^ (prefixWord ++ tailWord_2580439).sum := by decide
  have hdescent : baseEnd_2580439 < baseStart_2580439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580459 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 6, 3, 2]
def baseStart_2580459 : Nat := 118140960795 + 2580459 * 2 ^ 59
def prefixEnd_2580459 : Nat := 4983230072969 + 3 ^ 40 * 2580459 * 2
def baseEnd_2580459 : Nat := 1325015776220424675995191

theorem tailTrace_2580459 : CollatzResearch.WordTrace tailWord_2580459 prefixEnd_2580459 1325015776220424675995191 := by
  unfold tailWord_2580459
  simp only [CollatzResearch.WordTrace]
  refine ⟨94117071758445225155808431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62744714505630150103872287 94117071758445225155808431)
  ·
    refine ⟨141175607637667837733712647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94117071758445225155808431 141175607637667837733712647)
    ·
      refine ⟨211763411456501756600568971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141175607637667837733712647 211763411456501756600568971)
      ·
        refine ⟨317645117184752634900853457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211763411456501756600568971 317645117184752634900853457)
        ·
          refine ⟨238233837888564476175640093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317645117184752634900853457 238233837888564476175640093)
          ·
            refine ⟨89337689208211678565865035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238233837888564476175640093 89337689208211678565865035)
            ·
              refine ⟨134006533812317517848797553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89337689208211678565865035 134006533812317517848797553)
              ·
                refine ⟨100504900359238138386598165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134006533812317517848797553 100504900359238138386598165)
                ·
                  refine ⟨4711167204339287736871789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100504900359238138386598165 4711167204339287736871789)
                  ·
                    refine ⟨1766687701627232901326921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4711167204339287736871789 1766687701627232901326921)
                    ·
                      refine ⟨1325015776220424675995191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766687701627232901326921 1325015776220424675995191)
                      ·
                        rfl

theorem cell23_2580459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 3, 2].length) (baseStart_2580459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580459 prefixEnd_2580459 := by exact prefixLift 2580459
  have htrace : WordTrace (prefixWord ++ tailWord_2580459) baseStart_2580459 baseEnd_2580459 := by
    simpa [prefixWord, tailWord_2580459, baseEnd_2580459] using wordTrace_append hprefix tailTrace_2580459
  have hstable : (prefixWord ++ tailWord_2580459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580459).length < 2 ^ (prefixWord ++ tailWord_2580459).sum := by decide
  have hdescent : baseEnd_2580459 < baseStart_2580459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580476 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 2, 3, 2]
def baseStart_2580476 : Nat := 118140960795 + 2580476 * 2 ^ 59
def prefixEnd_2580476 : Nat := 4983230072969 + 3 ^ 40 * 2580476 * 2
def baseEnd_2580476 : Nat := 1325024505391551109482613

theorem tailTrace_2580476 : CollatzResearch.WordTrace tailWord_2580476 prefixEnd_2580476 1325024505391551109482613 := by
  unfold tailWord_2580476
  simp only [CollatzResearch.WordTrace]
  refine ⟨47058845899691818529588641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62745127866255758039451521 47058845899691818529588641)
  ·
    refine ⟨35294134424768863897191481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47058845899691818529588641 35294134424768863897191481)
    ·
      refine ⟨26470600818576647922893611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35294134424768863897191481 26470600818576647922893611)
      ·
        refine ⟨39705901227864971884340417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26470600818576647922893611 39705901227864971884340417)
        ·
          refine ⟨29779425920898728913255313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39705901227864971884340417 29779425920898728913255313)
          ·
            refine ⟨22334569440674046684941485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29779425920898728913255313 22334569440674046684941485)
            ·
              refine ⟨8375463540252767506853057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22334569440674046684941485 8375463540252767506853057)
              ·
                refine ⟨6281597655189575630139793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8375463540252767506853057 6281597655189575630139793)
                ·
                  refine ⟨4711198241392181722604845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6281597655189575630139793 4711198241392181722604845)
                  ·
                    refine ⟨1766699340522068145976817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4711198241392181722604845 1766699340522068145976817)
                    ·
                      refine ⟨1325024505391551109482613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766699340522068145976817 1325024505391551109482613)
                      ·
                        rfl

theorem cell23_2580476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_2580476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580476 prefixEnd_2580476 := by exact prefixLift 2580476
  have htrace : WordTrace (prefixWord ++ tailWord_2580476) baseStart_2580476 baseEnd_2580476 := by
    simpa [prefixWord, tailWord_2580476, baseEnd_2580476] using wordTrace_append hprefix tailTrace_2580476
  have hstable : (prefixWord ++ tailWord_2580476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580476).length < 2 ^ (prefixWord ++ tailWord_2580476).sum := by decide
  have hdescent : baseEnd_2580476 < baseStart_2580476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580503 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 1, 5]
def baseStart_2580503 : Nat := 118140960795 + 2580503 * 2 ^ 59
def prefixEnd_2580503 : Nat := 4983230072969 + 3 ^ 40 * 2580503 * 2
def baseEnd_2580503 : Nat := 441679456456407501281663

theorem tailTrace_2580503 : CollatzResearch.WordTrace tailWord_2580503 prefixEnd_2580503 441679456456407501281663 := by
  unfold tailWord_2580503
  simp only [CollatzResearch.WordTrace]
  refine ⟨94118676570285820670410163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62745784380190547113606775 94118676570285820670410163)
  ·
    refine ⟨141178014855428731005615245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94118676570285820670410163 141178014855428731005615245)
    ·
      refine ⟨52941755570785774127105717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141178014855428731005615245 52941755570785774127105717)
      ·
        refine ⟨4963289584761166324416161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52941755570785774127105717 4963289584761166324416161)
        ·
          refine ⟨3722467188570874743312121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4963289584761166324416161 3722467188570874743312121)
          ·
            refine ⟨2791850391428156057484091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3722467188570874743312121 2791850391428156057484091)
            ·
              refine ⟨4187775587142234086226137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2791850391428156057484091 4187775587142234086226137)
              ·
                refine ⟨3140831690356675564669603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4187775587142234086226137 3140831690356675564669603)
                ·
                  refine ⟨4711247535535013347004405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140831690356675564669603 4711247535535013347004405)
                  ·
                    refine ⟨441679456456407501281663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4711247535535013347004405 441679456456407501281663)
                    ·
                      rfl

theorem cell23_2580503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_2580503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580503 prefixEnd_2580503 := by exact prefixLift 2580503
  have htrace : WordTrace (prefixWord ++ tailWord_2580503) baseStart_2580503 baseEnd_2580503 := by
    simpa [prefixWord, tailWord_2580503, baseEnd_2580503] using wordTrace_append hprefix tailTrace_2580503
  have hstable : (prefixWord ++ tailWord_2580503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580503).length < 2 ^ (prefixWord ++ tailWord_2580503).sum := by decide
  have hdescent : baseEnd_2580503 < baseStart_2580503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580506 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4]
def baseStart_2580506 : Nat := 118140960795 + 2580506 * 2 ^ 59
def prefixEnd_2580506 : Nat := 4983230072969 + 3 ^ 40 * 2580506 * 2
def baseEnd_2580506 : Nat := 1325039909811185992107475

theorem tailTrace_2580506 : CollatzResearch.WordTrace tailWord_2580506 prefixEnd_2580506 1325039909811185992107475 := by
  unfold tailWord_2580506
  simp only [CollatzResearch.WordTrace]
  refine ⟨23529696497318738045692343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62745857326183301455179581 23529696497318738045692343)
  ·
    refine ⟨35294544745978107068538515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23529696497318738045692343 35294544745978107068538515)
    ·
      refine ⟨52941817118967160602807773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35294544745978107068538515 52941817118967160602807773)
      ·
        refine ⟨19853181419612685226052915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52941817118967160602807773 19853181419612685226052915)
        ·
          refine ⟨29779772129419027839079373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19853181419612685226052915 29779772129419027839079373)
          ·
            refine ⟨11167414548532135439654765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29779772129419027839079373 11167414548532135439654765)
            ·
              refine ⟨4187780455699550789870537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11167414548532135439654765 4187780455699550789870537)
              ·
                refine ⟨3140835341774663092402903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4187780455699550789870537 3140835341774663092402903)
                ·
                  refine ⟨4711253012661994638604355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140835341774663092402903 4711253012661994638604355)
                  ·
                    refine ⟨7066879518992991957906533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4711253012661994638604355 7066879518992991957906533)
                    ·
                      refine ⟨1325039909811185992107475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7066879518992991957906533 1325039909811185992107475)
                      ·
                        rfl

theorem cell23_2580506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_2580506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580506 prefixEnd_2580506 := by exact prefixLift 2580506
  have htrace : WordTrace (prefixWord ++ tailWord_2580506) baseStart_2580506 baseEnd_2580506 := by
    simpa [prefixWord, tailWord_2580506, baseEnd_2580506] using wordTrace_append hprefix tailTrace_2580506
  have hstable : (prefixWord ++ tailWord_2580506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580506).length < 2 ^ (prefixWord ++ tailWord_2580506).sum := by decide
  have hdescent : baseEnd_2580506 < baseStart_2580506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580516 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_2580516 : Nat := 118140960795 + 2580516 * 2 ^ 59
def prefixEnd_2580516 : Nat := 4983230072969 + 3 ^ 40 * 2580516 * 2
def baseEnd_2580516 : Nat := 441681681539243650994143

theorem tailTrace_2580516 : CollatzResearch.WordTrace tailWord_2580516 prefixEnd_2580516 441681681539243650994143 := by
  unfold tailWord_2580516
  simp only [CollatzResearch.WordTrace]
  refine ⟨47059575359619361945316701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62746100479492482593755601 47059575359619361945316701)
  ·
    refine ⟨17647340759857260729493763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47059575359619361945316701 17647340759857260729493763)
    ·
      refine ⟨26471011139785891094240645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17647340759857260729493763 26471011139785891094240645)
      ·
        refine ⟨4963314588709854580170121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26471011139785891094240645 4963314588709854580170121)
        ·
          refine ⟨3722485941532390935127591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4963314588709854580170121 3722485941532390935127591)
          ·
            refine ⟨5583728912298586402691387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722485941532390935127591 5583728912298586402691387)
            ·
              refine ⟨8375593368447879604037081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583728912298586402691387 8375593368447879604037081)
              ·
                refine ⟨6281695026335909703027811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8375593368447879604037081 6281695026335909703027811)
                ·
                  refine ⟨9422542539503864554541717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6281695026335909703027811 9422542539503864554541717)
                  ·
                    refine ⟨441681681539243650994143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9422542539503864554541717 441681681539243650994143)
                    ·
                      rfl

theorem cell23_2580516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_2580516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580516 prefixEnd_2580516 := by exact prefixLift 2580516
  have htrace : WordTrace (prefixWord ++ tailWord_2580516) baseStart_2580516 baseEnd_2580516 := by
    simpa [prefixWord, tailWord_2580516, baseEnd_2580516] using wordTrace_append hprefix tailTrace_2580516
  have hstable : (prefixWord ++ tailWord_2580516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580516).length < 2 ^ (prefixWord ++ tailWord_2580516).sum := by decide
  have hdescent : baseEnd_2580516 < baseStart_2580516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580520 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2580520 : Nat := 118140960795 + 2580520 * 2 ^ 59
def prefixEnd_2580520 : Nat := 4983230072969 + 3 ^ 40 * 2580520 * 2
def baseEnd_2580520 : Nat := 441682366180116312444137

theorem tailTrace_2580520 : CollatzResearch.WordTrace tailWord_2580520 prefixEnd_2580520 441682366180116312444137 := by
  unfold tailWord_2580520
  simp only [CollatzResearch.WordTrace]
  refine ⟨47059648305612116286889507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62746197740816155049186009 47059648305612116286889507)
  ·
    refine ⟨70589472458418174430334261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47059648305612116286889507 70589472458418174430334261)
    ·
      refine ⟨6617763042976703852843837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70589472458418174430334261 6617763042976703852843837)
      ·
        refine ⟨2481661141116263944816439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6617763042976703852843837 2481661141116263944816439)
        ·
          refine ⟨3722491711674395917224659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481661141116263944816439 3722491711674395917224659)
          ·
            refine ⟨5583737567511593875836989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722491711674395917224659 5583737567511593875836989)
            ·
              refine ⟨2093901587816847703438871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5583737567511593875836989 2093901587816847703438871)
              ·
                refine ⟨3140852381725271555158307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2093901587816847703438871 3140852381725271555158307)
                ·
                  refine ⟨4711278572587907332737461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140852381725271555158307 4711278572587907332737461)
                  ·
                    refine ⟨441682366180116312444137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4711278572587907332737461 441682366180116312444137)
                    ·
                      rfl

theorem cell23_2580520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2580520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580520 prefixEnd_2580520 := by exact prefixLift 2580520
  have htrace : WordTrace (prefixWord ++ tailWord_2580520) baseStart_2580520 baseEnd_2580520 := by
    simpa [prefixWord, tailWord_2580520, baseEnd_2580520] using wordTrace_append hprefix tailTrace_2580520
  have hstable : (prefixWord ++ tailWord_2580520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580520).length < 2 ^ (prefixWord ++ tailWord_2580520).sum := by decide
  have hdescent : baseEnd_2580520 < baseStart_2580520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580526 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_2580526 : Nat := 118140960795 + 2580526 * 2 ^ 59
def prefixEnd_2580526 : Nat := 4983230072969 + 3 ^ 40 * 2580526 * 2
def baseEnd_2580526 : Nat := 1325050179424275913857383

theorem tailTrace_2580526 : CollatzResearch.WordTrace tailWord_2580526 prefixEnd_2580526 1325050179424275913857383 := by
  unfold tailWord_2580526
  simp only [CollatzResearch.WordTrace]
  refine ⟨11764939431150311949812179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62746343632801663732331621 11764939431150311949812179)
  ·
    refine ⟨17647409146725467924718269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11764939431150311949812179 17647409146725467924718269)
    ·
      refine ⟨6617778430022050471769351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17647409146725467924718269 6617778430022050471769351)
      ·
        refine ⟨9926667645033075707654027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617778430022050471769351 9926667645033075707654027)
        ·
          refine ⟨14890001467549613561481041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9926667645033075707654027 14890001467549613561481041)
          ·
            refine ⟨11167501100662210171110781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14890001467549613561481041 11167501100662210171110781)
            ·
              refine ⟨4187812912748328814166543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11167501100662210171110781 4187812912748328814166543)
              ·
                refine ⟨6281719369122493221249815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187812912748328814166543 6281719369122493221249815)
                ·
                  refine ⟨9422579053683739831874723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6281719369122493221249815 9422579053683739831874723)
                  ·
                    refine ⟨14133868580525609747812085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9422579053683739831874723 14133868580525609747812085)
                    ·
                      refine ⟨1325050179424275913857383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14133868580525609747812085 1325050179424275913857383)
                      ·
                        rfl

theorem cell23_2580526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_2580526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580526 prefixEnd_2580526 := by exact prefixLift 2580526
  have htrace : WordTrace (prefixWord ++ tailWord_2580526) baseStart_2580526 baseEnd_2580526 := by
    simpa [prefixWord, tailWord_2580526, baseEnd_2580526] using wordTrace_append hprefix tailTrace_2580526
  have hstable : (prefixWord ++ tailWord_2580526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580526).length < 2 ^ (prefixWord ++ tailWord_2580526).sum := by decide
  have hdescent : baseEnd_2580526 < baseStart_2580526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580540 : List Nat := [2, 2, 2, 2, 2, 1, 3, 4, 1, 2, 2]
def baseStart_2580540 : Nat := 118140960795 + 2580540 * 2 ^ 59
def prefixEnd_2580540 : Nat := 4983230072969 + 3 ^ 40 * 2580540 * 2
def baseEnd_2580540 : Nat := 1325057368153438859082319

theorem tailTrace_2580540 : CollatzResearch.WordTrace tailWord_2580540 prefixEnd_2580540 1325057368153438859082319 := by
  unfold tailWord_2580540
  simp only [CollatzResearch.WordTrace]
  refine ⟨47060013035575887994753537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62746684047434517326338049 47060013035575887994753537)
  ·
    refine ⟨35295009776681915996065153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47060013035575887994753537 35295009776681915996065153)
    ·
      refine ⟨26471257332511436997048865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35295009776681915996065153 26471257332511436997048865)
      ·
        refine ⟨19853442999383577747786649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26471257332511436997048865 19853442999383577747786649)
        ·
          refine ⟨14890082249537683310839987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19853442999383577747786649 14890082249537683310839987)
          ·
            refine ⟨22335123374306524966259981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14890082249537683310839987 22335123374306524966259981)
            ·
              refine ⟨8375671265364946862347493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22335123374306524966259981 8375671265364946862347493)
              ·
                refine ⟨1570438362255927536690155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8375671265364946862347493 1570438362255927536690155)
                ·
                  refine ⟨2355657543383891305035233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570438362255927536690155 2355657543383891305035233)
                  ·
                    refine ⟨1766743157537918478776425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2355657543383891305035233 1766743157537918478776425)
                    ·
                      refine ⟨1325057368153438859082319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766743157537918478776425 1325057368153438859082319)
                      ·
                        rfl

theorem cell23_2580540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_2580540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580540 prefixEnd_2580540 := by exact prefixLift 2580540
  have htrace : WordTrace (prefixWord ++ tailWord_2580540) baseStart_2580540 baseEnd_2580540 := by
    simpa [prefixWord, tailWord_2580540, baseEnd_2580540] using wordTrace_append hprefix tailTrace_2580540
  have hstable : (prefixWord ++ tailWord_2580540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580540).length < 2 ^ (prefixWord ++ tailWord_2580540).sum := by decide
  have hdescent : baseEnd_2580540 < baseStart_2580540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580573 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2580573 : Nat := 118140960795 + 2580573 * 2 ^ 59
def prefixEnd_2580573 : Nat := 4983230072969 + 3 ^ 40 * 2580573 * 2
def baseEnd_2580573 : Nat := 1325074313015037229969667

theorem tailTrace_2580573 : CollatzResearch.WordTrace tailWord_2580573 prefixEnd_2580573 1325074313015037229969667 := by
  unfold tailWord_2580573
  simp only [CollatzResearch.WordTrace]
  refine ⟨94121229680032222625458373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62747486453354815083638915 94121229680032222625458373)
  ·
    refine ⟨17647730565006041742273445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94121229680032222625458373 17647730565006041742273445)
    ·
      refine ⟨3308949480938632826676271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17647730565006041742273445 3308949480938632826676271)
      ·
        refine ⟨4963424221407949240014407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3308949480938632826676271 4963424221407949240014407)
        ·
          refine ⟨7445136332111923860021611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4963424221407949240014407 7445136332111923860021611)
          ·
            refine ⟨11167704498167885790032417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7445136332111923860021611 11167704498167885790032417)
            ·
              refine ⟨8375778373625914342524313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11167704498167885790032417 8375778373625914342524313)
              ·
                refine ⟨6281833780219435756893235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8375778373625914342524313 6281833780219435756893235)
                ·
                  refine ⟨9422750670329153635339853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6281833780219435756893235 9422750670329153635339853)
                  ·
                    refine ⟨3533531501373432613252445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9422750670329153635339853 3533531501373432613252445)
                    ·
                      refine ⟨1325074313015037229969667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3533531501373432613252445 1325074313015037229969667)
                      ·
                        rfl

theorem cell23_2580573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2580573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580573 prefixEnd_2580573 := by exact prefixLift 2580573
  have htrace : WordTrace (prefixWord ++ tailWord_2580573) baseStart_2580573 baseEnd_2580573 := by
    simpa [prefixWord, tailWord_2580573, baseEnd_2580573] using wordTrace_append hprefix tailTrace_2580573
  have hstable : (prefixWord ++ tailWord_2580573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580573).length < 2 ^ (prefixWord ++ tailWord_2580573).sum := by decide
  have hdescent : baseEnd_2580573 < baseStart_2580573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580574 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_2580574 : Nat := 118140960795 + 2580574 * 2 ^ 59
def prefixEnd_2580574 : Nat := 4983230072969 + 3 ^ 40 * 2580574 * 2
def baseEnd_2580574 : Nat := 1325074826495691726057163

theorem tailTrace_2580574 : CollatzResearch.WordTrace tailWord_2580574 prefixEnd_2580574 1325074826495691726057163 := by
  unfold tailWord_2580574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11765158269128574974530597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62747510768685733197496517 11765158269128574974530597)
  ·
    refine ⟨2205967175461607807724487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11765158269128574974530597 2205967175461607807724487)
    ·
      refine ⟨3308950763192411711586731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2205967175461607807724487 3308950763192411711586731)
      ·
        refine ⟨4963426144788617567380097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3308950763192411711586731 4963426144788617567380097)
        ·
          refine ⟨3722569608591463175535073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4963426144788617567380097 3722569608591463175535073)
          ·
            refine ⟨2791927206443597381651305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3722569608591463175535073 2791927206443597381651305)
            ·
              refine ⟨2093945404832698036238479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2791927206443597381651305 2093945404832698036238479)
              ·
                refine ⟨3140918107249047054357719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2093945404832698036238479 3140918107249047054357719)
                ·
                  refine ⟨4711377160873570581536579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140918107249047054357719 4711377160873570581536579)
                  ·
                    refine ⟨7067065741310355872304869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4711377160873570581536579 7067065741310355872304869)
                    ·
                      refine ⟨1325074826495691726057163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7067065741310355872304869 1325074826495691726057163)
                      ·
                        rfl

theorem cell23_2580574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_2580574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580574 prefixEnd_2580574 := by exact prefixLift 2580574
  have htrace : WordTrace (prefixWord ++ tailWord_2580574) baseStart_2580574 baseEnd_2580574 := by
    simpa [prefixWord, tailWord_2580574, baseEnd_2580574] using wordTrace_append hprefix tailTrace_2580574
  have hstable : (prefixWord ++ tailWord_2580574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580574).length < 2 ^ (prefixWord ++ tailWord_2580574).sum := by decide
  have hdescent : baseEnd_2580574 < baseStart_2580574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580583 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_2580583 : Nat := 118140960795 + 2580583 * 2 ^ 59
def prefixEnd_2580583 : Nat := 4983230072969 + 3 ^ 40 * 2580583 * 2
def baseEnd_2580583 : Nat := 1325079447821582190844621

theorem tailTrace_2580583 : CollatzResearch.WordTrace tailWord_2580583 prefixEnd_2580583 1325079447821582190844621 := by
  unfold tailWord_2580583
  simp only [CollatzResearch.WordTrace]
  refine ⟨94121594409995994333322403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62747729606663996222214935 94121594409995994333322403)
  ·
    refine ⟨141182391614993991499983605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94121594409995994333322403 141182391614993991499983605)
    ·
      refine ⟨13235849213905686703123463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141182391614993991499983605 13235849213905686703123463)
      ·
        refine ⟨19853773820858530054685195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13235849213905686703123463 19853773820858530054685195)
        ·
          refine ⟨29780660731287795082027793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19853773820858530054685195 29780660731287795082027793)
          ·
            refine ⟨22335495548465846311520845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29780660731287795082027793 22335495548465846311520845)
            ·
              refine ⟨8375810830674692366820317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22335495548465846311520845 8375810830674692366820317)
              ·
                refine ⟨3140929061503009637557619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8375810830674692366820317 3140929061503009637557619)
                ·
                  refine ⟨4711393592254514456336429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140929061503009637557619 4711393592254514456336429)
                  ·
                    refine ⟨1766772597095442921126161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4711393592254514456336429 1766772597095442921126161)
                    ·
                      refine ⟨1325079447821582190844621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766772597095442921126161 1325079447821582190844621)
                      ·
                        rfl

theorem cell23_2580583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_2580583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580583 prefixEnd_2580583 := by exact prefixLift 2580583
  have htrace : WordTrace (prefixWord ++ tailWord_2580583) baseStart_2580583 baseEnd_2580583 := by
    simpa [prefixWord, tailWord_2580583, baseEnd_2580583] using wordTrace_append hprefix tailTrace_2580583
  have hstable : (prefixWord ++ tailWord_2580583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580583).length < 2 ^ (prefixWord ++ tailWord_2580583).sum := by decide
  have hdescent : baseEnd_2580583 < baseStart_2580583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580589 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_2580589 : Nat := 118140960795 + 2580589 * 2 ^ 59
def prefixEnd_2580589 : Nat := 4983230072969 + 3 ^ 40 * 2580589 * 2
def baseEnd_2580589 : Nat := 441694176235169722456531

theorem tailTrace_2580589 : CollatzResearch.WordTrace tailWord_2580589 prefixEnd_2580589 441694176235169722456531 := by
  unfold tailWord_2580589
  simp only [CollatzResearch.WordTrace]
  refine ⟨94121813247974257358040821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62747875498649504905360547 94121813247974257358040821)
  ·
    refine ⟨8823919991997586627316327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94121813247974257358040821 8823919991997586627316327)
    ·
      refine ⟨13235879987996379940974491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8823919991997586627316327 13235879987996379940974491)
      ·
        refine ⟨19853819981994569911461737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13235879987996379940974491 19853819981994569911461737)
        ·
          refine ⟨14890364986495927433596303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19853819981994569911461737 14890364986495927433596303)
          ·
            refine ⟨22335547479743891150394455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14890364986495927433596303 22335547479743891150394455)
            ·
              refine ⟨33503321219615836725591683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22335547479743891150394455 33503321219615836725591683)
              ·
                refine ⟨50254981829423755088387525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33503321219615836725591683 50254981829423755088387525)
                ·
                  refine ⟨9422809093016954079072661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50254981829423755088387525 9422809093016954079072661)
                  ·
                    refine ⟨441694176235169722456531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9422809093016954079072661 441694176235169722456531)
                    ·
                      rfl

theorem cell23_2580589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_2580589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580589 prefixEnd_2580589 := by exact prefixLift 2580589
  have htrace : WordTrace (prefixWord ++ tailWord_2580589) baseStart_2580589 baseEnd_2580589 := by
    simpa [prefixWord, tailWord_2580589, baseEnd_2580589] using wordTrace_append hprefix tailTrace_2580589
  have hstable : (prefixWord ++ tailWord_2580589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580589).length < 2 ^ (prefixWord ++ tailWord_2580589).sum := by decide
  have hdescent : baseEnd_2580589 < baseStart_2580589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580613 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 1, 4, 2]
def baseStart_2580613 : Nat := 118140960795 + 2580613 * 2 ^ 59
def prefixEnd_2580613 : Nat := 4983230072969 + 3 ^ 40 * 2580613 * 2
def baseEnd_2580613 : Nat := 1325094852241217073469483

theorem tailTrace_2580613 : CollatzResearch.WordTrace tailWord_2580613 prefixEnd_2580613 1325094852241217073469483 := by
  unfold tailWord_2580613
  simp only [CollatzResearch.WordTrace]
  refine ⟨94122688599887309456914493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62748459066591539637942995 94122688599887309456914493)
  ·
    refine ⟨35296008224957741046342935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94122688599887309456914493 35296008224957741046342935)
    ·
      refine ⟨52944012337436611569514403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35296008224957741046342935 52944012337436611569514403)
      ·
        refine ⟨79416018506154917354271605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52944012337436611569514403 79416018506154917354271605)
        ·
          refine ⟨7445251734952023501962963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79416018506154917354271605 7445251734952023501962963)
          ·
            refine ⟨11167877602428035252944445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7445251734952023501962963 11167877602428035252944445)
            ·
              refine ⟨4187954100910513219854167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11167877602428035252944445 4187954100910513219854167)
              ·
                refine ⟨6281931151365769829781251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187954100910513219854167 6281931151365769829781251)
                ·
                  refine ⟨9422896727048654744671877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6281931151365769829781251 9422896727048654744671877)
                  ·
                    refine ⟨1766793136321622764625977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9422896727048654744671877 1766793136321622764625977)
                    ·
                      refine ⟨1325094852241217073469483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766793136321622764625977 1325094852241217073469483)
                      ·
                        rfl

theorem cell23_2580613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_2580613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580613 prefixEnd_2580613 := by exact prefixLift 2580613
  have htrace : WordTrace (prefixWord ++ tailWord_2580613) baseStart_2580613 baseEnd_2580613 := by
    simpa [prefixWord, tailWord_2580613, baseEnd_2580613] using wordTrace_append hprefix tailTrace_2580613
  have hstable : (prefixWord ++ tailWord_2580613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580613).length < 2 ^ (prefixWord ++ tailWord_2580613).sum := by decide
  have hdescent : baseEnd_2580613 < baseStart_2580613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580653 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 7]
def baseStart_2580653 : Nat := 118140960795 + 2580653 * 2 ^ 59
def prefixEnd_2580653 : Nat := 4983230072969 + 3 ^ 40 * 2580653 * 2
def baseEnd_2580653 : Nat := 147235043496377435218811

theorem tailTrace_2580653 : CollatzResearch.WordTrace tailWord_2580653 prefixEnd_2580653 147235043496377435218811 := by
  unfold tailWord_2580653
  simp only [CollatzResearch.WordTrace]
  refine ⟨94124147519742396288370613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62749431679828264192247075 94124147519742396288370613)
  ·
    refine ⟨8824138829975849652034745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94124147519742396288370613 8824138829975849652034745)
    ·
      refine ⟨6618104122481887239026059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8824138829975849652034745 6618104122481887239026059)
      ·
        refine ⟨9927156183722830858539089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6618104122481887239026059 9927156183722830858539089)
        ·
          refine ⟨7445367137792123143904317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9927156183722830858539089 7445367137792123143904317)
          ·
            refine ⟨2792012676672046178964119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7445367137792123143904317 2792012676672046178964119)
            ·
              refine ⟨4188019015008069268446179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792012676672046178964119 4188019015008069268446179)
              ·
                refine ⟨6282028522512103902669269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188019015008069268446179 6282028522512103902669269)
                ·
                  refine ⟨147235043496377435218811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6282028522512103902669269 147235043496377435218811)
                  ·
                    rfl

theorem cell23_2580653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_2580653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580653 prefixEnd_2580653 := by exact prefixLift 2580653
  have htrace : WordTrace (prefixWord ++ tailWord_2580653) baseStart_2580653 baseEnd_2580653 := by
    simpa [prefixWord, tailWord_2580653, baseEnd_2580653] using wordTrace_append hprefix tailTrace_2580653
  have hstable : (prefixWord ++ tailWord_2580653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580653).length < 2 ^ (prefixWord ++ tailWord_2580653).sum := by decide
  have hdescent : baseEnd_2580653 < baseStart_2580653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580713 : List Nat := [1, 2, 1, 1, 1, 2, 2, 8, 1, 4]
def baseStart_2580713 : Nat := 118140960795 + 2580713 * 2 ^ 59
def prefixEnd_2580713 : Nat := 4983230072969 + 3 ^ 40 * 2580713 * 2
def baseEnd_2580713 : Nat := 441715400102222227406341

theorem tailTrace_2580713 : CollatzResearch.WordTrace tailWord_2580713 prefixEnd_2580713 441715400102222227406341 := by
  unfold tailWord_2580713
  simp only [CollatzResearch.WordTrace]
  refine ⟨94126335899525026535554793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62750890599683351023703195 94126335899525026535554793)
  ·
    refine ⟨70594751924643769901666095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94126335899525026535554793 70594751924643769901666095)
    ·
      refine ⟨105892127886965654852499143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70594751924643769901666095 105892127886965654852499143)
      ·
        refine ⟨158838191830448482278748715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105892127886965654852499143 158838191830448482278748715)
        ·
          refine ⟨238257287745672723418123073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158838191830448482278748715 238257287745672723418123073)
          ·
            refine ⟨178692965809254542563592305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238257287745672723418123073 178692965809254542563592305)
            ·
              refine ⟨134019724356940906922694229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178692965809254542563592305 134019724356940906922694229)
              ·
                refine ⟨1570543644807901253000323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 134019724356940906922694229 1570543644807901253000323)
                ·
                  refine ⟨2355815467211851879500485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570543644807901253000323 2355815467211851879500485)
                  ·
                    refine ⟨441715400102222227406341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2355815467211851879500485 441715400102222227406341)
                    ·
                      rfl

theorem cell23_2580713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 1, 4].length) (baseStart_2580713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580713 prefixEnd_2580713 := by exact prefixLift 2580713
  have htrace : WordTrace (prefixWord ++ tailWord_2580713) baseStart_2580713 baseEnd_2580713 := by
    simpa [prefixWord, tailWord_2580713, baseEnd_2580713] using wordTrace_append hprefix tailTrace_2580713
  have hstable : (prefixWord ++ tailWord_2580713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580713).length < 2 ^ (prefixWord ++ tailWord_2580713).sum := by decide
  have hdescent : baseEnd_2580713 < baseStart_2580713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580729 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_2580729 : Nat := 118140960795 + 2580729 * 2 ^ 59
def prefixEnd_2580729 : Nat := 4983230072969 + 3 ^ 40 * 2580729 * 2
def baseEnd_2580729 : Nat := 1325154415997138619618949

theorem tailTrace_2580729 : CollatzResearch.WordTrace tailWord_2580729 prefixEnd_2580729 1325154415997138619618949 := by
  unfold tailWord_2580729
  simp only [CollatzResearch.WordTrace]
  refine ⟨94126919467467061268137241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62751279644978040845424827 94126919467467061268137241)
  ·
    refine ⟨70595189600600295951102931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94126919467467061268137241 70595189600600295951102931)
    ·
      refine ⟨105892784400900443926654397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70595189600600295951102931 105892784400900443926654397)
      ·
        refine ⟨39709794150337666472495399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105892784400900443926654397 39709794150337666472495399)
        ·
          refine ⟨59564691225506499708743099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39709794150337666472495399 59564691225506499708743099)
          ·
            refine ⟨89347036838259749563114649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59564691225506499708743099 89347036838259749563114649)
            ·
              refine ⟨67010277628694812172335987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89347036838259749563114649 67010277628694812172335987)
              ·
                refine ⟨100515416443042218258503981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67010277628694812172335987 100515416443042218258503981)
                ·
                  refine ⟨37693281166140831846938993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100515416443042218258503981 37693281166140831846938993)
                  ·
                    refine ⟨28269960874605623885204245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37693281166140831846938993 28269960874605623885204245)
                    ·
                      refine ⟨1325154415997138619618949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28269960874605623885204245 1325154415997138619618949)
                      ·
                        rfl

theorem cell23_2580729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_2580729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580729 prefixEnd_2580729 := by exact prefixLift 2580729
  have htrace : WordTrace (prefixWord ++ tailWord_2580729) baseStart_2580729 baseEnd_2580729 := by
    simpa [prefixWord, tailWord_2580729, baseEnd_2580729] using wordTrace_append hprefix tailTrace_2580729
  have hstable : (prefixWord ++ tailWord_2580729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580729).length < 2 ^ (prefixWord ++ tailWord_2580729).sum := by decide
  have hdescent : baseEnd_2580729 < baseStart_2580729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580763 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 2, 3, 2]
def baseStart_2580763 : Nat := 118140960795 + 2580763 * 2 ^ 59
def prefixEnd_2580763 : Nat := 4983230072969 + 3 ^ 40 * 2580763 * 2
def baseEnd_2580763 : Nat := 1325171874339391486593793

theorem tailTrace_2580763 : CollatzResearch.WordTrace tailWord_2580763 prefixEnd_2580763 1325171874339391486593793 := by
  unfold tailWord_2580763
  simp only [CollatzResearch.WordTrace]
  refine ⟨94128159549343885074874943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62752106366229256716583295 94128159549343885074874943)
  ·
    refine ⟨141192239324015827612312415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94128159549343885074874943 141192239324015827612312415)
    ·
      refine ⟨211788358986023741418468623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141192239324015827612312415 211788358986023741418468623)
      ·
        refine ⟨317682538479035612127702935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211788358986023741418468623 317682538479035612127702935)
        ·
          refine ⟨476523807718553418191554403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317682538479035612127702935 476523807718553418191554403)
          ·
            refine ⟨714785711577830127287331605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476523807718553418191554403 714785711577830127287331605)
            ·
              refine ⟨33505580230210787216593669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 714785711577830127287331605 33505580230210787216593669)
              ·
                refine ⟨6282296293164522603111313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33505580230210787216593669 6282296293164522603111313)
                ·
                  refine ⟨4711722219873391952333485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6282296293164522603111313 4711722219873391952333485)
                  ·
                    refine ⟨1766895832452521982125057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4711722219873391952333485 1766895832452521982125057)
                    ·
                      refine ⟨1325171874339391486593793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766895832452521982125057 1325171874339391486593793)
                      ·
                        rfl

theorem cell23_2580763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 3, 2].length) (baseStart_2580763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580763 prefixEnd_2580763 := by exact prefixLift 2580763
  have htrace : WordTrace (prefixWord ++ tailWord_2580763) baseStart_2580763 baseEnd_2580763 := by
    simpa [prefixWord, tailWord_2580763, baseEnd_2580763] using wordTrace_append hprefix tailTrace_2580763
  have hstable : (prefixWord ++ tailWord_2580763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580763).length < 2 ^ (prefixWord ++ tailWord_2580763).sum := by decide
  have hdescent : baseEnd_2580763 < baseStart_2580763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580770 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_2580770 : Nat := 118140960795 + 2580770 * 2 ^ 59
def prefixEnd_2580770 : Nat := 4983230072969 + 3 ^ 40 * 2580770 * 2
def baseEnd_2580770 : Nat := 1325175468703972959206261

theorem tailTrace_2580770 : CollatzResearch.WordTrace tailWord_2580770 prefixEnd_2580770 1325175468703972959206261 := by
  unfold tailWord_2580770
  simp only [CollatzResearch.WordTrace]
  refine ⟨23532103715079631317594941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62752276573545683513586509 23532103715079631317594941)
  ·
    refine ⟨8824538893154861744098103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23532103715079631317594941 8824538893154861744098103)
    ·
      refine ⟨13236808339732292616147155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8824538893154861744098103 13236808339732292616147155)
      ·
        refine ⟨19855212509598438924220733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13236808339732292616147155 19855212509598438924220733)
        ·
          refine ⟨7445704691099414596582775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19855212509598438924220733 7445704691099414596582775)
          ·
            refine ⟨11168557036649121894874163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7445704691099414596582775 11168557036649121894874163)
            ·
              refine ⟨16752835554973682842311245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11168557036649121894874163 16752835554973682842311245)
              ·
                refine ⟨6282313333115131065866717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16752835554973682842311245 6282313333115131065866717)
                ·
                  refine ⟨2355867499918174149700019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6282313333115131065866717 2355867499918174149700019)
                  ·
                    refine ⟨3533801249877261224550029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2355867499918174149700019 3533801249877261224550029)
                    ·
                      refine ⟨1325175468703972959206261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3533801249877261224550029 1325175468703972959206261)
                      ·
                        rfl

theorem cell23_2580770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_2580770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580770 prefixEnd_2580770 := by exact prefixLift 2580770
  have htrace : WordTrace (prefixWord ++ tailWord_2580770) baseStart_2580770 baseEnd_2580770 := by
    simpa [prefixWord, tailWord_2580770, baseEnd_2580770] using wordTrace_append hprefix tailTrace_2580770
  have hstable : (prefixWord ++ tailWord_2580770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580770).length < 2 ^ (prefixWord ++ tailWord_2580770).sum := by decide
  have hdescent : baseEnd_2580770 < baseStart_2580770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580796 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_2580796 : Nat := 118140960795 + 2580796 * 2 ^ 59
def prefixEnd_2580796 : Nat := 4983230072969 + 3 ^ 40 * 2580796 * 2
def baseEnd_2580796 : Nat := 1325188819200989857481141

theorem tailTrace_2580796 : CollatzResearch.WordTrace tailWord_2580796 prefixEnd_2580796 1325188819200989857481141 := by
  unfold tailWord_2580796
  simp only [CollatzResearch.WordTrace]
  refine ⟨47064681579112165855413121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62752908772149554473884161 47064681579112165855413121)
  ·
    refine ⟨35298511184334124391559841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47064681579112165855413121 35298511184334124391559841)
    ·
      refine ⟨26473883388250593293669881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35298511184334124391559841 26473883388250593293669881)
      ·
        refine ⟨19855412541187944970252411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26473883388250593293669881 19855412541187944970252411)
        ·
          refine ⟨29783118811781917455378617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19855412541187944970252411 29783118811781917455378617)
          ·
            refine ⟨22337339108836438091533963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29783118811781917455378617 22337339108836438091533963)
            ·
              refine ⟨33506008663254657137300945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22337339108836438091533963 33506008663254657137300945)
              ·
                refine ⟨25129506497440992852975709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33506008663254657137300945 25129506497440992852975709)
                ·
                  refine ⟨9423564936540372319865891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25129506497440992852975709 9423564936540372319865891)
                  ·
                    refine ⟨14135347404810558479798837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9423564936540372319865891 14135347404810558479798837)
                    ·
                      refine ⟨1325188819200989857481141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14135347404810558479798837 1325188819200989857481141)
                      ·
                        rfl

theorem cell23_2580796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_2580796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580796 prefixEnd_2580796 := by exact prefixLift 2580796
  have htrace : WordTrace (prefixWord ++ tailWord_2580796) baseStart_2580796 baseEnd_2580796 := by
    simpa [prefixWord, tailWord_2580796, baseEnd_2580796] using wordTrace_append hprefix tailTrace_2580796
  have hstable : (prefixWord ++ tailWord_2580796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580796).length < 2 ^ (prefixWord ++ tailWord_2580796).sum := by decide
  have hdescent : baseEnd_2580796 < baseStart_2580796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580816 : List Nat := [2, 1, 1, 1, 1, 8, 9]
def baseStart_2580816 : Nat := 118140960795 + 2580816 * 2 ^ 59
def prefixEnd_2580816 : Nat := 4983230072969 + 3 ^ 40 * 2580816 * 2
def baseEnd_2580816 : Nat := 16360482577951602212729

theorem tailTrace_2580816 : CollatzResearch.WordTrace tailWord_2580816 prefixEnd_2580816 16360482577951602212729 := by
  unfold tailWord_2580816
  simp only [CollatzResearch.WordTrace]
  refine ⟨47065046309075937563277151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62753395078767916751036201 47065046309075937563277151)
  ·
    refine ⟨70597569463613906344915727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47065046309075937563277151 70597569463613906344915727)
    ·
      refine ⟨105896354195420859517373591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70597569463613906344915727 105896354195420859517373591)
      ·
        refine ⟨158844531293131289276060387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105896354195420859517373591 158844531293131289276060387)
        ·
          refine ⟨238266796939696933914090581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158844531293131289276060387 238266796939696933914090581)
          ·
            refine ⟨2792189026637073444305749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 238266796939696933914090581 2792189026637073444305749)
            ·
              refine ⟨16360482577951602212729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2792189026637073444305749 16360482577951602212729)
              ·
                rfl

theorem cell23_2580816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 9].length) (baseStart_2580816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580816 prefixEnd_2580816 := by exact prefixLift 2580816
  have htrace : WordTrace (prefixWord ++ tailWord_2580816) baseStart_2580816 baseEnd_2580816 := by
    simpa [prefixWord, tailWord_2580816, baseEnd_2580816] using wordTrace_append hprefix tailTrace_2580816
  have hstable : (prefixWord ++ tailWord_2580816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580816).length < 2 ^ (prefixWord ++ tailWord_2580816).sum := by decide
  have hdescent : baseEnd_2580816 < baseStart_2580816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580836 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_2580836 : Nat := 118140960795 + 2580836 * 2 ^ 59
def prefixEnd_2580836 : Nat := 4983230072969 + 3 ^ 40 * 2580836 * 2
def baseEnd_2580836 : Nat := 1325209358427169700980957

theorem tailTrace_2580836 : CollatzResearch.WordTrace tailWord_2580836 prefixEnd_2580836 1325209358427169700980957 := by
  unfold tailWord_2580836
  simp only [CollatzResearch.WordTrace]
  refine ⟨47065411039039709271141181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62753881385386279028188241 47065411039039709271141181)
  ·
    refine ⟨17649529139639890976677943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47065411039039709271141181 17649529139639890976677943)
    ·
      refine ⟨26474293709459836465016915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17649529139639890976677943 26474293709459836465016915)
      ·
        refine ⟨39711440564189754697525373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26474293709459836465016915 39711440564189754697525373)
        ·
          refine ⟨14891790211571158011572015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39711440564189754697525373 14891790211571158011572015)
          ·
            refine ⟨22337685317356737017358023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14891790211571158011572015 22337685317356737017358023)
            ·
              refine ⟨33506527976035105526037035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22337685317356737017358023 33506527976035105526037035)
              ·
                refine ⟨50259791964052658289055553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33506527976035105526037035 50259791964052658289055553)
                ·
                  refine ⟨37694843973039493716791665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50259791964052658289055553 37694843973039493716791665)
                  ·
                    refine ⟨28271132979779620287593749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37694843973039493716791665 28271132979779620287593749)
                    ·
                      refine ⟨1325209358427169700980957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28271132979779620287593749 1325209358427169700980957)
                      ·
                        rfl

theorem cell23_2580836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_2580836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580836 prefixEnd_2580836 := by exact prefixLift 2580836
  have htrace : WordTrace (prefixWord ++ tailWord_2580836) baseStart_2580836 baseEnd_2580836 := by
    simpa [prefixWord, tailWord_2580836, baseEnd_2580836] using wordTrace_append hprefix tailTrace_2580836
  have hstable : (prefixWord ++ tailWord_2580836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580836).length < 2 ^ (prefixWord ++ tailWord_2580836).sum := by decide
  have hdescent : baseEnd_2580836 < baseStart_2580836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580837 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 2, 4]
def baseStart_2580837 : Nat := 118140960795 + 2580837 * 2 ^ 59
def prefixEnd_2580837 : Nat := 4983230072969 + 3 ^ 40 * 2580837 * 2
def baseEnd_2580837 : Nat := 441736623969274732356151

theorem tailTrace_2580837 : CollatzResearch.WordTrace tailWord_2580837 prefixEnd_2580837 441736623969274732356151 := by
  unfold tailWord_2580837
  simp only [CollatzResearch.WordTrace]
  refine ⟨94130858551075795713068765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62753905700717197142045843 94130858551075795713068765)
  ·
    refine ⟨35299071956653423392400787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94130858551075795713068765 35299071956653423392400787)
    ·
      refine ⟨52948607934980135088601181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35299071956653423392400787 52948607934980135088601181)
      ·
        refine ⟨19855727975617550658225443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52948607934980135088601181 19855727975617550658225443)
        ·
          refine ⟨29783591963426325987338165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19855727975617550658225443 29783591963426325987338165)
          ·
            refine ⟨2792211746571218061312953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29783591963426325987338165 2792211746571218061312953)
            ·
              refine ⟨2094158809928413545984715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2792211746571218061312953 2094158809928413545984715)
              ·
                refine ⟨3141238214892620318977073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094158809928413545984715 3141238214892620318977073)
                ·
                  refine ⟨2355928661169465239232805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141238214892620318977073 2355928661169465239232805)
                  ·
                    refine ⟨441736623969274732356151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2355928661169465239232805 441736623969274732356151)
                    ·
                      rfl

theorem cell23_2580837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_2580837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580837 prefixEnd_2580837 := by exact prefixLift 2580837
  have htrace : WordTrace (prefixWord ++ tailWord_2580837) baseStart_2580837 baseEnd_2580837 := by
    simpa [prefixWord, tailWord_2580837, baseEnd_2580837] using wordTrace_append hprefix tailTrace_2580837
  have hstable : (prefixWord ++ tailWord_2580837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580837).length < 2 ^ (prefixWord ++ tailWord_2580837).sum := by decide
  have hdescent : baseEnd_2580837 < baseStart_2580837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580878 : List Nat := [4, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2580878 : Nat := 118140960795 + 2580878 * 2 ^ 59
def prefixEnd_2580878 : Nat := 4983230072969 + 3 ^ 40 * 2580878 * 2
def baseEnd_2580878 : Nat := 1325230924614658536655765

theorem tailTrace_2580878 : CollatzResearch.WordTrace tailWord_2580878 prefixEnd_2580878 1325230924614658536655765 := by
  unfold tailWord_2580878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766544242990907464413911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62754902629284839810207525 11766544242990907464413911)
  ·
    refine ⟨17649816364486361196620867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11766544242990907464413911 17649816364486361196620867)
    ·
      refine ⟨26474724546729541794931301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17649816364486361196620867 26474724546729541794931301)
      ·
        refine ⟨4964010852511789086549619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26474724546729541794931301 4964010852511789086549619)
        ·
          refine ⟨7446016278767683629824429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964010852511789086549619 7446016278767683629824429)
          ·
            refine ⟨2792256104537881361184161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7446016278767683629824429 2792256104537881361184161)
            ·
              refine ⟨2094192078403411020888121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2792256104537881361184161 2094192078403411020888121)
              ·
                refine ⟨1570644058802558265666091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094192078403411020888121 1570644058802558265666091)
                ·
                  refine ⟨2355966088203837398499137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570644058802558265666091 2355966088203837398499137)
                  ·
                    refine ⟨1766974566152878048874353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2355966088203837398499137 1766974566152878048874353)
                    ·
                      refine ⟨1325230924614658536655765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766974566152878048874353 1325230924614658536655765)
                      ·
                        rfl

theorem cell23_2580878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2580878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580878 prefixEnd_2580878 := by exact prefixLift 2580878
  have htrace : WordTrace (prefixWord ++ tailWord_2580878) baseStart_2580878 baseEnd_2580878 := by
    simpa [prefixWord, tailWord_2580878, baseEnd_2580878] using wordTrace_append hprefix tailTrace_2580878
  have hstable : (prefixWord ++ tailWord_2580878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580878).length < 2 ^ (prefixWord ++ tailWord_2580878).sum := by decide
  have hdescent : baseEnd_2580878 < baseStart_2580878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580894 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2580894 : Nat := 118140960795 + 2580894 * 2 ^ 59
def prefixEnd_2580894 : Nat := 4983230072969 + 3 ^ 40 * 2580894 * 2
def baseEnd_2580894 : Nat := 1325239140305130474055691

theorem tailTrace_2580894 : CollatzResearch.WordTrace tailWord_2580894 prefixEnd_2580894 1325239140305130474055691 := by
  unfold tailWord_2580894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766617188983661805986717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62755291674579529631929157 11766617188983661805986717)
  ·
    refine ⟨4412481445868873177245019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11766617188983661805986717 4412481445868873177245019)
    ·
      refine ⟨6618722168803309765867529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4412481445868873177245019 6618722168803309765867529)
      ·
        refine ⟨4964041626602482324400647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6618722168803309765867529 4964041626602482324400647)
        ·
          refine ⟨7446062439903723486600971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964041626602482324400647 7446062439903723486600971)
          ·
            refine ⟨11169093659855585229901457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446062439903723486600971 11169093659855585229901457)
            ·
              refine ⟨8376820244891688922426093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11169093659855585229901457 8376820244891688922426093)
              ·
                refine ⟨3141307591834383345909785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8376820244891688922426093 3141307591834383345909785)
                ·
                  refine ⟨2355980693875787509432339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141307591834383345909785 2355980693875787509432339)
                  ·
                    refine ⟨3533971040813681264148509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2355980693875787509432339 3533971040813681264148509)
                    ·
                      refine ⟨1325239140305130474055691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3533971040813681264148509 1325239140305130474055691)
                      ·
                        rfl

theorem cell23_2580894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2580894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580894 prefixEnd_2580894 := by exact prefixLift 2580894
  have htrace : WordTrace (prefixWord ++ tailWord_2580894) baseStart_2580894 baseEnd_2580894 := by
    simpa [prefixWord, tailWord_2580894, baseEnd_2580894] using wordTrace_append hprefix tailTrace_2580894
  have hstable : (prefixWord ++ tailWord_2580894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580894).length < 2 ^ (prefixWord ++ tailWord_2580894).sum := by decide
  have hdescent : baseEnd_2580894 < baseStart_2580894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580900 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 1, 4, 2]
def baseStart_2580900 : Nat := 118140960795 + 2580900 * 2 ^ 59
def prefixEnd_2580900 : Nat := 4983230072969 + 3 ^ 40 * 2580900 * 2
def baseEnd_2580900 : Nat := 1325242221189057450580663

theorem tailTrace_2580900 : CollatzResearch.WordTrace tailWord_2580900 prefixEnd_2580900 1325242221189057450580663 := by
  unfold tailWord_2580900
  simp only [CollatzResearch.WordTrace]
  refine ⟨47066578174923778736306077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62755437566565038315074769 47066578174923778736306077)
  ·
    refine ⟨17649966815596417026114779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47066578174923778736306077 17649966815596417026114779)
    ·
      refine ⟨26474950223394625539172169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17649966815596417026114779 26474950223394625539172169)
      ·
        refine ⟨19856212667545969154379127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26474950223394625539172169 19856212667545969154379127)
        ·
          refine ⟨29784319001318953731568691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19856212667545969154379127 29784319001318953731568691)
          ·
            refine ⟨44676478501978430597353037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29784319001318953731568691 44676478501978430597353037)
            ·
              refine ⟨16753679438241911474007389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44676478501978430597353037 16753679438241911474007389)
              ·
                refine ⟨6282629789340716802752771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16753679438241911474007389 6282629789340716802752771)
                ·
                  refine ⟨9423944684011075204129157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6282629789340716802752771 9423944684011075204129157)
                  ·
                    refine ⟨1766989628252076600774217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9423944684011075204129157 1766989628252076600774217)
                    ·
                      refine ⟨1325242221189057450580663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1766989628252076600774217 1325242221189057450580663)
                      ·
                        rfl

theorem cell23_2580900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_2580900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580900 prefixEnd_2580900 := by exact prefixLift 2580900
  have htrace : WordTrace (prefixWord ++ tailWord_2580900) baseStart_2580900 baseEnd_2580900 := by
    simpa [prefixWord, tailWord_2580900, baseEnd_2580900] using wordTrace_append hprefix tailTrace_2580900
  have hstable : (prefixWord ++ tailWord_2580900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580900).length < 2 ^ (prefixWord ++ tailWord_2580900).sum := by decide
  have hdescent : baseEnd_2580900 < baseStart_2580900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580940 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 7]
def baseStart_2580940 : Nat := 118140960795 + 2580940 * 2 ^ 59
def prefixEnd_2580940 : Nat := 4983230072969 + 3 ^ 40 * 2580940 * 2
def baseEnd_2580940 : Nat := 147251417823915254897831

theorem tailTrace_2580940 : CollatzResearch.WordTrace tailWord_2580940 prefixEnd_2580940 147251417823915254897831 := by
  unfold tailWord_2580940
  simp only [CollatzResearch.WordTrace]
  refine ⟨47067307634851322152034137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62756410179801762869378849 47067307634851322152034137)
  ·
    refine ⟨35300480726138491614025603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47067307634851322152034137 35300480726138491614025603)
    ·
      refine ⟨52950721089207737421038405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35300480726138491614025603 52950721089207737421038405)
      ·
        refine ⟨9928260204226450766444701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52950721089207737421038405 9928260204226450766444701)
        ·
          refine ⟨3723097576584919037416763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9928260204226450766444701 3723097576584919037416763)
          ·
            refine ⟨5584646364877378556125145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723097576584919037416763 5584646364877378556125145)
            ·
              refine ⟨4188484773658033917093859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5584646364877378556125145 4188484773658033917093859)
              ·
                refine ⟨6282727160487050875640789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188484773658033917093859 6282727160487050875640789)
                ·
                  refine ⟨147251417823915254897831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6282727160487050875640789 147251417823915254897831)
                  ·
                    rfl

theorem cell23_2580940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_2580940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580940 prefixEnd_2580940 := by exact prefixLift 2580940
  have htrace : WordTrace (prefixWord ++ tailWord_2580940) baseStart_2580940 baseEnd_2580940 := by
    simpa [prefixWord, tailWord_2580940, baseEnd_2580940] using wordTrace_append hprefix tailTrace_2580940
  have hstable : (prefixWord ++ tailWord_2580940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580940).length < 2 ^ (prefixWord ++ tailWord_2580940).sum := by decide
  have hdescent : baseEnd_2580940 < baseStart_2580940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581027 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 3]
def baseStart_2581027 : Nat := 118140960795 + 2581027 * 2 ^ 59
def prefixEnd_2581027 : Nat := 4983230072969 + 3 ^ 40 * 2581027 * 2
def baseEnd_2581027 : Nat := 1325307433232178453692579

theorem tailTrace_2581027 : CollatzResearch.WordTrace tailWord_2581027 prefixEnd_2581027 1325307433232178453692579 := by
  unfold tailWord_2581027
  simp only [CollatzResearch.WordTrace]
  refine ⟨94137788420387458162485335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62758525613591638774990223 94137788420387458162485335)
  ·
    refine ⟨141206682630581187243728003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94137788420387458162485335 141206682630581187243728003)
    ·
      refine ⟨211810023945871780865592005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141206682630581187243728003 211810023945871780865592005)
      ·
        refine ⟨39714379489850958912298501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211810023945871780865592005 39714379489850958912298501)
        ·
          refine ⟨7446446154347054796055969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39714379489850958912298501 7446446154347054796055969)
          ·
            refine ⟨5584834615760291097041977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7446446154347054796055969 5584834615760291097041977)
            ·
              refine ⟨4188625961820218322781483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5584834615760291097041977 4188625961820218322781483)
              ·
                refine ⟨6282938942730327484172225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188625961820218322781483 6282938942730327484172225)
                ·
                  refine ⟨4712204207047745613129169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6282938942730327484172225 4712204207047745613129169)
                  ·
                    refine ⟨3534153155285809209846877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4712204207047745613129169 3534153155285809209846877)
                    ·
                      refine ⟨1325307433232178453692579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3534153155285809209846877 1325307433232178453692579)
                      ·
                        rfl

theorem cell23_2581027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_2581027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581027 prefixEnd_2581027 := by exact prefixLift 2581027
  have htrace : WordTrace (prefixWord ++ tailWord_2581027) baseStart_2581027 baseEnd_2581027 := by
    simpa [prefixWord, tailWord_2581027, baseEnd_2581027] using wordTrace_append hprefix tailTrace_2581027
  have hstable : (prefixWord ++ tailWord_2581027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581027).length < 2 ^ (prefixWord ++ tailWord_2581027).sum := by decide
  have hdescent : baseEnd_2581027 < baseStart_2581027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581080 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2581080 : Nat := 118140960795 + 2581080 * 2 ^ 59
def prefixEnd_2581080 : Nat := 4983230072969 + 3 ^ 40 * 2581080 * 2
def baseEnd_2581080 : Nat := 1325334647706866746329835

theorem tailTrace_2581080 : CollatzResearch.WordTrace tailWord_2581080 prefixEnd_2581080 1325334647706866746329835 := by
  unfold tailWord_2581080
  simp only [CollatzResearch.WordTrace]
  refine ⟨47069860744597724107082347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62759814326130298809443129 47069860744597724107082347)
  ·
    refine ⟨70604791116896586160623521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47069860744597724107082347 70604791116896586160623521)
    ·
      refine ⟨52953593337672439620467641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70604791116896586160623521 52953593337672439620467641)
      ·
        refine ⟨39715195003254329715350731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52953593337672439620467641 39715195003254329715350731)
        ·
          refine ⟨59572792504881494573026097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39715195003254329715350731 59572792504881494573026097)
          ·
            refine ⟨44679594378661120929769573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59572792504881494573026097 44679594378661120929769573)
            ·
              refine ⟨8377423945998960174331795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44679594378661120929769573 8377423945998960174331795)
              ·
                refine ⟨12566135918998440261497693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8377423945998960174331795 12566135918998440261497693)
                ·
                  refine ⟨4712300969624415098061635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12566135918998440261497693 4712300969624415098061635)
                  ·
                    refine ⟨7068451454436622647092453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4712300969624415098061635 7068451454436622647092453)
                    ·
                      refine ⟨1325334647706866746329835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7068451454436622647092453 1325334647706866746329835)
                      ·
                        rfl

theorem cell23_2581080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2581080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581080 prefixEnd_2581080 := by exact prefixLift 2581080
  have htrace : WordTrace (prefixWord ++ tailWord_2581080) baseStart_2581080 baseEnd_2581080 := by
    simpa [prefixWord, tailWord_2581080, baseEnd_2581080] using wordTrace_append hprefix tailTrace_2581080
  have hstable : (prefixWord ++ tailWord_2581080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581080).length < 2 ^ (prefixWord ++ tailWord_2581080).sum := by decide
  have hdescent : baseEnd_2581080 < baseStart_2581080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581084 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_2581084 : Nat := 118140960795 + 2581084 * 2 ^ 59
def prefixEnd_2581084 : Nat := 4983230072969 + 3 ^ 40 * 2581084 * 2
def baseEnd_2581084 : Nat := 1325336701629484730679817

theorem tailTrace_2581084 : CollatzResearch.WordTrace tailWord_2581084 prefixEnd_2581084 1325336701629484730679817 := by
  unfold tailWord_2581084
  simp only [CollatzResearch.WordTrace]
  refine ⟨47069933690590478448655153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62759911587453971264873537 47069933690590478448655153)
  ·
    refine ⟨35302450267942858836491365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47069933690590478448655153 35302450267942858836491365)
    ·
      refine ⟨6619209425239286031842131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35302450267942858836491365 6619209425239286031842131)
      ·
        refine ⟨9928814137858929047763197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6619209425239286031842131 9928814137858929047763197)
        ·
          refine ⟨3723305301697098392911199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9928814137858929047763197 3723305301697098392911199)
          ·
            refine ⟨5584957952545647589366799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723305301697098392911199 5584957952545647589366799)
            ·
              refine ⟨8377436928818471384050199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5584957952545647589366799 8377436928818471384050199)
              ·
                refine ⟨12566155393227707076075299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8377436928818471384050199 12566155393227707076075299)
                ·
                  refine ⟨18849233089841560614112949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12566155393227707076075299 18849233089841560614112949)
                  ·
                    refine ⟨1767115602172646307573089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18849233089841560614112949 1767115602172646307573089)
                    ·
                      refine ⟨1325336701629484730679817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767115602172646307573089 1325336701629484730679817)
                      ·
                        rfl

theorem cell23_2581084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_2581084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581084 prefixEnd_2581084 := by exact prefixLift 2581084
  have htrace : WordTrace (prefixWord ++ tailWord_2581084) baseStart_2581084 baseEnd_2581084 := by
    simpa [prefixWord, tailWord_2581084, baseEnd_2581084] using wordTrace_append hprefix tailTrace_2581084
  have hstable : (prefixWord ++ tailWord_2581084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581084).length < 2 ^ (prefixWord ++ tailWord_2581084).sum := by decide
  have hdescent : baseEnd_2581084 < baseStart_2581084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581097 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 7, 2, 2]
def baseStart_2581097 : Nat := 118140960795 + 2581097 * 2 ^ 59
def prefixEnd_2581097 : Nat := 4983230072969 + 3 ^ 40 * 2581097 * 2
def baseEnd_2581097 : Nat := 1325343376877993179817257

theorem tailTrace_2581097 : CollatzResearch.WordTrace tailWord_2581097 prefixEnd_2581097 1325343376877993179817257 := by
  unfold tailWord_2581097
  simp only [CollatzResearch.WordTrace]
  refine ⟨94140341530133860117533545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62760227686755906745022363 94140341530133860117533545)
  ·
    refine ⟨70605256147600395088150159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94140341530133860117533545 70605256147600395088150159)
    ·
      refine ⟨105907884221400592632225239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70605256147600395088150159 105907884221400592632225239)
      ·
        refine ⟨158861826332100888948337859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105907884221400592632225239 158861826332100888948337859)
        ·
          refine ⟨238292739498151333422506789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158861826332100888948337859 238292739498151333422506789)
          ·
            refine ⟨44679888655903375016720023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238292739498151333422506789 44679888655903375016720023)
            ·
              refine ⟨67019832983855062525080035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44679888655903375016720023 67019832983855062525080035)
              ·
                refine ⟨100529749475782593787620053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67019832983855062525080035 100529749475782593787620053)
                ·
                  refine ⟨2356166003338654541897345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 100529749475782593787620053 2356166003338654541897345)
                  ·
                    refine ⟨1767124502503990906423009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2356166003338654541897345 1767124502503990906423009)
                    ·
                      refine ⟨1325343376877993179817257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767124502503990906423009 1325343376877993179817257)
                      ·
                        rfl

theorem cell23_2581097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 2, 2].length) (baseStart_2581097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581097 prefixEnd_2581097 := by exact prefixLift 2581097
  have htrace : WordTrace (prefixWord ++ tailWord_2581097) baseStart_2581097 baseEnd_2581097 := by
    simpa [prefixWord, tailWord_2581097, baseEnd_2581097] using wordTrace_append hprefix tailTrace_2581097
  have hstable : (prefixWord ++ tailWord_2581097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581097).length < 2 ^ (prefixWord ++ tailWord_2581097).sum := by decide
  have hdescent : baseEnd_2581097 < baseStart_2581097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581117 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_2581117 : Nat := 118140960795 + 2581117 * 2 ^ 59
def prefixEnd_2581117 : Nat := 4983230072969 + 3 ^ 40 * 2581117 * 2
def baseEnd_2581117 : Nat := 1325353646491083101567165

theorem tailTrace_2581117 : CollatzResearch.WordTrace tailWord_2581117 prefixEnd_2581117 1325353646491083101567165 := by
  unfold tailWord_2581117
  simp only [CollatzResearch.WordTrace]
  refine ⟨94141070990061403533261605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62760713993374269022174403 94141070990061403533261605)
  ·
    refine ⟨17651450810636513162486551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94141070990061403533261605 17651450810636513162486551)
    ·
      refine ⟨26477176215954769743729827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17651450810636513162486551 26477176215954769743729827)
      ·
        refine ⟨39715764323932154615594741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26477176215954769743729827 39715764323932154615594741)
        ·
          refine ⟨3723352905368639495212007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39715764323932154615594741 3723352905368639495212007)
          ·
            refine ⟨5585029358052959242818011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723352905368639495212007 5585029358052959242818011)
            ·
              refine ⟨8377544037079438864227017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585029358052959242818011 8377544037079438864227017)
              ·
                refine ⟨6283158027809579148170263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8377544037079438864227017 6283158027809579148170263)
                ·
                  refine ⟨9424737041714368722255395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6283158027809579148170263 9424737041714368722255395)
                  ·
                    refine ⟨14137105562571553083383093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9424737041714368722255395 14137105562571553083383093)
                    ·
                      refine ⟨1325353646491083101567165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14137105562571553083383093 1325353646491083101567165)
                      ·
                        rfl

theorem cell23_2581117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_2581117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581117 prefixEnd_2581117 := by exact prefixLift 2581117
  have htrace : WordTrace (prefixWord ++ tailWord_2581117) baseStart_2581117 baseEnd_2581117 := by
    simpa [prefixWord, tailWord_2581117, baseEnd_2581117] using wordTrace_append hprefix tailTrace_2581117
  have hstable : (prefixWord ++ tailWord_2581117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581117).length < 2 ^ (prefixWord ++ tailWord_2581117).sum := by decide
  have hdescent : baseEnd_2581117 < baseStart_2581117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581134 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2581134 : Nat := 118140960795 + 2581134 * 2 ^ 59
def prefixEnd_2581134 : Nat := 4983230072969 + 3 ^ 40 * 2581134 * 2
def baseEnd_2581134 : Nat := 1325362375662209535054587

theorem tailTrace_2581134 : CollatzResearch.WordTrace tailWord_2581134 prefixEnd_2581134 1325362375662209535054587 := by
  unfold tailWord_2581134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11767711378874976929578807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62761127353999876957753637 11767711378874976929578807)
  ·
    refine ⟨17651567068312465394368211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11767711378874976929578807 17651567068312465394368211)
    ·
      refine ⟨26477350602468698091552317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17651567068312465394368211 26477350602468698091552317)
      ·
        refine ⟨9929006475925761784332119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26477350602468698091552317 9929006475925761784332119)
        ·
          refine ⟨14893509713888642676498179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9929006475925761784332119 14893509713888642676498179)
          ·
            refine ⟨22340264570832964014747269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14893509713888642676498179 22340264570832964014747269)
            ·
              refine ⟨4188799607031180752765113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22340264570832964014747269 4188799607031180752765113)
              ·
                refine ⟨3141599705273385564573835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4188799607031180752765113 3141599705273385564573835)
                ·
                  refine ⟨4712399557910078346860753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141599705273385564573835 4712399557910078346860753)
                  ·
                    refine ⟨3534299668432558760145565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4712399557910078346860753 3534299668432558760145565)
                    ·
                      refine ⟨1325362375662209535054587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3534299668432558760145565 1325362375662209535054587)
                      ·
                        rfl

theorem cell23_2581134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2581134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581134 prefixEnd_2581134 := by exact prefixLift 2581134
  have htrace : WordTrace (prefixWord ++ tailWord_2581134) baseStart_2581134 baseEnd_2581134 := by
    simpa [prefixWord, tailWord_2581134, baseEnd_2581134] using wordTrace_append hprefix tailTrace_2581134
  have hstable : (prefixWord ++ tailWord_2581134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581134).length < 2 ^ (prefixWord ++ tailWord_2581134).sum := by decide
  have hdescent : baseEnd_2581134 < baseStart_2581134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581148 : List Nat := [2, 2, 3, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_2581148 : Nat := 118140960795 + 2581148 * 2 ^ 59
def prefixEnd_2581148 : Nat := 4983230072969 + 3 ^ 40 * 2581148 * 2
def baseEnd_2581148 : Nat := 1325369564391372480279523

theorem tailTrace_2581148 : CollatzResearch.WordTrace tailWord_2581148 prefixEnd_2581148 1325369564391372480279523 := by
  unfold tailWord_2581148
  simp only [CollatzResearch.WordTrace]
  refine ⟨47071100826474547913820049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62761467768632730551760065 47071100826474547913820049)
  ·
    refine ⟨35303325619855910935365037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47071100826474547913820049 35303325619855910935365037)
    ·
      refine ⟨13238747107445966600761889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35303325619855910935365037 13238747107445966600761889)
      ·
        refine ⟨9929060330584474950571417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13238747107445966600761889 9929060330584474950571417)
        ·
          refine ⟨7446795247938356212928563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9929060330584474950571417 7446795247938356212928563)
          ·
            refine ⟨11170192871907534319392845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446795247938356212928563 11170192871907534319392845)
            ·
              refine ⟨4188822326965325369772317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11170192871907534319392845 4188822326965325369772317)
              ·
                refine ⟨1570808372611997013664619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4188822326965325369772317 1570808372611997013664619)
                ·
                  refine ⟨2356212558917995520496929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570808372611997013664619 2356212558917995520496929)
                  ·
                    refine ⟨1767159419188496640372697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2356212558917995520496929 1767159419188496640372697)
                    ·
                      refine ⟨1325369564391372480279523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767159419188496640372697 1325369564391372480279523)
                      ·
                        rfl

theorem cell23_2581148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_2581148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581148 prefixEnd_2581148 := by exact prefixLift 2581148
  have htrace : WordTrace (prefixWord ++ tailWord_2581148) baseStart_2581148 baseEnd_2581148 := by
    simpa [prefixWord, tailWord_2581148, baseEnd_2581148] using wordTrace_append hprefix tailTrace_2581148
  have hstable : (prefixWord ++ tailWord_2581148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581148).length < 2 ^ (prefixWord ++ tailWord_2581148).sum := by decide
  have hdescent : baseEnd_2581148 < baseStart_2581148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581157 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 5, 3, 2]
def baseStart_2581157 : Nat := 118140960795 + 2581157 * 2 ^ 59
def prefixEnd_2581157 : Nat := 4983230072969 + 3 ^ 40 * 2581157 * 2
def baseEnd_2581157 : Nat := 1325374185717262945066981

theorem tailTrace_2581157 : CollatzResearch.WordTrace tailWord_2581157 prefixEnd_2581157 1325374185717262945066981 := by
  unfold tailWord_2581157
  simp only [CollatzResearch.WordTrace]
  refine ⟨94142529909916490364717725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62761686606610993576478483 94142529909916490364717725)
  ·
    refine ⟨35303448716218683886769147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94142529909916490364717725 35303448716218683886769147)
    ·
      refine ⟨52955173074328025830153721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35303448716218683886769147 52955173074328025830153721)
      ·
        refine ⟨39716379805746019372615291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52955173074328025830153721 39716379805746019372615291)
        ·
          refine ⟨59574569708619029058922937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39716379805746019372615291 59574569708619029058922937)
          ·
            refine ⟨44680927281464271794192203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59574569708619029058922937 44680927281464271794192203)
            ·
              refine ⟨67021390922196407691288305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44680927281464271794192203 67021390922196407691288305)
              ·
                refine ⟨50266043191647305768466229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67021390922196407691288305 50266043191647305768466229)
                ·
                  refine ⟨4712441549216934915793709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50266043191647305768466229 4712441549216934915793709)
                  ·
                    refine ⟨1767165580956350593422641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4712441549216934915793709 1767165580956350593422641)
                    ·
                      refine ⟨1325374185717262945066981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767165580956350593422641 1325374185717262945066981)
                      ·
                        rfl

theorem cell23_2581157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_2581157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581157 prefixEnd_2581157 := by exact prefixLift 2581157
  have htrace : WordTrace (prefixWord ++ tailWord_2581157) baseStart_2581157 baseEnd_2581157 := by
    simpa [prefixWord, tailWord_2581157, baseEnd_2581157] using wordTrace_append hprefix tailTrace_2581157
  have hstable : (prefixWord ++ tailWord_2581157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581157).length < 2 ^ (prefixWord ++ tailWord_2581157).sum := by decide
  have hdescent : baseEnd_2581157 < baseStart_2581157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581165 : List Nat := [1, 5, 2, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_2581165 : Nat := 118140960795 + 2581165 * 2 ^ 59
def prefixEnd_2581165 : Nat := 4983230072969 + 3 ^ 40 * 2581165 * 2
def baseEnd_2581165 : Nat := 1325378293562498913766945

theorem tailTrace_2581165 : CollatzResearch.WordTrace tailWord_2581165 prefixEnd_2581165 1325378293562498913766945 := by
  unfold tailWord_2581165
  simp only [CollatzResearch.WordTrace]
  refine ⟨94142821693887507731008949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62761881129258338487339299 94142821693887507731008949)
  ·
    refine ⟨8825889533801953849782089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94142821693887507731008949 8825889533801953849782089)
    ·
      refine ⟨6619417150351465387336567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8825889533801953849782089 6619417150351465387336567)
      ·
        refine ⟨9929125725527198081004851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6619417150351465387336567 9929125725527198081004851)
        ·
          refine ⟨14893688588290797121507277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9929125725527198081004851 14893688588290797121507277)
          ·
            refine ⟨5585133220609048920565229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14893688588290797121507277 5585133220609048920565229)
            ·
              refine ⟨2094424957728393345211961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5585133220609048920565229 2094424957728393345211961)
              ·
                refine ⟨1570818718296295008908971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094424957728393345211961 1570818718296295008908971)
                ·
                  refine ⟨2356228077444442513363457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570818718296295008908971 2356228077444442513363457)
                  ·
                    refine ⟨1767171058083331885022593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2356228077444442513363457 1767171058083331885022593)
                    ·
                      refine ⟨1325378293562498913766945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767171058083331885022593 1325378293562498913766945)
                      ·
                        rfl

theorem cell23_2581165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_2581165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581165 prefixEnd_2581165 := by exact prefixLift 2581165
  have htrace : WordTrace (prefixWord ++ tailWord_2581165) baseStart_2581165 baseEnd_2581165 := by
    simpa [prefixWord, tailWord_2581165, baseEnd_2581165] using wordTrace_append hprefix tailTrace_2581165
  have hstable : (prefixWord ++ tailWord_2581165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581165).length < 2 ^ (prefixWord ++ tailWord_2581165).sum := by decide
  have hdescent : baseEnd_2581165 < baseStart_2581165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581170 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_2581170 : Nat := 118140960795 + 2581170 * 2 ^ 59
def prefixEnd_2581170 : Nat := 4983230072969 + 3 ^ 40 * 2581170 * 2
def baseEnd_2581170 : Nat := 1325380860965771394204421

theorem tailTrace_2581170 : CollatzResearch.WordTrace tailWord_2581170 prefixEnd_2581170 1325380860965771394204421 := by
  unfold tailWord_2581170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23535751014717348396235241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62762002705912929056627309 23535751014717348396235241)
  ·
    refine ⟨17651813261038011297176431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23535751014717348396235241 17651813261038011297176431)
    ·
      refine ⟨26477719891557016945764647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17651813261038011297176431 26477719891557016945764647)
      ·
        refine ⟨39716579837335525418646971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26477719891557016945764647 39716579837335525418646971)
        ·
          refine ⟨59574869756003288127970457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39716579837335525418646971 59574869756003288127970457)
          ·
            refine ⟨44681152317002466095977843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59574869756003288127970457 44681152317002466095977843)
            ·
              refine ⟨67021728475503699143966765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44681152317002466095977843 67021728475503699143966765)
              ·
                refine ⟨25133148178313887178987537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67021728475503699143966765 25133148178313887178987537)
                ·
                  refine ⟨18849861133735415384240653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25133148178313887178987537 18849861133735415384240653)
                  ·
                    refine ⟨7068697925150780769090245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18849861133735415384240653 7068697925150780769090245)
                    ·
                      refine ⟨1325380860965771394204421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7068697925150780769090245 1325380860965771394204421)
                      ·
                        rfl

theorem cell23_2581170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_2581170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581170 prefixEnd_2581170 := by exact prefixLift 2581170
  have htrace : WordTrace (prefixWord ++ tailWord_2581170) baseStart_2581170 baseEnd_2581170 := by
    simpa [prefixWord, tailWord_2581170, baseEnd_2581170] using wordTrace_append hprefix tailTrace_2581170
  have hstable : (prefixWord ++ tailWord_2581170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581170).length < 2 ^ (prefixWord ++ tailWord_2581170).sum := by decide
  have hdescent : baseEnd_2581170 < baseStart_2581170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581180 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_2581180 : Nat := 118140960795 + 2581180 * 2 ^ 59
def prefixEnd_2581180 : Nat := 4983230072969 + 3 ^ 40 * 2581180 * 2
def baseEnd_2581180 : Nat := 441795331924105451693125

theorem tailTrace_2581180 : CollatzResearch.WordTrace tailWord_2581180 prefixEnd_2581180 441795331924105451693125 := by
  unfold tailWord_2581180
  simp only [CollatzResearch.WordTrace]
  refine ⟨47071684394416582646402497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62762245859222110195203329 47071684394416582646402497)
  ·
    refine ⟨35303763295812436984801873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47071684394416582646402497 35303763295812436984801873)
    ·
      refine ⟨26477822471859327738601405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35303763295812436984801873 26477822471859327738601405)
      ·
        refine ⟨9929183426947247901975527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26477822471859327738601405 9929183426947247901975527)
        ·
          refine ⟨14893775140420871852963291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9929183426947247901975527 14893775140420871852963291)
          ·
            refine ⟨22340662710631307779444937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14893775140420871852963291 22340662710631307779444937)
            ·
              refine ⟨16755497032973480834583703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22340662710631307779444937 16755497032973480834583703)
              ·
                refine ⟨25133245549460221251875555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16755497032973480834583703 25133245549460221251875555)
                ·
                  refine ⟨37699868324190331877813333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25133245549460221251875555 37699868324190331877813333)
                  ·
                    refine ⟨441795331924105451693125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37699868324190331877813333 441795331924105451693125)
                    ·
                      rfl

theorem cell23_2581180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_2581180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581180 prefixEnd_2581180 := by exact prefixLift 2581180
  have htrace : WordTrace (prefixWord ++ tailWord_2581180) baseStart_2581180 baseEnd_2581180 := by
    simpa [prefixWord, tailWord_2581180, baseEnd_2581180] using wordTrace_append hprefix tailTrace_2581180
  have hstable : (prefixWord ++ tailWord_2581180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581180).length < 2 ^ (prefixWord ++ tailWord_2581180).sum := by decide
  have hdescent : baseEnd_2581180 < baseStart_2581180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581181 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 2, 1, 3]
def baseStart_2581181 : Nat := 118140960795 + 2581181 * 2 ^ 59
def prefixEnd_2581181 : Nat := 4983230072969 + 3 ^ 40 * 2581181 * 2
def baseEnd_2581181 : Nat := 1325386509252970851166871

theorem tailTrace_2581181 : CollatzResearch.WordTrace tailWord_2581181 prefixEnd_2581181 1325386509252970851166871 := by
  unfold tailWord_2581181
  simp only [CollatzResearch.WordTrace]
  refine ⟨94143405261829542463591397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62762270174553028309060931 94143405261829542463591397)
  ·
    refine ⟨17651888486593039211923387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94143405261829542463591397 17651888486593039211923387)
    ·
      refine ⟨26477832729889558817885081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17651888486593039211923387 26477832729889558817885081)
      ·
        refine ⟨19858374547417169113413811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26477832729889558817885081 19858374547417169113413811)
        ·
          refine ⟨29787561821125753670120717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19858374547417169113413811 29787561821125753670120717)
          ·
            refine ⟨11170335682922157626295269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29787561821125753670120717 11170335682922157626295269)
            ·
              refine ⟨2094437940547904554930363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11170335682922157626295269 2094437940547904554930363)
              ·
                refine ⟨3141656910821856832395545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094437940547904554930363 3141656910821856832395545)
                ·
                  refine ⟨2356242683116392624296659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141656910821856832395545 2356242683116392624296659)
                  ·
                    refine ⟨3534364024674588936444989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2356242683116392624296659 3534364024674588936444989)
                    ·
                      refine ⟨1325386509252970851166871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3534364024674588936444989 1325386509252970851166871)
                      ·
                        rfl

theorem cell23_2581181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_2581181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581181 prefixEnd_2581181 := by exact prefixLift 2581181
  have htrace : WordTrace (prefixWord ++ tailWord_2581181) baseStart_2581181 baseEnd_2581181 := by
    simpa [prefixWord, tailWord_2581181, baseEnd_2581181] using wordTrace_append hprefix tailTrace_2581181
  have hstable : (prefixWord ++ tailWord_2581181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581181).length < 2 ^ (prefixWord ++ tailWord_2581181).sum := by decide
  have hdescent : baseEnd_2581181 < baseStart_2581181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581185 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2581185 : Nat := 118140960795 + 2581185 * 2 ^ 59
def prefixEnd_2581185 : Nat := 4983230072969 + 3 ^ 40 * 2581185 * 2
def baseEnd_2581185 : Nat := 1325388563175588835516853

theorem tailTrace_2581185 : CollatzResearch.WordTrace tailWord_2581185 prefixEnd_2581185 1325388563175588835516853 := by
  unfold tailWord_2581185
  simp only [CollatzResearch.WordTrace]
  refine ⟨94143551153815051146737009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62762367435876700764491339 94143551153815051146737009)
  ·
    refine ⟨70607663365361288360052757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94143551153815051146737009 70607663365361288360052757)
    ·
      refine ⟨3309734220251310391877473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70607663365361288360052757 3309734220251310391877473)
      ·
        refine ⟨2482300665188482793908105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3309734220251310391877473 2482300665188482793908105)
        ·
          refine ⟨1861725498891362095431079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2482300665188482793908105 1861725498891362095431079)
          ·
            refine ⟨2792588248337043143146619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861725498891362095431079 2792588248337043143146619)
            ·
              refine ⟨4188882372505564714719929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792588248337043143146619 4188882372505564714719929)
              ·
                refine ⟨3141661779379173536039947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4188882372505564714719929 3141661779379173536039947)
                ·
                  refine ⟨4712492669068760304059921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141661779379173536039947 4712492669068760304059921)
                  ·
                    refine ⟨3534369501801570228044941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4712492669068760304059921 3534369501801570228044941)
                    ·
                      refine ⟨1325388563175588835516853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3534369501801570228044941 1325388563175588835516853)
                      ·
                        rfl

theorem cell23_2581185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2581185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581185 prefixEnd_2581185 := by exact prefixLift 2581185
  have htrace : WordTrace (prefixWord ++ tailWord_2581185) baseStart_2581185 baseEnd_2581185 := by
    simpa [prefixWord, tailWord_2581185, baseEnd_2581185] using wordTrace_append hprefix tailTrace_2581185
  have hstable : (prefixWord ++ tailWord_2581185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581185).length < 2 ^ (prefixWord ++ tailWord_2581185).sum := by decide
  have hdescent : baseEnd_2581185 < baseStart_2581185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581221 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 2, 2, 2]
def baseStart_2581221 : Nat := 118140960795 + 2581221 * 2 ^ 59
def prefixEnd_2581221 : Nat := 4983230072969 + 3 ^ 40 * 2581221 * 2
def baseEnd_2581221 : Nat := 1325407048479150694666687

theorem tailTrace_2581221 : CollatzResearch.WordTrace tailWord_2581221 prefixEnd_2581221 1325407048479150694666687 := by
  unfold tailWord_2581221
  simp only [CollatzResearch.WordTrace]
  refine ⟨94144864181684629295047517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62763242787789752863365011 94144864181684629295047517)
  ·
    refine ⟨35304324068131735985642819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94144864181684629295047517 35304324068131735985642819)
    ·
      refine ⟨52956486102197603978464229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35304324068131735985642819 52956486102197603978464229)
      ·
        refine ⟨9929341144162050745962043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52956486102197603978464229 9929341144162050745962043)
        ·
          refine ⟨14894011716243076118943065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9929341144162050745962043 14894011716243076118943065)
          ·
            refine ⟨11170508787182307089207299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14894011716243076118943065 11170508787182307089207299)
            ·
              refine ⟨16755763180773460633810949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11170508787182307089207299 16755763180773460633810949)
              ·
                refine ⟨3141705596395023868839553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16755763180773460633810949 3141705596395023868839553)
                ·
                  refine ⟨2356279197296267901629665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141705596395023868839553 2356279197296267901629665)
                  ·
                    refine ⟨1767209397972200926222249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2356279197296267901629665 1767209397972200926222249)
                    ·
                      refine ⟨1325407048479150694666687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767209397972200926222249 1325407048479150694666687)
                      ·
                        rfl

theorem cell23_2581221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_2581221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581221 prefixEnd_2581221 := by exact prefixLift 2581221
  have htrace : WordTrace (prefixWord ++ tailWord_2581221) baseStart_2581221 baseEnd_2581221 := by
    simpa [prefixWord, tailWord_2581221, baseEnd_2581221] using wordTrace_append hprefix tailTrace_2581221
  have hstable : (prefixWord ++ tailWord_2581221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581221).length < 2 ^ (prefixWord ++ tailWord_2581221).sum := by decide
  have hdescent : baseEnd_2581221 < baseStart_2581221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581240 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 1, 7]
def baseStart_2581240 : Nat := 118140960795 + 2581240 * 2 ^ 59
def prefixEnd_2581240 : Nat := 4983230072969 + 3 ^ 40 * 2581240 * 2
def baseEnd_2581240 : Nat := 441805601537195373443033

theorem tailTrace_2581240 : CollatzResearch.WordTrace tailWord_2581240 prefixEnd_2581240 441805601537195373443033 := by
  unfold tailWord_2581240
  simp only [CollatzResearch.WordTrace]
  refine ⟨47072778584307897769994587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62763704779077197026659449 47072778584307897769994587)
  ·
    refine ⟨70609167876461846654991881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47072778584307897769994587 70609167876461846654991881)
    ·
      refine ⟨52956875907346384991243911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70609167876461846654991881 52956875907346384991243911)
      ·
        refine ⟨79435313861019577486865867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52956875907346384991243911 79435313861019577486865867)
        ·
          refine ⟨119152970791529366230298801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79435313861019577486865867 119152970791529366230298801)
          ·
            refine ⟨89364728093647024672724101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119152970791529366230298801 89364728093647024672724101)
            ·
              refine ⟨16755886517558817126135769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89364728093647024672724101 16755886517558817126135769)
              ·
                refine ⟨12566914888169112844601827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16755886517558817126135769 12566914888169112844601827)
                ·
                  refine ⟨18850372332253669266902741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12566914888169112844601827 18850372332253669266902741)
                  ·
                    refine ⟨441805601537195373443033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18850372332253669266902741 441805601537195373443033)
                    ·
                      rfl

theorem cell23_2581240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_2581240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581240 prefixEnd_2581240 := by exact prefixLift 2581240
  have htrace : WordTrace (prefixWord ++ tailWord_2581240) baseStart_2581240 baseEnd_2581240 := by
    simpa [prefixWord, tailWord_2581240, baseEnd_2581240] using wordTrace_append hprefix tailTrace_2581240
  have hstable : (prefixWord ++ tailWord_2581240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581240).length < 2 ^ (prefixWord ++ tailWord_2581240).sum := by decide
  have hdescent : baseEnd_2581240 < baseStart_2581240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581247 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 4, 5, 2]
def baseStart_2581247 : Nat := 118140960795 + 2581247 * 2 ^ 59
def prefixEnd_2581247 : Nat := 4983230072969 + 3 ^ 40 * 2581247 * 2
def baseEnd_2581247 : Nat := 1325420398976167592941567

theorem tailTrace_2581247 : CollatzResearch.WordTrace tailWord_2581247 prefixEnd_2581247 1325420398976167592941567 := by
  unfold tailWord_2581247
  simp only [CollatzResearch.WordTrace]
  refine ⟨94145812479590435735493995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62763874986393623823662663 94145812479590435735493995)
  ·
    refine ⟨141218718719385653603240993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94145812479590435735493995 141218718719385653603240993)
    ·
      refine ⟨105914039039539240202430745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141218718719385653603240993 105914039039539240202430745)
      ·
        refine ⟨79435529279654430151823059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105914039039539240202430745 79435529279654430151823059)
        ·
          refine ⟨119153293919481645227734589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79435529279654430151823059 119153293919481645227734589)
          ·
            refine ⟨44682485219805616960400471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119153293919481645227734589 44682485219805616960400471)
            ·
              refine ⟨67023727829708425440600707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44682485219805616960400471 67023727829708425440600707)
              ·
                refine ⟨100535591744562638160901061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67023727829708425440600707 100535591744562638160901061)
                ·
                  refine ⟨18850423452105494655168949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100535591744562638160901061 18850423452105494655168949)
                  ·
                    refine ⟨1767227198634890123922089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18850423452105494655168949 1767227198634890123922089)
                    ·
                      refine ⟨1325420398976167592941567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767227198634890123922089 1325420398976167592941567)
                      ·
                        rfl

theorem cell23_2581247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_2581247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581247 prefixEnd_2581247 := by exact prefixLift 2581247
  have htrace : WordTrace (prefixWord ++ tailWord_2581247) baseStart_2581247 baseEnd_2581247 := by
    simpa [prefixWord, tailWord_2581247, baseEnd_2581247] using wordTrace_append hprefix tailTrace_2581247
  have hstable : (prefixWord ++ tailWord_2581247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581247).length < 2 ^ (prefixWord ++ tailWord_2581247).sum := by decide
  have hdescent : baseEnd_2581247 < baseStart_2581247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581257 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 2, 5]
def baseStart_2581257 : Nat := 118140960795 + 2581257 * 2 ^ 59
def prefixEnd_2581257 : Nat := 4983230072969 + 3 ^ 40 * 2581257 * 2
def baseEnd_2581257 : Nat := 441808511260904184605507

theorem tailTrace_2581257 : CollatzResearch.WordTrace tailWord_2581257 prefixEnd_2581257 441808511260904184605507 := by
  unfold tailWord_2581257
  simp only [CollatzResearch.WordTrace]
  refine ⟨94146177209554207443358025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62764118139702804962238683 94146177209554207443358025)
  ·
    refine ⟨70609632907165655582518519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94146177209554207443358025 70609632907165655582518519)
    ·
      refine ⟨105914449360748483373777779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70609632907165655582518519 105914449360748483373777779)
      ·
        refine ⟨158871674041122725060666669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105914449360748483373777779 158871674041122725060666669)
        ·
          refine ⟨59576877765421021897750001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158871674041122725060666669 59576877765421021897750001)
          ·
            refine ⟨44682658324065766423312501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59576877765421021897750001 44682658324065766423312501)
            ·
              refine ⟨4188999217881165602185547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44682658324065766423312501 4188999217881165602185547)
              ·
                refine ⟨6283498826821748403278321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188999217881165602185547 6283498826821748403278321)
                ·
                  refine ⟨4712624120116311302458741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6283498826821748403278321 4712624120116311302458741)
                  ·
                    refine ⟨441808511260904184605507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4712624120116311302458741 441808511260904184605507)
                    ·
                      rfl

theorem cell23_2581257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 5].length) (baseStart_2581257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581257 prefixEnd_2581257 := by exact prefixLift 2581257
  have htrace : WordTrace (prefixWord ++ tailWord_2581257) baseStart_2581257 baseEnd_2581257 := by
    simpa [prefixWord, tailWord_2581257, baseEnd_2581257] using wordTrace_append hprefix tailTrace_2581257
  have hstable : (prefixWord ++ tailWord_2581257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581257).length < 2 ^ (prefixWord ++ tailWord_2581257).sum := by decide
  have hdescent : baseEnd_2581257 < baseStart_2581257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581294 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2581294 : Nat := 118140960795 + 2581294 * 2 ^ 59
def prefixEnd_2581294 : Nat := 4983230072969 + 3 ^ 40 * 2581294 * 2
def baseEnd_2581294 : Nat := 1325444532566928909053851

theorem tailTrace_2581294 : CollatzResearch.WordTrace tailWord_2581294 prefixEnd_2581294 1325444532566928909053851 := by
  unfold tailWord_2581294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11768440838802520345306867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62765017806946775174969957 11768440838802520345306867)
  ·
    refine ⟨17652661258203780517960301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11768440838802520345306867 17652661258203780517960301)
    ·
      refine ⟨6619747971826417694235113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17652661258203780517960301 6619747971826417694235113)
      ·
        refine ⟨4964810978869813270676335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6619747971826417694235113 4964810978869813270676335)
        ·
          refine ⟨7447216468304719906014503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964810978869813270676335 7447216468304719906014503)
          ·
            refine ⟨11170824702457079859021755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7447216468304719906014503 11170824702457079859021755)
            ·
              refine ⟨16756237053685619788532633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11170824702457079859021755 16756237053685619788532633)
              ·
                refine ⟨12567177790264214841399475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16756237053685619788532633 12567177790264214841399475)
                ·
                  refine ⟨18850766685396322262099213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12567177790264214841399475 18850766685396322262099213)
                  ·
                    refine ⟨7069037507023620848287205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18850766685396322262099213 7069037507023620848287205)
                    ·
                      refine ⟨1325444532566928909053851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7069037507023620848287205 1325444532566928909053851)
                      ·
                        rfl

theorem cell23_2581294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2581294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581294 prefixEnd_2581294 := by exact prefixLift 2581294
  have htrace : WordTrace (prefixWord ++ tailWord_2581294) baseStart_2581294 baseEnd_2581294 := by
    simpa [prefixWord, tailWord_2581294, baseEnd_2581294] using wordTrace_append hprefix tailTrace_2581294
  have hstable : (prefixWord ++ tailWord_2581294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581294).length < 2 ^ (prefixWord ++ tailWord_2581294).sum := by decide
  have hdescent : baseEnd_2581294 < baseStart_2581294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581297 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 3, 4, 3]
def baseStart_2581297 : Nat := 118140960795 + 2581297 * 2 ^ 59
def prefixEnd_2581297 : Nat := 4983230072969 + 3 ^ 40 * 2581297 * 2
def baseEnd_2581297 : Nat := 1325446073008892397316337

theorem tailTrace_2581297 : CollatzResearch.WordTrace tailWord_2581297 prefixEnd_2581297 1325446073008892397316337 := by
  unfold tailWord_2581297
  simp only [CollatzResearch.WordTrace]
  refine ⟨94147636129409294274814145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62765090752939529516542763 94147636129409294274814145)
  ·
    refine ⟨70610727097056970706110609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94147636129409294274814145 70610727097056970706110609)
    ·
      refine ⟨52958045322792728029582957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70610727097056970706110609 52958045322792728029582957)
      ·
        refine ⟨19859266996047273011093609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52958045322792728029582957 19859266996047273011093609)
        ·
          refine ⟨14894450247035454758320207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19859266996047273011093609 14894450247035454758320207)
          ·
            refine ⟨22341675370553182137480311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14894450247035454758320207 22341675370553182137480311)
            ·
              refine ⟨33512513055829773206220467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22341675370553182137480311 33512513055829773206220467)
              ·
                refine ⟨50268769583744659809330701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33512513055829773206220467 50268769583744659809330701)
                ·
                  refine ⟨18850788593904247428499013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50268769583744659809330701 18850788593904247428499013)
                  ·
                    refine ⟨3534522861357046392843565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18850788593904247428499013 3534522861357046392843565)
                    ·
                      refine ⟨1325446073008892397316337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3534522861357046392843565 1325446073008892397316337)
                      ·
                        rfl

theorem cell23_2581297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_2581297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581297 prefixEnd_2581297 := by exact prefixLift 2581297
  have htrace : WordTrace (prefixWord ++ tailWord_2581297) baseStart_2581297 baseEnd_2581297 := by
    simpa [prefixWord, tailWord_2581297, baseEnd_2581297] using wordTrace_append hprefix tailTrace_2581297
  have hstable : (prefixWord ++ tailWord_2581297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581297).length < 2 ^ (prefixWord ++ tailWord_2581297).sum := by decide
  have hdescent : baseEnd_2581297 < baseStart_2581297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581321 : List Nat := [1, 2, 1, 1, 2, 5, 3, 3, 1, 4]
def baseStart_2581321 : Nat := 118140960795 + 2581321 * 2 ^ 59
def prefixEnd_2581321 : Nat := 4983230072969 + 3 ^ 40 * 2581321 * 2
def baseEnd_2581321 : Nat := 441819465514866767805409

theorem tailTrace_2581321 : CollatzResearch.WordTrace tailWord_2581321 prefixEnd_2581321 441819465514866767805409 := by
  unfold tailWord_2581321
  simp only [CollatzResearch.WordTrace]
  refine ⟨94148511481322346373687817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62765674320881564249125211 94148511481322346373687817)
  ·
    refine ⟨70611383610991759780265863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94148511481322346373687817 70611383610991759780265863)
    ·
      refine ⟨105917075416487639670398795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70611383610991759780265863 105917075416487639670398795)
      ·
        refine ⟨158875613124731459505598193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105917075416487639670398795 158875613124731459505598193)
        ·
          refine ⟨119156709843548594629198645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158875613124731459505598193 119156709843548594629198645)
          ·
            refine ⟨11170941547832680746487373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119156709843548594629198645 11170941547832680746487373)
            ·
              refine ⟨4189103080437255279932765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11170941547832680746487373 4189103080437255279932765)
              ·
                refine ⟨1570913655163970729974787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4189103080437255279932765 1570913655163970729974787)
                ·
                  refine ⟨2356370482745956094962181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570913655163970729974787 2356370482745956094962181)
                  ·
                    refine ⟨441819465514866767805409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2356370482745956094962181 441819465514866767805409)
                    ·
                      rfl

theorem cell23_2581321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 1, 4].length) (baseStart_2581321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581321 prefixEnd_2581321 := by exact prefixLift 2581321
  have htrace : WordTrace (prefixWord ++ tailWord_2581321) baseStart_2581321 baseEnd_2581321 := by
    simpa [prefixWord, tailWord_2581321, baseEnd_2581321] using wordTrace_append hprefix tailTrace_2581321
  have hstable : (prefixWord ++ tailWord_2581321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581321).length < 2 ^ (prefixWord ++ tailWord_2581321).sum := by decide
  have hdescent : baseEnd_2581321 < baseStart_2581321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581338 : List Nat := [3, 1, 1, 2, 1, 5, 3, 2, 1, 4]
def baseStart_2581338 : Nat := 118140960795 + 2581338 * 2 ^ 59
def prefixEnd_2581338 : Nat := 4983230072969 + 3 ^ 40 * 2581338 * 2
def baseEnd_2581338 : Nat := 441822375238575578967883

theorem tailTrace_2581338 : CollatzResearch.WordTrace tailWord_2581338 prefixEnd_2581338 441822375238575578967883 := by
  unfold tailWord_2581338
  simp only [CollatzResearch.WordTrace]
  refine ⟨23537282880565189569264167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62766087681507172184704445 23537282880565189569264167)
  ·
    refine ⟨35305924320847784353896251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23537282880565189569264167 35305924320847784353896251)
    ·
      refine ⟨52958886481271676530844377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35305924320847784353896251 52958886481271676530844377)
      ·
        refine ⟨39719164860953757398133283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52958886481271676530844377 39719164860953757398133283)
        ·
          refine ⟨59578747291430636097199925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39719164860953757398133283 59578747291430636097199925)
          ·
            refine ⟨5585507558571622134112493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59578747291430636097199925 5585507558571622134112493)
            ·
              refine ⟨2094565334464358300292185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5585507558571622134112493 2094565334464358300292185)
              ·
                refine ⟨1570924000848268725219139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094565334464358300292185 1570924000848268725219139)
                ·
                  refine ⟨2356386001272403087828709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570924000848268725219139 2356386001272403087828709)
                  ·
                    refine ⟨441822375238575578967883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2356386001272403087828709 441822375238575578967883)
                    ·
                      rfl

theorem cell23_2581338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_2581338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581338 prefixEnd_2581338 := by exact prefixLift 2581338
  have htrace : WordTrace (prefixWord ++ tailWord_2581338) baseStart_2581338 baseEnd_2581338 := by
    simpa [prefixWord, tailWord_2581338, baseEnd_2581338] using wordTrace_append hprefix tailTrace_2581338
  have hstable : (prefixWord ++ tailWord_2581338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581338).length < 2 ^ (prefixWord ++ tailWord_2581338).sum := by decide
  have hdescent : baseEnd_2581338 < baseStart_2581338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581351 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 6]
def baseStart_2581351 : Nat := 118140960795 + 2581351 * 2 ^ 59
def prefixEnd_2581351 : Nat := 4983230072969 + 3 ^ 40 * 2581351 * 2
def baseEnd_2581351 : Nat := 147274866773803909560121

theorem tailTrace_2581351 : CollatzResearch.WordTrace tailWord_2581351 prefixEnd_2581351 147274866773803909560121 := by
  unfold tailWord_2581351
  simp only [CollatzResearch.WordTrace]
  refine ⟨94149605671213661497279907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62766403780809107664853271 94149605671213661497279907)
  ·
    refine ⟨141224408506820492245919861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94149605671213661497279907 141224408506820492245919861)
    ·
      refine ⟨13239788297514421148054987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141224408506820492245919861 13239788297514421148054987)
      ·
        refine ⟨19859682446271631722082481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13239788297514421148054987 19859682446271631722082481)
        ·
          refine ⟨14894761834703723791561861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19859682446271631722082481 14894761834703723791561861)
          ·
            refine ⟨2792767844006948210917849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14894761834703723791561861 2792767844006948210917849)
            ·
              refine ⟨2094575883005211158188387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2792767844006948210917849 2094575883005211158188387)
              ·
                refine ⟨3141863824507816737282581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094575883005211158188387 3141863824507816737282581)
                ·
                  refine ⟨147274866773803909560121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3141863824507816737282581 147274866773803909560121)
                  ·
                    rfl

theorem cell23_2581351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 6].length) (baseStart_2581351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581351 prefixEnd_2581351 := by exact prefixLift 2581351
  have htrace : WordTrace (prefixWord ++ tailWord_2581351) baseStart_2581351 baseEnd_2581351 := by
    simpa [prefixWord, tailWord_2581351, baseEnd_2581351] using wordTrace_append hprefix tailTrace_2581351
  have hstable : (prefixWord ++ tailWord_2581351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581351).length < 2 ^ (prefixWord ++ tailWord_2581351).sum := by decide
  have hdescent : baseEnd_2581351 < baseStart_2581351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581381 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 1, 5]
def baseStart_2581381 : Nat := 118140960795 + 2581381 * 2 ^ 59
def prefixEnd_2581381 : Nat := 4983230072969 + 3 ^ 40 * 2581381 * 2
def baseEnd_2581381 : Nat := 441829735127956689555317

theorem tailTrace_2581381 : CollatzResearch.WordTrace tailWord_2581381 prefixEnd_2581381 441829735127956689555317 := by
  unfold tailWord_2581381
  simp only [CollatzResearch.WordTrace]
  refine ⟨94150699861104976620871997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62767133240736651080581331 94150699861104976620871997)
  ·
    refine ⟨35306512447914366232826999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94150699861104976620871997 35306512447914366232826999)
    ·
      refine ⟨52959768671871549349240499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35306512447914366232826999 52959768671871549349240499)
      ·
        refine ⟨79439653007807324023860749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52959768671871549349240499 79439653007807324023860749)
        ·
          refine ⟨29789869877927746508947781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79439653007807324023860749 29789869877927746508947781)
          ·
            refine ⟨5585600602111452470427709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29789869877927746508947781 5585600602111452470427709)
            ·
              refine ⟨2094600225791794676410391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5585600602111452470427709 2094600225791794676410391)
              ·
                refine ⟨3141900338687692014615587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094600225791794676410391 3141900338687692014615587)
                ·
                  refine ⟨4712850508031538021923381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141900338687692014615587 4712850508031538021923381)
                  ·
                    refine ⟨441829735127956689555317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4712850508031538021923381 441829735127956689555317)
                    ·
                      rfl

theorem cell23_2581381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_2581381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581381 prefixEnd_2581381 := by exact prefixLift 2581381
  have htrace : WordTrace (prefixWord ++ tailWord_2581381) baseStart_2581381 baseEnd_2581381 := by
    simpa [prefixWord, tailWord_2581381, baseEnd_2581381] using wordTrace_append hprefix tailTrace_2581381
  have hstable : (prefixWord ++ tailWord_2581381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581381).length < 2 ^ (prefixWord ++ tailWord_2581381).sum := by decide
  have hdescent : baseEnd_2581381 < baseStart_2581381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581398 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2581398 : Nat := 118140960795 + 2581398 * 2 ^ 59
def prefixEnd_2581398 : Nat := 4983230072969 + 3 ^ 40 * 2581398 * 2
def baseEnd_2581398 : Nat := 441832644851665500717791

theorem tailTrace_2581398 : CollatzResearch.WordTrace tailWord_2581398 prefixEnd_2581398 441832644851665500717791 := by
  unfold tailWord_2581398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884457493877711782765053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62767546601362259016160565 5884457493877711782765053)
  ·
    refine ⟨2206671560204141918536895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5884457493877711782765053 2206671560204141918536895)
    ·
      refine ⟨3310007340306212877805343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2206671560204141918536895 3310007340306212877805343)
      ·
        refine ⟨4965011010459319316708015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310007340306212877805343 4965011010459319316708015)
        ·
          refine ⟨7447516515688978975062023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4965011010459319316708015 7447516515688978975062023)
          ·
            refine ⟨11171274773533468462593035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7447516515688978975062023 11171274773533468462593035)
            ·
              refine ⟨16756912160300202693889553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11171274773533468462593035 16756912160300202693889553)
              ·
                refine ⟨12567684120225152020417165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16756912160300202693889553 12567684120225152020417165)
                ·
                  refine ⟨4712881545084432007656437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12567684120225152020417165 4712881545084432007656437)
                  ·
                    refine ⟨441832644851665500717791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4712881545084432007656437 441832644851665500717791)
                    ·
                      rfl

theorem cell23_2581398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2581398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581398 prefixEnd_2581398 := by exact prefixLift 2581398
  have htrace : WordTrace (prefixWord ++ tailWord_2581398) baseStart_2581398 baseEnd_2581398 := by
    simpa [prefixWord, tailWord_2581398, baseEnd_2581398] using wordTrace_append hprefix tailTrace_2581398
  have hstable : (prefixWord ++ tailWord_2581398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581398).length < 2 ^ (prefixWord ++ tailWord_2581398).sum := by decide
  have hdescent : baseEnd_2581398 < baseStart_2581398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581401 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 3, 2, 2]
def baseStart_2581401 : Nat := 118140960795 + 2581401 * 2 ^ 59
def prefixEnd_2581401 : Nat := 4983230072969 + 3 ^ 40 * 2581401 * 2
def baseEnd_2581401 : Nat := 1325499474996959990415859

theorem tailTrace_2581401 : CollatzResearch.WordTrace tailWord_2581401 prefixEnd_2581401 1325499474996959990415859 := by
  unfold tailWord_2581401
  simp only [CollatzResearch.WordTrace]
  refine ⟨94151429321032520036600057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62767619547355013357733371 94151429321032520036600057)
  ·
    refine ⟨70613571990774390027450043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94151429321032520036600057 70613571990774390027450043)
    ·
      refine ⟨105920357986161585041175065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70613571990774390027450043 105920357986161585041175065)
      ·
        refine ⟨79440268489621188780881299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105920357986161585041175065 79440268489621188780881299)
        ·
          refine ⟨119160402734431783171321949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79440268489621188780881299 119160402734431783171321949)
          ·
            refine ⟨44685151025411918689245731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119160402734431783171321949 44685151025411918689245731)
            ·
              refine ⟨67027726538117878033868597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44685151025411918689245731 67027726538117878033868597)
              ·
                refine ⟨6283849362948551065675181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67027726538117878033868597 6283849362948551065675181)
                ·
                  refine ⟨2356443511105706649628193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6283849362948551065675181 2356443511105706649628193)
                  ·
                    refine ⟨1767332633329279987221145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2356443511105706649628193 1767332633329279987221145)
                    ·
                      refine ⟨1325499474996959990415859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767332633329279987221145 1325499474996959990415859)
                      ·
                        rfl

theorem cell23_2581401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_2581401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581401 prefixEnd_2581401 := by exact prefixLift 2581401
  have htrace : WordTrace (prefixWord ++ tailWord_2581401) baseStart_2581401 baseEnd_2581401 := by
    simpa [prefixWord, tailWord_2581401, baseEnd_2581401] using wordTrace_append hprefix tailTrace_2581401
  have hstable : (prefixWord ++ tailWord_2581401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581401).length < 2 ^ (prefixWord ++ tailWord_2581401).sum := by decide
  have hdescent : baseEnd_2581401 < baseStart_2581401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581434 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3]
def baseStart_2581434 : Nat := 118140960795 + 2581434 * 2 ^ 59
def prefixEnd_2581434 : Nat := 4983230072969 + 3 ^ 40 * 2581434 * 2
def baseEnd_2581434 : Nat := 1325516419858558361303207

theorem tailTrace_2581434 : CollatzResearch.WordTrace tailWord_2581434 prefixEnd_2581434 1325516419858558361303207 := by
  unfold tailWord_2581434
  simp only [CollatzResearch.WordTrace]
  refine ⟨23538158232478241668137839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62768421953275311115034237 23538158232478241668137839)
  ·
    refine ⟨35307237348717362502206759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23538158232478241668137839 35307237348717362502206759)
    ·
      refine ⟨52960856023076043753310139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35307237348717362502206759 52960856023076043753310139)
      ·
        refine ⟨79441284034614065629965209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52960856023076043753310139 79441284034614065629965209)
        ·
          refine ⟨59580963025960549222473907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79441284034614065629965209 59580963025960549222473907)
          ·
            refine ⟨89371444538940823833710861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59580963025960549222473907 89371444538940823833710861)
            ·
              refine ⟨33514291702102808937641573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89371444538940823833710861 33514291702102808937641573)
              ·
                refine ⟨6283929694144276675807795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33514291702102808937641573 6283929694144276675807795)
                ·
                  refine ⟨9425894541216415013711693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6283929694144276675807795 9425894541216415013711693)
                  ·
                    refine ⟨3534710452956155630141885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9425894541216415013711693 3534710452956155630141885)
                    ·
                      refine ⟨1325516419858558361303207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3534710452956155630141885 1325516419858558361303207)
                      ·
                        rfl

theorem cell23_2581434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_2581434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581434 prefixEnd_2581434 := by exact prefixLift 2581434
  have htrace : WordTrace (prefixWord ++ tailWord_2581434) baseStart_2581434 baseEnd_2581434 := by
    simpa [prefixWord, tailWord_2581434, baseEnd_2581434] using wordTrace_append hprefix tailTrace_2581434
  have hstable : (prefixWord ++ tailWord_2581434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581434).length < 2 ^ (prefixWord ++ tailWord_2581434).sum := by decide
  have hdescent : baseEnd_2581434 < baseStart_2581434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581451 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 4, 1, 3]
def baseStart_2581451 : Nat := 118140960795 + 2581451 * 2 ^ 59
def prefixEnd_2581451 : Nat := 4983230072969 + 3 ^ 40 * 2581451 * 2
def baseEnd_2581451 : Nat := 1325525149029684794790629

theorem tailTrace_2581451 : CollatzResearch.WordTrace tailWord_2581451 prefixEnd_2581451 1325525149029684794790629 := by
  unfold tailWord_2581451
  simp only [CollatzResearch.WordTrace]
  refine ⟨94153252970851378575920207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62768835313900919050613471 94153252970851378575920207)
  ·
    refine ⟨141229879456277067863880311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94153252970851378575920207 141229879456277067863880311)
    ·
      refine ⟨211844819184415601795820467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141229879456277067863880311 211844819184415601795820467)
      ·
        refine ⟨317767228776623402693730701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211844819184415601795820467 317767228776623402693730701)
        ·
          refine ⟨119162710791233776010149013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317767228776623402693730701 119162710791233776010149013)
          ·
            refine ⟨5585752068339083250475735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119162710791233776010149013 5585752068339083250475735)
            ·
              refine ⟨8378628102508624875713603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585752068339083250475735 8378628102508624875713603)
              ·
                refine ⟨12567942153762937313570405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8378628102508624875713603 12567942153762937313570405)
                ·
                  refine ⟨2356489153830550746294451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12567942153762937313570405 2356489153830550746294451)
                  ·
                    refine ⟨3534733730745826119441677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2356489153830550746294451 3534733730745826119441677)
                    ·
                      refine ⟨1325525149029684794790629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3534733730745826119441677 1325525149029684794790629)
                      ·
                        rfl

theorem cell23_2581451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 1, 3].length) (baseStart_2581451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581451 prefixEnd_2581451 := by exact prefixLift 2581451
  have htrace : WordTrace (prefixWord ++ tailWord_2581451) baseStart_2581451 baseEnd_2581451 := by
    simpa [prefixWord, tailWord_2581451, baseEnd_2581451] using wordTrace_append hprefix tailTrace_2581451
  have hstable : (prefixWord ++ tailWord_2581451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581451).length < 2 ^ (prefixWord ++ tailWord_2581451).sum := by decide
  have hdescent : baseEnd_2581451 < baseStart_2581451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581492 : List Nat := [2, 6, 2, 1, 2, 1, 9]
def baseStart_2581492 : Nat := 118140960795 + 2581492 * 2 ^ 59
def prefixEnd_2581492 : Nat := 4983230072969 + 3 ^ 40 * 2581492 * 2
def baseEnd_2581492 : Nat := 16364767922673075733061

theorem tailTrace_2581492 : CollatzResearch.WordTrace tailWord_2581492 prefixEnd_2581492 16364767922673075733061 := by
  unfold tailWord_2581492
  simp only [CollatzResearch.WordTrace]
  refine ⟨47077374181851421289081365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62769832242468561718775153 47077374181851421289081365)
  ·
    refine ⟨2206751914774285372925689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47077374181851421289081365 2206751914774285372925689)
    ·
      refine ⟨1655063936080714029694267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2206751914774285372925689 1655063936080714029694267)
      ·
        refine ⟨2482595904121071044541401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655063936080714029694267 2482595904121071044541401)
        ·
          refine ⟨1861946928090803283406051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2482595904121071044541401 1861946928090803283406051)
          ·
            refine ⟨2792920392136204925109077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861946928090803283406051 2792920392136204925109077)
            ·
              refine ⟨16364767922673075733061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2792920392136204925109077 16364767922673075733061)
              ·
                rfl

theorem cell23_2581492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 9].length) (baseStart_2581492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581492 prefixEnd_2581492 := by exact prefixLift 2581492
  have htrace : WordTrace (prefixWord ++ tailWord_2581492) baseStart_2581492 baseEnd_2581492 := by
    simpa [prefixWord, tailWord_2581492, baseEnd_2581492] using wordTrace_append hprefix tailTrace_2581492
  have hstable : (prefixWord ++ tailWord_2581492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581492).length < 2 ^ (prefixWord ++ tailWord_2581492).sum := by decide
  have hdescent : baseEnd_2581492 < baseStart_2581492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581525 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 2, 2, 2]
def baseStart_2581525 : Nat := 118140960795 + 2581525 * 2 ^ 59
def prefixEnd_2581525 : Nat := 4983230072969 + 3 ^ 40 * 2581525 * 2
def baseEnd_2581525 : Nat := 1325563146598117505265289

theorem tailTrace_2581525 : CollatzResearch.WordTrace tailWord_2581525 prefixEnd_2581525 1325563146598117505265289 := by
  unfold tailWord_2581525
  simp only [CollatzResearch.WordTrace]
  refine ⟨94155951972583289214114029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62770634648388859476076019 94155951972583289214114029)
  ·
    refine ⟨35308481989718733455292761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94155951972583289214114029 35308481989718733455292761)
    ·
      refine ⟨26481361492289050091469571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35308481989718733455292761 26481361492289050091469571)
      ·
        refine ⟨39722042238433575137204357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26481361492289050091469571 39722042238433575137204357)
        ·
          refine ⟨7447882919706295338225817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39722042238433575137204357 7447882919706295338225817)
          ·
            refine ⟨5585912189779721503669363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7447882919706295338225817 5585912189779721503669363)
            ·
              refine ⟨8378868284669582255504045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585912189779721503669363 8378868284669582255504045)
              ·
                refine ⟨3142075606751093345814017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8378868284669582255504045 3142075606751093345814017)
                ·
                  refine ⟨2356556705063320009360513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3142075606751093345814017 2356556705063320009360513)
                  ·
                    refine ⟨1767417528797490007020385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2356556705063320009360513 1767417528797490007020385)
                    ·
                      refine ⟨1325563146598117505265289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767417528797490007020385 1325563146598117505265289)
                      ·
                        rfl

theorem cell23_2581525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_2581525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581525 prefixEnd_2581525 := by exact prefixLift 2581525
  have htrace : WordTrace (prefixWord ++ tailWord_2581525) baseStart_2581525 baseEnd_2581525 := by
    simpa [prefixWord, tailWord_2581525, baseEnd_2581525] using wordTrace_append hprefix tailTrace_2581525
  have hstable : (prefixWord ++ tailWord_2581525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581525).length < 2 ^ (prefixWord ++ tailWord_2581525).sum := by decide
  have hdescent : baseEnd_2581525 < baseStart_2581525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581554 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_2581554 : Nat := 118140960795 + 2581554 * 2 ^ 59
def prefixEnd_2581554 : Nat := 4983230072969 + 3 ^ 40 * 2581554 * 2
def baseEnd_2581554 : Nat := 1325578037537097891802655

theorem tailTrace_2581554 : CollatzResearch.WordTrace tailWord_2581554 prefixEnd_2581554 1325578037537097891802655 := by
  unfold tailWord_2581554
  simp only [CollatzResearch.WordTrace]
  refine ⟨23539252422369556791729929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62771339792985484777946477 23539252422369556791729929)
  ·
    refine ⟨17654439316777167593797447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23539252422369556791729929 17654439316777167593797447)
    ·
      refine ⟨26481658975165751390696171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17654439316777167593797447 26481658975165751390696171)
      ·
        refine ⟨39722488462748627086044257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26481658975165751390696171 39722488462748627086044257)
        ·
          refine ⟨29791866347061470314533193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39722488462748627086044257 29791866347061470314533193)
          ·
            refine ⟨22343899760296102735899895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29791866347061470314533193 22343899760296102735899895)
            ·
              refine ⟨33515849640444154103849843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22343899760296102735899895 33515849640444154103849843)
              ·
                refine ⟨50273774460666231155774765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33515849640444154103849843 50273774460666231155774765)
                ·
                  refine ⟨18852665422749836683415537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50273774460666231155774765 18852665422749836683415537)
                  ·
                    refine ⟨14139499067062377512561653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18852665422749836683415537 14139499067062377512561653)
                    ·
                      refine ⟨1325578037537097891802655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14139499067062377512561653 1325578037537097891802655)
                      ·
                        rfl

theorem cell23_2581554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_2581554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581554 prefixEnd_2581554 := by exact prefixLift 2581554
  have htrace : WordTrace (prefixWord ++ tailWord_2581554) baseStart_2581554 baseEnd_2581554 := by
    simpa [prefixWord, tailWord_2581554, baseEnd_2581554] using wordTrace_append hprefix tailTrace_2581554
  have hstable : (prefixWord ++ tailWord_2581554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581554).length < 2 ^ (prefixWord ++ tailWord_2581554).sum := by decide
  have hdescent : baseEnd_2581554 < baseStart_2581554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581561 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 2, 5]
def baseStart_2581561 : Nat := 118140960795 + 2581561 * 2 ^ 59
def prefixEnd_2581561 : Nat := 4983230072969 + 3 ^ 40 * 2581561 * 2
def baseEnd_2581561 : Nat := 441860543967226454805041

theorem tailTrace_2581561 : CollatzResearch.WordTrace tailWord_2581561 prefixEnd_2581561 441860543967226454805041 := by
  unfold tailWord_2581561
  simp only [CollatzResearch.WordTrace]
  refine ⟨94157265000452867362424537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62771510000301911574949691 94157265000452867362424537)
  ·
    refine ⟨70617948750339650521818403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94157265000452867362424537 70617948750339650521818403)
    ·
      refine ⟨105926923125509475782727605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70617948750339650521818403 105926923125509475782727605)
      ·
        refine ⟨9930649043016513354630713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105926923125509475782727605 9930649043016513354630713)
        ·
          refine ⟨7447986782262385015973035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9930649043016513354630713 7447986782262385015973035)
          ·
            refine ⟨11171980173393577523959553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7447986782262385015973035 11171980173393577523959553)
            ·
              refine ⟨8378985130045183142969665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11171980173393577523959553 8378985130045183142969665)
              ·
                refine ⟨6284238847533887357227249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8378985130045183142969665 6284238847533887357227249)
                ·
                  refine ⟨4713179135650415517920437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6284238847533887357227249 4713179135650415517920437)
                  ·
                    refine ⟨441860543967226454805041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4713179135650415517920437 441860543967226454805041)
                    ·
                      rfl

theorem cell23_2581561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_2581561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581561 prefixEnd_2581561 := by exact prefixLift 2581561
  have htrace : WordTrace (prefixWord ++ tailWord_2581561) baseStart_2581561 baseEnd_2581561 := by
    simpa [prefixWord, tailWord_2581561, baseEnd_2581561] using wordTrace_append hprefix tailTrace_2581561
  have hstable : (prefixWord ++ tailWord_2581561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581561).length < 2 ^ (prefixWord ++ tailWord_2581561).sum := by decide
  have hdescent : baseEnd_2581561 < baseStart_2581561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581565 : List Nat := [1, 4, 1, 3, 1, 4, 2, 2, 5]
def baseStart_2581565 : Nat := 118140960795 + 2581565 * 2 ^ 59
def prefixEnd_2581565 : Nat := 4983230072969 + 3 ^ 40 * 2581565 * 2
def baseEnd_2581565 : Nat := 147287076202699705418345

theorem tailTrace_2581565 : CollatzResearch.WordTrace tailWord_2581565 prefixEnd_2581565 147287076202699705418345 := by
  unfold tailWord_2581565
  simp only [CollatzResearch.WordTrace]
  refine ⟨94157410892438376045570149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62771607261625584030380099 94157410892438376045570149)
  ·
    refine ⟨17654514542332195508544403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94157410892438376045570149 17654514542332195508544403)
    ·
      refine ⟨26481771813498293262816605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17654514542332195508544403 26481771813498293262816605)
      ·
        refine ⟨9930664430061859973556227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26481771813498293262816605 9930664430061859973556227)
        ·
          refine ⟨14895996645092789960334341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9930664430061859973556227 14895996645092789960334341)
          ·
            refine ⟨2792999370954898117562689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14895996645092789960334341 2792999370954898117562689)
            ·
              refine ⟨2094749528216173588172017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2792999370954898117562689 2094749528216173588172017)
              ·
                refine ⟨1571062146162130191129013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094749528216173588172017 1571062146162130191129013)
                ·
                  refine ⟨147287076202699705418345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1571062146162130191129013 147287076202699705418345)
                  ·
                    rfl

theorem cell23_2581565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_2581565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581565 prefixEnd_2581565 := by exact prefixLift 2581565
  have htrace : WordTrace (prefixWord ++ tailWord_2581565) baseStart_2581565 baseEnd_2581565 := by
    simpa [prefixWord, tailWord_2581565, baseEnd_2581565] using wordTrace_append hprefix tailTrace_2581565
  have hstable : (prefixWord ++ tailWord_2581565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581565).length < 2 ^ (prefixWord ++ tailWord_2581565).sum := by decide
  have hdescent : baseEnd_2581565 < baseStart_2581565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581594 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_2581594 : Nat := 118140960795 + 2581594 * 2 ^ 59
def prefixEnd_2581594 : Nat := 4983230072969 + 3 ^ 40 * 2581594 * 2
def baseEnd_2581594 : Nat := 1325598576763277735302471

theorem tailTrace_2581594 : CollatzResearch.WordTrace tailWord_2581594 prefixEnd_2581594 1325598576763277735302471 := by
  unfold tailWord_2581594
  simp only [CollatzResearch.WordTrace]
  refine ⟨23539617152333328499593959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62772312406222209332250557 23539617152333328499593959)
  ·
    refine ⟨35309425728499992749390939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23539617152333328499593959 35309425728499992749390939)
    ·
      refine ⟨52964138592749989124086409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35309425728499992749390939 52964138592749989124086409)
      ·
        refine ⟨39723103944562491843064807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52964138592749989124086409 39723103944562491843064807)
        ·
          refine ⟨59584655916843737764597211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39723103944562491843064807 59584655916843737764597211)
          ·
            refine ⟨89376983875265606646895817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59584655916843737764597211 89376983875265606646895817)
            ·
              refine ⟨67032737906449204985171863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89376983875265606646895817 67032737906449204985171863)
              ·
                refine ⟨100549106859673807477757795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67032737906449204985171863 100549106859673807477757795)
                ·
                  refine ⟨150823660289510711216636693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100549106859673807477757795 150823660289510711216636693)
                  ·
                    refine ⟨7069859076070814588279845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 150823660289510711216636693 7069859076070814588279845)
                    ·
                      refine ⟨1325598576763277735302471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7069859076070814588279845 1325598576763277735302471)
                      ·
                        rfl

theorem cell23_2581594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_2581594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581594 prefixEnd_2581594 := by exact prefixLift 2581594
  have htrace : WordTrace (prefixWord ++ tailWord_2581594) baseStart_2581594 baseEnd_2581594 := by
    simpa [prefixWord, tailWord_2581594, baseEnd_2581594] using wordTrace_append hprefix tailTrace_2581594
  have hstable : (prefixWord ++ tailWord_2581594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581594).length < 2 ^ (prefixWord ++ tailWord_2581594).sum := by decide
  have hdescent : baseEnd_2581594 < baseStart_2581594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581604 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 8]
def baseStart_2581604 : Nat := 118140960795 + 2581604 * 2 ^ 59
def prefixEnd_2581604 : Nat := 4983230072969 + 3 ^ 40 * 2581604 * 2
def baseEnd_2581604 : Nat := 147289301285535855130825

theorem tailTrace_2581604 : CollatzResearch.WordTrace tailWord_2581604 prefixEnd_2581604 147289301285535855130825 := by
  unfold tailWord_2581604
  simp only [CollatzResearch.WordTrace]
  refine ⟨47079416669648542853119933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62772555559531390470826577 47079416669648542853119933)
  ·
    refine ⟨17654781251118203569919975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47079416669648542853119933 17654781251118203569919975)
    ·
      refine ⟨26482171876677305354879963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17654781251118203569919975 26482171876677305354879963)
      ·
        refine ⟨39723257815015958032319945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26482171876677305354879963 39723257815015958032319945)
        ·
          refine ⟨29792443361261968524239959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39723257815015958032319945 29792443361261968524239959)
          ·
            refine ⟨44688665041892952786359939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29792443361261968524239959 44688665041892952786359939)
            ·
              refine ⟨67032997562839429179539909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44688665041892952786359939 67032997562839429179539909)
              ·
                refine ⟨12568687043032392971163733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67032997562839429179539909 12568687043032392971163733)
                ·
                  refine ⟨147289301285535855130825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12568687043032392971163733 147289301285535855130825)
                  ·
                    rfl

theorem cell23_2581604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_2581604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581604 prefixEnd_2581604 := by exact prefixLift 2581604
  have htrace : WordTrace (prefixWord ++ tailWord_2581604) baseStart_2581604 baseEnd_2581604 := by
    simpa [prefixWord, tailWord_2581604, baseEnd_2581604] using wordTrace_append hprefix tailTrace_2581604
  have hstable : (prefixWord ++ tailWord_2581604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581604).length < 2 ^ (prefixWord ++ tailWord_2581604).sum := by decide
  have hdescent : baseEnd_2581604 < baseStart_2581604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581624 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_2581624 : Nat := 118140960795 + 2581624 * 2 ^ 59
def prefixEnd_2581624 : Nat := 4983230072969 + 3 ^ 40 * 2581624 * 2
def baseEnd_2581624 : Nat := 1325613981182912617927333

theorem tailTrace_2581624 : CollatzResearch.WordTrace tailWord_2581624 prefixEnd_2581624 1325613981182912617927333 := by
  unfold tailWord_2581624
  simp only [CollatzResearch.WordTrace]
  refine ⟨47079781399612314560983963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62773041866149752747978617 47079781399612314560983963)
  ·
    refine ⟨70619672099418471841475945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47079781399612314560983963 70619672099418471841475945)
    ·
      refine ⟨52964754074563853881106959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70619672099418471841475945 52964754074563853881106959)
      ·
        refine ⟨79447131111845780821660439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52964754074563853881106959 79447131111845780821660439)
        ·
          refine ⟨119170696667768671232490659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79447131111845780821660439 119170696667768671232490659)
          ·
            refine ⟨178756045001653006848735989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119170696667768671232490659 178756045001653006848735989)
            ·
              refine ⟨16758379218904969392068999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178756045001653006848735989 16758379218904969392068999)
              ·
                refine ⟨25137568828357454088103499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16758379218904969392068999 25137568828357454088103499)
                ·
                  refine ⟨37706353242536181132155249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25137568828357454088103499 37706353242536181132155249)
                  ·
                    refine ⟨28279764931902135849116437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37706353242536181132155249 28279764931902135849116437)
                    ·
                      refine ⟨1325613981182912617927333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28279764931902135849116437 1325613981182912617927333)
                      ·
                        rfl

theorem cell23_2581624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_2581624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581624 prefixEnd_2581624 := by exact prefixLift 2581624
  have htrace : WordTrace (prefixWord ++ tailWord_2581624) baseStart_2581624 baseEnd_2581624 := by
    simpa [prefixWord, tailWord_2581624, baseEnd_2581624] using wordTrace_append hprefix tailTrace_2581624
  have hstable : (prefixWord ++ tailWord_2581624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581624).length < 2 ^ (prefixWord ++ tailWord_2581624).sum := by decide
  have hdescent : baseEnd_2581624 < baseStart_2581624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581644 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2581644 : Nat := 118140960795 + 2581644 * 2 ^ 59
def prefixEnd_2581644 : Nat := 4983230072969 + 3 ^ 40 * 2581644 * 2
def baseEnd_2581644 : Nat := 1325624250796002539677241

theorem tailTrace_2581644 : CollatzResearch.WordTrace tailWord_2581644 prefixEnd_2581644 1325624250796002539677241 := by
  unfold tailWord_2581644
  simp only [CollatzResearch.WordTrace]
  refine ⟨47080146129576086268847993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62773528172768115025130657 47080146129576086268847993)
  ·
    refine ⟨35310109597182064701635995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47080146129576086268847993 35310109597182064701635995)
    ·
      refine ⟨52965164395773097052453993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35310109597182064701635995 52965164395773097052453993)
      ·
        refine ⟨39723873296829822789340495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52965164395773097052453993 39723873296829822789340495)
        ·
          refine ⟨59585809945244734184010743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39723873296829822789340495 59585809945244734184010743)
          ·
            refine ⟨89378714917867101276016115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59585809945244734184010743 89378714917867101276016115)
            ·
              refine ⟨134068072376800651914024173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89378714917867101276016115 134068072376800651914024173)
              ·
                refine ⟨50275527141300244467759065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134068072376800651914024173 50275527141300244467759065)
                ·
                  refine ⟨37706645355975183350819299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50275527141300244467759065 37706645355975183350819299)
                  ·
                    refine ⟨56559968033962775026228949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37706645355975183350819299 56559968033962775026228949)
                    ·
                      refine ⟨1325624250796002539677241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56559968033962775026228949 1325624250796002539677241)
                      ·
                        rfl

theorem cell23_2581644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2581644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581644 prefixEnd_2581644 := by exact prefixLift 2581644
  have htrace : WordTrace (prefixWord ++ tailWord_2581644) baseStart_2581644 baseEnd_2581644 := by
    simpa [prefixWord, tailWord_2581644, baseEnd_2581644] using wordTrace_append hprefix tailTrace_2581644
  have hstable : (prefixWord ++ tailWord_2581644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581644).length < 2 ^ (prefixWord ++ tailWord_2581644).sum := by decide
  have hdescent : baseEnd_2581644 < baseStart_2581644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581651 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 1, 5]
def baseStart_2581651 : Nat := 118140960795 + 2581651 * 2 ^ 59
def prefixEnd_2581651 : Nat := 4983230072969 + 3 ^ 40 * 2581651 * 2
def baseEnd_2581651 : Nat := 441875948386861337429903

theorem tailTrace_2581651 : CollatzResearch.WordTrace tailWord_2581651 prefixEnd_2581651 441875948386861337429903 := by
  unfold tailWord_2581651
  simp only [CollatzResearch.WordTrace]
  refine ⟨94160547570126812733200807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62773698380084541822133871 94160547570126812733200807)
  ·
    refine ⟨141240821355190219099801211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94160547570126812733200807 141240821355190219099801211)
    ·
      refine ⟨211861232032785328649701817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141240821355190219099801211 211861232032785328649701817)
      ·
        refine ⟨158895924024588996487276363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211861232032785328649701817 158895924024588996487276363)
        ·
          refine ⟨238343886036883494730914545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158895924024588996487276363 238343886036883494730914545)
          ·
            refine ⟨178757914527662621048185909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238343886036883494730914545 178757914527662621048185909)
            ·
              refine ⟨16758554486968370723267429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178757914527662621048185909 16758554486968370723267429)
              ·
                refine ⟨3142228966306569510612643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16758554486968370723267429 3142228966306569510612643)
                ·
                  refine ⟨4713343449459854265918965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142228966306569510612643 4713343449459854265918965)
                  ·
                    refine ⟨441875948386861337429903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4713343449459854265918965 441875948386861337429903)
                    ·
                      rfl

theorem cell23_2581651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 5].length) (baseStart_2581651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581651 prefixEnd_2581651 := by exact prefixLift 2581651
  have htrace : WordTrace (prefixWord ++ tailWord_2581651) baseStart_2581651 baseEnd_2581651 := by
    simpa [prefixWord, tailWord_2581651, baseEnd_2581651] using wordTrace_append hprefix tailTrace_2581651
  have hstable : (prefixWord ++ tailWord_2581651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581651).length < 2 ^ (prefixWord ++ tailWord_2581651).sum := by decide
  have hdescent : baseEnd_2581651 < baseStart_2581651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581668 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_2581668 : Nat := 118140960795 + 2581668 * 2 ^ 59
def prefixEnd_2581668 : Nat := 4983230072969 + 3 ^ 40 * 2581668 * 2
def baseEnd_2581668 : Nat := 441878858110570148592377

theorem tailTrace_2581668 : CollatzResearch.WordTrace tailWord_2581668 prefixEnd_2581668 441878858110570148592377 := by
  unfold tailWord_2581668
  simp only [CollatzResearch.WordTrace]
  refine ⟨47080583805532612318284829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62774111740710149757713105 47080583805532612318284829)
  ·
    refine ⟨17655218927074729619356811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47080583805532612318284829 17655218927074729619356811)
    ·
      refine ⟨26482828390612094429035217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17655218927074729619356811 26482828390612094429035217)
      ·
        refine ⟨19862121292959070821776413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26482828390612094429035217 19862121292959070821776413)
        ·
          refine ⟨7448295484859651558166155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19862121292959070821776413 7448295484859651558166155)
          ·
            refine ⟨11172443227289477337249233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7448295484859651558166155 11172443227289477337249233)
            ·
              refine ⟨8379332420467108002936925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11172443227289477337249233 8379332420467108002936925)
              ·
                refine ⟨3142249657675165501101347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8379332420467108002936925 3142249657675165501101347)
                ·
                  refine ⟨4713374486512748251652021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142249657675165501101347 4713374486512748251652021)
                  ·
                    refine ⟨441878858110570148592377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4713374486512748251652021 441878858110570148592377)
                    ·
                      rfl

theorem cell23_2581668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_2581668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581668 prefixEnd_2581668 := by exact prefixLift 2581668
  have htrace : WordTrace (prefixWord ++ tailWord_2581668) baseStart_2581668 baseEnd_2581668 := by
    simpa [prefixWord, tailWord_2581668, baseEnd_2581668] using wordTrace_append hprefix tailTrace_2581668
  have hstable : (prefixWord ++ tailWord_2581668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581668).length < 2 ^ (prefixWord ++ tailWord_2581668).sum := by decide
  have hdescent : baseEnd_2581668 < baseStart_2581668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581701 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_2581701 : Nat := 118140960795 + 2581701 * 2 ^ 59
def prefixEnd_2581701 : Nat := 4983230072969 + 3 ^ 40 * 2581701 * 2
def baseEnd_2581701 : Nat := 1325653519193308816664479

theorem tailTrace_2581701 : CollatzResearch.WordTrace tailWord_2581701 prefixEnd_2581701 1325653519193308816664479 := by
  unfold tailWord_2581701
  simp only [CollatzResearch.WordTrace]
  refine ⟨94162371219945671272520957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62774914146630447515013971 94162371219945671272520957)
  ·
    refine ⟨35310889207479626727195359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94162371219945671272520957 35310889207479626727195359)
    ·
      refine ⟨52966333811219440090793039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35310889207479626727195359 52966333811219440090793039)
      ·
        refine ⟨79449500716829160136189559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52966333811219440090793039 79449500716829160136189559)
        ·
          refine ⟨119174251075243740204284339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79449500716829160136189559 119174251075243740204284339)
          ·
            refine ⟨178761376612865610306426509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119174251075243740204284339 178761376612865610306426509)
            ·
              refine ⟨67035516229824603864909941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178761376612865610306426509 67035516229824603864909941)
              ·
                refine ⟨6284579646546056612335307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67035516229824603864909941 6284579646546056612335307)
                ·
                  refine ⟨9426869469819084918502961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6284579646546056612335307 9426869469819084918502961)
                  ·
                    refine ⟨7070152102364313688877221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9426869469819084918502961 7070152102364313688877221)
                    ·
                      refine ⟨1325653519193308816664479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7070152102364313688877221 1325653519193308816664479)
                      ·
                        rfl

theorem cell23_2581701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_2581701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581701 prefixEnd_2581701 := by exact prefixLift 2581701
  have htrace : WordTrace (prefixWord ++ tailWord_2581701) baseStart_2581701 baseEnd_2581701 := by
    simpa [prefixWord, tailWord_2581701, baseEnd_2581701] using wordTrace_append hprefix tailTrace_2581701
  have hstable : (prefixWord ++ tailWord_2581701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581701).length < 2 ^ (prefixWord ++ tailWord_2581701).sum := by decide
  have hdescent : baseEnd_2581701 < baseStart_2581701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581722 : List Nat := [3, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2]
def baseStart_2581722 : Nat := 118140960795 + 2581722 * 2 ^ 59
def prefixEnd_2581722 : Nat := 4983230072969 + 3 ^ 40 * 2581722 * 2
def baseEnd_2581722 : Nat := 1325664302287053234501883

theorem tailTrace_2581722 : CollatzResearch.WordTrace tailWord_2581722 prefixEnd_2581722 1325664302287053234501883 := by
  unfold tailWord_2581722
  simp only [CollatzResearch.WordTrace]
  refine ⟨23540784288217397964758855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62775424768579727906023613 23540784288217397964758855)
  ·
    refine ⟨35311176432326096947138283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23540784288217397964758855 35311176432326096947138283)
    ·
      refine ⟨52966764648489145420707425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35311176432326096947138283 52966764648489145420707425)
      ·
        refine ⟨39725073486366859065530569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52966764648489145420707425 39725073486366859065530569)
        ·
          refine ⟨29793805114775144299147927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39725073486366859065530569 29793805114775144299147927)
          ·
            refine ⟨44690707672162716448721891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29793805114775144299147927 44690707672162716448721891)
            ·
              refine ⟨67036061508244074673082837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44690707672162716448721891 67036061508244074673082837)
              ·
                refine ⟨1571157691599470500150379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 67036061508244074673082837 1571157691599470500150379)
                ·
                  refine ⟨2356736537399205750225569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571157691599470500150379 2356736537399205750225569)
                  ·
                    refine ⟨1767552403049404312669177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2356736537399205750225569 1767552403049404312669177)
                    ·
                      refine ⟨1325664302287053234501883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767552403049404312669177 1325664302287053234501883)
                      ·
                        rfl

theorem cell23_2581722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_2581722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581722 prefixEnd_2581722 := by exact prefixLift 2581722
  have htrace : WordTrace (prefixWord ++ tailWord_2581722) baseStart_2581722 baseEnd_2581722 := by
    simpa [prefixWord, tailWord_2581722, baseEnd_2581722] using wordTrace_append hprefix tailTrace_2581722
  have hstable : (prefixWord ++ tailWord_2581722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581722).length < 2 ^ (prefixWord ++ tailWord_2581722).sum := by decide
  have hdescent : baseEnd_2581722 < baseStart_2581722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581739 : List Nat := [1, 1, 1, 1, 2, 6, 4, 2, 1, 2, 2]
def baseStart_2581739 : Nat := 118140960795 + 2581739 * 2 ^ 59
def prefixEnd_2581739 : Nat := 4983230072969 + 3 ^ 40 * 2581739 * 2
def baseEnd_2581739 : Nat := 1325673031458179667989305

theorem tailTrace_2581739 : CollatzResearch.WordTrace tailWord_2581739 prefixEnd_2581739 1325673031458179667989305 := by
  unfold tailWord_2581739
  simp only [CollatzResearch.WordTrace]
  refine ⟨94163757193808003762404271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62775838129205335841602847 94163757193808003762404271)
  ·
    refine ⟨141245635790712005643606407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94163757193808003762404271 141245635790712005643606407)
    ·
      refine ⟨211868453686068008465409611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141245635790712005643606407 211868453686068008465409611)
      ·
        refine ⟨317802680529102012698114417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211868453686068008465409611 317802680529102012698114417)
        ·
          refine ⟨238352010396826509523585813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317802680529102012698114417 238352010396826509523585813)
          ·
            refine ⟨11172750487351242633918085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 238352010396826509523585813 11172750487351242633918085)
            ·
              refine ⟨2094890716378357993859641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11172750487351242633918085 2094890716378357993859641)
              ·
                refine ⟨1571168037283768495394731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094890716378357993859641 1571168037283768495394731)
                ·
                  refine ⟨2356752055925652743092097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571168037283768495394731 2356752055925652743092097)
                  ·
                    refine ⟨1767564041944239557319073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2356752055925652743092097 1767564041944239557319073)
                    ·
                      refine ⟨1325673031458179667989305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767564041944239557319073 1325673031458179667989305)
                      ·
                        rfl

theorem cell23_2581739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 1, 2, 2].length) (baseStart_2581739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581739 prefixEnd_2581739 := by exact prefixLift 2581739
  have htrace : WordTrace (prefixWord ++ tailWord_2581739) baseStart_2581739 baseEnd_2581739 := by
    simpa [prefixWord, tailWord_2581739, baseEnd_2581739] using wordTrace_append hprefix tailTrace_2581739
  have hstable : (prefixWord ++ tailWord_2581739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581739).length < 2 ^ (prefixWord ++ tailWord_2581739).sum := by decide
  have hdescent : baseEnd_2581739 < baseStart_2581739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581765 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 1, 3, 2]
def baseStart_2581765 : Nat := 118140960795 + 2581765 * 2 ^ 59
def prefixEnd_2581765 : Nat := 4983230072969 + 3 ^ 40 * 2581765 * 2
def baseEnd_2581765 : Nat := 1325686381955196566264185

theorem tailTrace_2581765 : CollatzResearch.WordTrace tailWord_2581765 prefixEnd_2581765 1325686381955196566264185 := by
  unfold tailWord_2581765
  simp only [CollatzResearch.WordTrace]
  refine ⟨94164705491713810202850749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62776470327809206801900499 94164705491713810202850749)
  ·
    refine ⟨35311764559392678826069031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94164705491713810202850749 35311764559392678826069031)
    ·
      refine ⟨52967646839089018239103547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35311764559392678826069031 52967646839089018239103547)
      ·
        refine ⟨79451470258633527358655321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52967646839089018239103547 79451470258633527358655321)
        ·
          refine ⟨59588602693975145518991491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79451470258633527358655321 59588602693975145518991491)
          ·
            refine ⟨89382904040962718278487237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59588602693975145518991491 89382904040962718278487237)
            ·
              refine ⟨16759294507680509677216357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89382904040962718278487237 16759294507680509677216357)
              ·
                refine ⟨3142367720190095564478067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16759294507680509677216357 3142367720190095564478067)
                ·
                  refine ⟨4713551580285143346717101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142367720190095564478067 4713551580285143346717101)
                  ·
                    refine ⟨1767581842606928755018913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4713551580285143346717101 1767581842606928755018913)
                    ·
                      refine ⟨1325686381955196566264185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767581842606928755018913 1325686381955196566264185)
                      ·
                        rfl

theorem cell23_2581765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_2581765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581765 prefixEnd_2581765 := by exact prefixLift 2581765
  have htrace : WordTrace (prefixWord ++ tailWord_2581765) baseStart_2581765 baseEnd_2581765 := by
    simpa [prefixWord, tailWord_2581765, baseEnd_2581765] using wordTrace_append hprefix tailTrace_2581765
  have hstable : (prefixWord ++ tailWord_2581765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581765).length < 2 ^ (prefixWord ++ tailWord_2581765).sum := by decide
  have hdescent : baseEnd_2581765 < baseStart_2581765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581781 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_2581781 : Nat := 118140960795 + 2581781 * 2 ^ 59
def prefixEnd_2581781 : Nat := 4983230072969 + 3 ^ 40 * 2581781 * 2
def baseEnd_2581781 : Nat := 1325694597645668503664111

theorem tailTrace_2581781 : CollatzResearch.WordTrace tailWord_2581781 prefixEnd_2581781 1325694597645668503664111 := by
  unfold tailWord_2581781
  simp only [CollatzResearch.WordTrace]
  refine ⟨94165289059655844935433197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62776859373103896623622131 94165289059655844935433197)
  ·
    refine ⟨35311983397370941850787449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94165289059655844935433197 35311983397370941850787449)
    ·
      refine ⟨26483987548028206388090587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35311983397370941850787449 26483987548028206388090587)
      ·
        refine ⟨39725981322042309582135881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26483987548028206388090587 39725981322042309582135881)
        ·
          refine ⟨29794485991531732186601911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39725981322042309582135881 29794485991531732186601911)
          ·
            refine ⟨44691728987297598279902867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29794485991531732186601911 44691728987297598279902867)
            ·
              refine ⟨67037593480946397419854301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44691728987297598279902867 67037593480946397419854301)
              ·
                refine ⟨25139097555354899032445363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67037593480946397419854301 25139097555354899032445363)
                ·
                  refine ⟨37708646333032348548668045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25139097555354899032445363 37708646333032348548668045)
                  ·
                    refine ⟨14140742374887130705750517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37708646333032348548668045 14140742374887130705750517)
                    ·
                      refine ⟨1325694597645668503664111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14140742374887130705750517 1325694597645668503664111)
                      ·
                        rfl

theorem cell23_2581781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_2581781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581781 prefixEnd_2581781 := by exact prefixLift 2581781
  have htrace : WordTrace (prefixWord ++ tailWord_2581781) baseStart_2581781 baseEnd_2581781 := by
    simpa [prefixWord, tailWord_2581781, baseEnd_2581781] using wordTrace_append hprefix tailTrace_2581781
  have hstable : (prefixWord ++ tailWord_2581781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581781).length < 2 ^ (prefixWord ++ tailWord_2581781).sum := by decide
  have hdescent : baseEnd_2581781 < baseStart_2581781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581789 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2581789 : Nat := 118140960795 + 2581789 * 2 ^ 59
def prefixEnd_2581789 : Nat := 4983230072969 + 3 ^ 40 * 2581789 * 2
def baseEnd_2581789 : Nat := 1325698705490904472364075

theorem tailTrace_2581789 : CollatzResearch.WordTrace tailWord_2581789 prefixEnd_2581789 1325698705490904472364075 := by
  unfold tailWord_2581789
  simp only [CollatzResearch.WordTrace]
  refine ⟨94165580843626862301724421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62777053895751241534482947 94165580843626862301724421)
  ·
    refine ⟨17656046408180036681573329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94165580843626862301724421 17656046408180036681573329)
    ·
      refine ⟨13242034806135027511179997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17656046408180036681573329 13242034806135027511179997)
      ·
        refine ⟨4965763052300635316692499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13242034806135027511179997 4965763052300635316692499)
        ·
          refine ⟨7448644578450952975038749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4965763052300635316692499 7448644578450952975038749)
          ·
            refine ⟨2793241716919107365639531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7448644578450952975038749 2793241716919107365639531)
            ·
              refine ⟨4189862575378661048459297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2793241716919107365639531 4189862575378661048459297)
              ·
                refine ⟨3142396931533995786344473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4189862575378661048459297 3142396931533995786344473)
                ·
                  refine ⟨2356797698650496839758355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3142396931533995786344473 2356797698650496839758355)
                  ·
                    refine ⟨3535196547975745259637533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2356797698650496839758355 3535196547975745259637533)
                    ·
                      refine ⟨1325698705490904472364075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3535196547975745259637533 1325698705490904472364075)
                      ·
                        rfl

theorem cell23_2581789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2581789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581789 prefixEnd_2581789 := by exact prefixLift 2581789
  have htrace : WordTrace (prefixWord ++ tailWord_2581789) baseStart_2581789 baseEnd_2581789 := by
    simpa [prefixWord, tailWord_2581789, baseEnd_2581789] using wordTrace_append hprefix tailTrace_2581789
  have hstable : (prefixWord ++ tailWord_2581789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581789).length < 2 ^ (prefixWord ++ tailWord_2581789).sum := by decide
  have hdescent : baseEnd_2581789 < baseStart_2581789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581805 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2581805 : Nat := 118140960795 + 2581805 * 2 ^ 59
def prefixEnd_2581805 : Nat := 4983230072969 + 3 ^ 40 * 2581805 * 2
def baseEnd_2581805 : Nat := 441902307060458803254667

theorem tailTrace_2581805 : CollatzResearch.WordTrace tailWord_2581805 prefixEnd_2581805 441902307060458803254667 := by
  unfold tailWord_2581805
  simp only [CollatzResearch.WordTrace]
  refine ⟨94166164411568897034306869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62777442941045931356204579 94166164411568897034306869)
  ·
    refine ⟨8828077913584584096966269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94166164411568897034306869 8828077913584584096966269)
    ·
      refine ⟨3310529217594219036362351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8828077913584584096966269 3310529217594219036362351)
      ·
        refine ⟨4965793826391328554543527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310529217594219036362351 4965793826391328554543527)
        ·
          refine ⟨7448690739586992831815291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4965793826391328554543527 7448690739586992831815291)
          ·
            refine ⟨11173036109380489247722937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7448690739586992831815291 11173036109380489247722937)
            ·
              refine ⟨8379777082035366935792203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11173036109380489247722937 8379777082035366935792203)
              ·
                refine ⟨12569665623053050403688305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8379777082035366935792203 12569665623053050403688305)
                ·
                  refine ⟨9427249217289787802766229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12569665623053050403688305 9427249217289787802766229)
                  ·
                    refine ⟨441902307060458803254667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9427249217289787802766229 441902307060458803254667)
                    ·
                      rfl

theorem cell23_2581805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2581805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581805 prefixEnd_2581805 := by exact prefixLift 2581805
  have htrace : WordTrace (prefixWord ++ tailWord_2581805) baseStart_2581805 baseEnd_2581805 := by
    simpa [prefixWord, tailWord_2581805, baseEnd_2581805] using wordTrace_append hprefix tailTrace_2581805
  have hstable : (prefixWord ++ tailWord_2581805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581805).length < 2 ^ (prefixWord ++ tailWord_2581805).sum := by decide
  have hdescent : baseEnd_2581805 < baseStart_2581805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581848 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 2, 5]
def baseStart_2581848 : Nat := 118140960795 + 2581848 * 2 ^ 59
def prefixEnd_2581848 : Nat := 4983230072969 + 3 ^ 40 * 2581848 * 2
def baseEnd_2581848 : Nat := 441909666949839913842101

theorem tailTrace_2581848 : CollatzResearch.WordTrace tailWord_2581848 prefixEnd_2581848 441909666949839913842101 := by
  unfold tailWord_2581848
  simp only [CollatzResearch.WordTrace]
  refine ⟨47083866375206557689061099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62778488500275410252081465 47083866375206557689061099)
  ·
    refine ⟨70625799562809836533591649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47083866375206557689061099 70625799562809836533591649)
    ·
      refine ⟨52969349672107377400193737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70625799562809836533591649 52969349672107377400193737)
      ·
        refine ⟨39727012254080533050145303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52969349672107377400193737 39727012254080533050145303)
        ·
          refine ⟨59590518381120799575217955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39727012254080533050145303 59590518381120799575217955)
          ·
            refine ⟨89385777571681199362826933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59590518381120799575217955 89385777571681199362826933)
            ·
              refine ⟨8379916647345112440265025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89385777571681199362826933 8379916647345112440265025)
              ·
                refine ⟨6284937485508834330198769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8379916647345112440265025 6284937485508834330198769)
                ·
                  refine ⟨4713703114131625747649077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6284937485508834330198769 4713703114131625747649077)
                  ·
                    refine ⟨441909666949839913842101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4713703114131625747649077 441909666949839913842101)
                    ·
                      rfl

theorem cell23_2581848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_2581848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581848 prefixEnd_2581848 := by exact prefixLift 2581848
  have htrace : WordTrace (prefixWord ++ tailWord_2581848) baseStart_2581848 baseEnd_2581848 := by
    simpa [prefixWord, tailWord_2581848, baseEnd_2581848] using wordTrace_append hprefix tailTrace_2581848
  have hstable : (prefixWord ++ tailWord_2581848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581848).length < 2 ^ (prefixWord ++ tailWord_2581848).sum := by decide
  have hdescent : baseEnd_2581848 < baseStart_2581848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581863 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_2581863 : Nat := 118140960795 + 2581863 * 2 ^ 59
def prefixEnd_2581863 : Nat := 4983230072969 + 3 ^ 40 * 2581863 * 2
def baseEnd_2581863 : Nat := 1325736703059337182838735

theorem tailTrace_2581863 : CollatzResearch.WordTrace tailWord_2581863 prefixEnd_2581863 1325736703059337182838735 := by
  unfold tailWord_2581863
  simp only [CollatzResearch.WordTrace]
  refine ⟨94168279845358772939918243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62778853230239181959945495 94168279845358772939918243)
  ·
    refine ⟨141252419768038159409877365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94168279845358772939918243 141252419768038159409877365)
    ·
      refine ⟨13242414353253577444676003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141252419768038159409877365 13242414353253577444676003)
      ·
        refine ⟨19863621529880366167014005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13242414353253577444676003 19863621529880366167014005)
        ·
          refine ⟨1862214518426284328157563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19863621529880366167014005 1862214518426284328157563)
          ·
            refine ⟨2793321777639426492236345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862214518426284328157563 2793321777639426492236345)
            ·
              refine ⟨2094991333229569869177259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2793321777639426492236345 2094991333229569869177259)
              ·
                refine ⟨3142486999844354803765889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094991333229569869177259 3142486999844354803765889)
                ·
                  refine ⟨2356865249883266102824417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3142486999844354803765889 2356865249883266102824417)
                  ·
                    refine ⟨1767648937412449577118313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2356865249883266102824417 1767648937412449577118313)
                    ·
                      refine ⟨1325736703059337182838735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767648937412449577118313 1325736703059337182838735)
                      ·
                        rfl

theorem cell23_2581863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_2581863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581863 prefixEnd_2581863 := by exact prefixLift 2581863
  have htrace : WordTrace (prefixWord ++ tailWord_2581863) baseStart_2581863 baseEnd_2581863 := by
    simpa [prefixWord, tailWord_2581863, baseEnd_2581863] using wordTrace_append hprefix tailTrace_2581863
  have hstable : (prefixWord ++ tailWord_2581863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581863).length < 2 ^ (prefixWord ++ tailWord_2581863).sum := by decide
  have hdescent : baseEnd_2581863 < baseStart_2581863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581885 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_2581885 : Nat := 118140960795 + 2581885 * 2 ^ 59
def prefixEnd_2581885 : Nat := 4983230072969 + 3 ^ 40 * 2581885 * 2
def baseEnd_2581885 : Nat := 1325747999633736096763633

theorem tailTrace_2581885 : CollatzResearch.WordTrace tailWord_2581885 prefixEnd_2581885 1325747999633736096763633 := by
  unfold tailWord_2581885
  simp only [CollatzResearch.WordTrace]
  refine ⟨94169082251279070697219109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62779388167519380464812739 94169082251279070697219109)
  ·
    refine ⟨17656702922114825755728583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94169082251279070697219109 17656702922114825755728583)
    ·
      refine ⟨26485054383172238633592875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17656702922114825755728583 26485054383172238633592875)
      ·
        refine ⟨39727581574758357950389313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26485054383172238633592875 39727581574758357950389313)
        ·
          refine ⟨29795686181068768462791985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39727581574758357950389313 29795686181068768462791985)
          ·
            refine ⟨22346764635801576347093989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29795686181068768462791985 22346764635801576347093989)
            ·
              refine ⟨4190018369212795565080123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22346764635801576347093989 4190018369212795565080123)
              ·
                refine ⟨6285027553819193347620185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4190018369212795565080123 6285027553819193347620185)
                ·
                  refine ⟨4713770665364395010715139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6285027553819193347620185 4713770665364395010715139)
                  ·
                    refine ⟨7070655998046592516072709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4713770665364395010715139 7070655998046592516072709)
                    ·
                      refine ⟨1325747999633736096763633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7070655998046592516072709 1325747999633736096763633)
                      ·
                        rfl

theorem cell23_2581885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_2581885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581885 prefixEnd_2581885 := by exact prefixLift 2581885
  have htrace : WordTrace (prefixWord ++ tailWord_2581885) baseStart_2581885 baseEnd_2581885 := by
    simpa [prefixWord, tailWord_2581885, baseEnd_2581885] using wordTrace_append hprefix tailTrace_2581885
  have hstable : (prefixWord ++ tailWord_2581885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581885).length < 2 ^ (prefixWord ++ tailWord_2581885).sum := by decide
  have hdescent : baseEnd_2581885 < baseStart_2581885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581888 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 3]
def baseStart_2581888 : Nat := 118140960795 + 2581888 * 2 ^ 59
def prefixEnd_2581888 : Nat := 4983230072969 + 3 ^ 40 * 2581888 * 2
def baseEnd_2581888 : Nat := 1325749540075699585026119

theorem tailTrace_2581888 : CollatzResearch.WordTrace tailWord_2581888 prefixEnd_2581888 1325749540075699585026119 := by
  unfold tailWord_2581888
  simp only [CollatzResearch.WordTrace]
  refine ⟨47084595835134101104789159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62779461113512134806385545 47084595835134101104789159)
  ·
    refine ⟨70626893752701151657183739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47084595835134101104789159 70626893752701151657183739)
    ·
      refine ⟨105940340629051727485775609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70626893752701151657183739 105940340629051727485775609)
      ·
        refine ⟨79455255471788795614331707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105940340629051727485775609 79455255471788795614331707)
        ·
          refine ⟨119182883207683193421497561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79455255471788795614331707 119182883207683193421497561)
          ·
            refine ⟨89387162405762395066123171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119182883207683193421497561 89387162405762395066123171)
            ·
              refine ⟨134080743608643592599184757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89387162405762395066123171 134080743608643592599184757)
              ·
                refine ⟨12570069713310336806173571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134080743608643592599184757 12570069713310336806173571)
                ·
                  refine ⟨18855104569965505209260357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12570069713310336806173571 18855104569965505209260357)
                  ·
                    refine ⟨3535332106868532226736317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18855104569965505209260357 3535332106868532226736317)
                    ·
                      refine ⟨1325749540075699585026119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3535332106868532226736317 1325749540075699585026119)
                      ·
                        rfl

theorem cell23_2581888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_2581888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581888 prefixEnd_2581888 := by exact prefixLift 2581888
  have htrace : WordTrace (prefixWord ++ tailWord_2581888) baseStart_2581888 baseEnd_2581888 := by
    simpa [prefixWord, tailWord_2581888, baseEnd_2581888] using wordTrace_append hprefix tailTrace_2581888
  have hstable : (prefixWord ++ tailWord_2581888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581888).length < 2 ^ (prefixWord ++ tailWord_2581888).sum := by decide
  have hdescent : baseEnd_2581888 < baseStart_2581888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581985 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 1, 6]
def baseStart_2581985 : Nat := 118140960795 + 2581985 * 2 ^ 59
def prefixEnd_2581985 : Nat := 4983230072969 + 3 ^ 40 * 2581985 * 2
def baseEnd_2581985 : Nat := 441933115899728568504391

theorem tailTrace_2581985 : CollatzResearch.WordTrace tailWord_2581985 prefixEnd_2581985 441933115899728568504391 := by
  unfold tailWord_2581985
  simp only [CollatzResearch.WordTrace]
  refine ⟨94172729550916787775859409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62781819700611191850572939 94172729550916787775859409)
  ·
    refine ⟨70629547163187590831894557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94172729550916787775859409 70629547163187590831894557)
    ·
      refine ⟨26486080186195346561960459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70629547163187590831894557 26486080186195346561960459)
      ·
        refine ⟨39729120279293019842940689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26486080186195346561960459 39729120279293019842940689)
        ·
          refine ⟨29796840209469764882205517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39729120279293019842940689 29796840209469764882205517)
          ·
            refine ⟨11173815078551161830827069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29796840209469764882205517 11173815078551161830827069)
            ·
              refine ⟨4190180654456685686560151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11173815078551161830827069 4190180654456685686560151)
              ·
                refine ⟨6285270981685028529840227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4190180654456685686560151 6285270981685028529840227)
                ·
                  refine ⟨9427906472527542794760341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6285270981685028529840227 9427906472527542794760341)
                  ·
                    refine ⟨441933115899728568504391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9427906472527542794760341 441933115899728568504391)
                    ·
                      rfl

theorem cell23_2581985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_2581985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581985 prefixEnd_2581985 := by exact prefixLift 2581985
  have htrace : WordTrace (prefixWord ++ tailWord_2581985) baseStart_2581985 baseEnd_2581985 := by
    simpa [prefixWord, tailWord_2581985, baseEnd_2581985] using wordTrace_append hprefix tailTrace_2581985
  have hstable : (prefixWord ++ tailWord_2581985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581985).length < 2 ^ (prefixWord ++ tailWord_2581985).sum := by decide
  have hdescent : baseEnd_2581985 < baseStart_2581985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581992 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_2581992 : Nat := 118140960795 + 2581992 * 2 ^ 59
def prefixEnd_2581992 : Nat := 4983230072969 + 3 ^ 40 * 2581992 * 2
def baseEnd_2581992 : Nat := 1325802942063767178125641

theorem tailTrace_2581992 : CollatzResearch.WordTrace tailWord_2581992 prefixEnd_2581992 1325802942063767178125641 := by
  unfold tailWord_2581992
  simp only [CollatzResearch.WordTrace]
  refine ⟨47086492430945713985682115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62781989907927618647576153 47086492430945713985682115)
  ·
    refine ⟨70629738646418570978523173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47086492430945713985682115 70629738646418570978523173)
    ·
      refine ⟨13243075996203482058473095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70629738646418570978523173 13243075996203482058473095)
      ·
        refine ⟨19864613994305223087709643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13243075996203482058473095 19864613994305223087709643)
        ·
          refine ⟨29796920991457834631564465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19864613994305223087709643 29796920991457834631564465)
          ·
            refine ⟨22347690743593375973673349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29796920991457834631564465 22347690743593375973673349)
            ·
              refine ⟨4190192014423757995063753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22347690743593375973673349 4190192014423757995063753)
              ·
                refine ⟨3142644010817818496297815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4190192014423757995063753 3142644010817818496297815)
                ·
                  refine ⟨4713966016226727744446723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142644010817818496297815 4713966016226727744446723)
                  ·
                    refine ⟨7070949024340091616670085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4713966016226727744446723 7070949024340091616670085)
                    ·
                      refine ⟨1325802942063767178125641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7070949024340091616670085 1325802942063767178125641)
                      ·
                        rfl

theorem cell23_2581992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_2581992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2581992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2581992 prefixEnd_2581992 := by exact prefixLift 2581992
  have htrace : WordTrace (prefixWord ++ tailWord_2581992) baseStart_2581992 baseEnd_2581992 := by
    simpa [prefixWord, tailWord_2581992, baseEnd_2581992] using wordTrace_append hprefix tailTrace_2581992
  have hstable : (prefixWord ++ tailWord_2581992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581992).length < 2 ^ (prefixWord ++ tailWord_2581992).sum := by decide
  have hdescent : baseEnd_2581992 < baseStart_2581992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582002 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_2582002 : Nat := 118140960795 + 2582002 * 2 ^ 59
def prefixEnd_2582002 : Nat := 4983230072969 + 3 ^ 40 * 2582002 * 2
def baseEnd_2582002 : Nat := 441936025623437379666865

theorem tailTrace_2582002 : CollatzResearch.WordTrace tailWord_2582002 prefixEnd_2582002 441936025623437379666865 := by
  unfold tailWord_2582002
  simp only [CollatzResearch.WordTrace]
  refine ⟨23543337397963799919807065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62782233061236799786152173 23543337397963799919807065)
  ·
    refine ⟨17657503048472849939855299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23543337397963799919807065 17657503048472849939855299)
    ·
      refine ⟨26486254572709274909782949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17657503048472849939855299 26486254572709274909782949)
      ·
        refine ⟨4966172732382989045584303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26486254572709274909782949 4966172732382989045584303)
        ·
          refine ⟨7449259098574483568376455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4966172732382989045584303 7449259098574483568376455)
          ·
            refine ⟨11173888647861725352564683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7449259098574483568376455 11173888647861725352564683)
            ·
              refine ⟨16760832971792588028847025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11173888647861725352564683 16760832971792588028847025)
              ·
                refine ⟨12570624728844441021635269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16760832971792588028847025 12570624728844441021635269)
                ·
                  refine ⟨2356992136658332691556613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12570624728844441021635269 2356992136658332691556613)
                  ·
                    refine ⟨441936025623437379666865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2356992136658332691556613 441936025623437379666865)
                    ·
                      rfl

theorem cell23_2582002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_2582002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582002 prefixEnd_2582002 := by exact prefixLift 2582002
  have htrace : WordTrace (prefixWord ++ tailWord_2582002) baseStart_2582002 baseEnd_2582002 := by
    simpa [prefixWord, tailWord_2582002, baseEnd_2582002] using wordTrace_append hprefix tailTrace_2582002
  have hstable : (prefixWord ++ tailWord_2582002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582002).length < 2 ^ (prefixWord ++ tailWord_2582002).sum := by decide
  have hdescent : baseEnd_2582002 < baseStart_2582002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582012 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_2582012 : Nat := 118140960795 + 2582012 * 2 ^ 59
def prefixEnd_2582012 : Nat := 4983230072969 + 3 ^ 40 * 2582012 * 2
def baseEnd_2582012 : Nat := 1325813211676857099875549

theorem tailTrace_2582012 : CollatzResearch.WordTrace tailWord_2582012 prefixEnd_2582012 1325813211676857099875549 := by
  unfold tailWord_2582012
  simp only [CollatzResearch.WordTrace]
  refine ⟨47086857160909485693546145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62782476214545980924728193 47086857160909485693546145)
  ·
    refine ⟨35315142870682114270159609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47086857160909485693546145 35315142870682114270159609)
    ·
      refine ⟨26486357153011585702619707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35315142870682114270159609 26486357153011585702619707)
      ·
        refine ⟨39729535729517378553929561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26486357153011585702619707 39729535729517378553929561)
        ·
          refine ⟨29797151797138033915447171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39729535729517378553929561 29797151797138033915447171)
          ·
            refine ⟨44695727695707050873170757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29797151797138033915447171 44695727695707050873170757)
            ·
              refine ⟨8380448942945072038719517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44695727695707050873170757 8380448942945072038719517)
              ·
                refine ⟨3142668353604402014519819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8380448942945072038719517 3142668353604402014519819)
                ·
                  refine ⟨4714002530406603021779729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142668353604402014519819 4714002530406603021779729)
                  ·
                    refine ⟨3535501897804952266334797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4714002530406603021779729 3535501897804952266334797)
                    ·
                      refine ⟨1325813211676857099875549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3535501897804952266334797 1325813211676857099875549)
                      ·
                        rfl

theorem cell23_2582012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_2582012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582012 prefixEnd_2582012 := by exact prefixLift 2582012
  have htrace : WordTrace (prefixWord ++ tailWord_2582012) baseStart_2582012 baseEnd_2582012 := by
    simpa [prefixWord, tailWord_2582012, baseEnd_2582012] using wordTrace_append hprefix tailTrace_2582012
  have hstable : (prefixWord ++ tailWord_2582012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582012).length < 2 ^ (prefixWord ++ tailWord_2582012).sum := by decide
  have hdescent : baseEnd_2582012 < baseStart_2582012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582026 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2]
def baseStart_2582026 : Nat := 118140960795 + 2582026 * 2 ^ 59
def prefixEnd_2582026 : Nat := 4983230072969 + 3 ^ 40 * 2582026 * 2
def baseEnd_2582026 : Nat := 1325820400406020045100485

theorem tailTrace_2582026 : CollatzResearch.WordTrace tailWord_2582026 prefixEnd_2582026 1325820400406020045100485 := by
  unfold tailWord_2582026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23543556235942062944525483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62782816629178834518734621 23543556235942062944525483)
  ·
    refine ⟨35315334353913094416788225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23543556235942062944525483 35315334353913094416788225)
    ·
      refine ⟨26486500765434820812591169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35315334353913094416788225 26486500765434820812591169)
      ·
        refine ⟨19864875574076115609443377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26486500765434820812591169 19864875574076115609443377)
        ·
          refine ⟨14898656680557086707082533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19864875574076115609443377 14898656680557086707082533)
          ·
            refine ⟨2793498127604453757577975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14898656680557086707082533 2793498127604453757577975)
            ·
              refine ⟨4190247191406680636366963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2793498127604453757577975 4190247191406680636366963)
              ·
                refine ⟨6285370787110020954550445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4190247191406680636366963 6285370787110020954550445)
                ·
                  refine ⟨2357014045166257857956417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6285370787110020954550445 2357014045166257857956417)
                  ·
                    refine ⟨1767760533874693393467313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2357014045166257857956417 1767760533874693393467313)
                    ·
                      refine ⟨1325820400406020045100485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767760533874693393467313 1325820400406020045100485)
                      ·
                        rfl

theorem cell23_2582026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_2582026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582026 prefixEnd_2582026 := by exact prefixLift 2582026
  have htrace : WordTrace (prefixWord ++ tailWord_2582026) baseStart_2582026 baseEnd_2582026 := by
    simpa [prefixWord, tailWord_2582026, baseEnd_2582026] using wordTrace_append hprefix tailTrace_2582026
  have hstable : (prefixWord ++ tailWord_2582026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582026).length < 2 ^ (prefixWord ++ tailWord_2582026).sum := by decide
  have hdescent : baseEnd_2582026 < baseStart_2582026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582036 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2582036 : Nat := 118140960795 + 2582036 * 2 ^ 59
def prefixEnd_2582036 : Nat := 4983230072969 + 3 ^ 40 * 2582036 * 2
def baseEnd_2582036 : Nat := 441941845070855001991813

theorem tailTrace_2582036 : CollatzResearch.WordTrace tailWord_2582036 prefixEnd_2582036 441941845070855001991813 := by
  unfold tailWord_2582036
  simp only [CollatzResearch.WordTrace]
  refine ⟨47087294836866011742982981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62783059782488015657310641 47087294836866011742982981)
  ·
    refine ⟨8828867781912377201809309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47087294836866011742982981 8828867781912377201809309)
    ·
      refine ⟨3310825418217141450678491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8828867781912377201809309 3310825418217141450678491)
      ·
        refine ⟨4966238127325712176017737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310825418217141450678491 4966238127325712176017737)
        ·
          refine ⟨3724678595494284132013303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4966238127325712176017737 3724678595494284132013303)
          ·
            refine ⟨5587017893241426198019955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3724678595494284132013303 5587017893241426198019955)
            ·
              refine ⟨8380526839862139297029933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5587017893241426198019955 8380526839862139297029933)
              ·
                refine ⟨3142697564948302236386225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8380526839862139297029933 3142697564948302236386225)
                ·
                  refine ⟨2357023173711226677289669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3142697564948302236386225 2357023173711226677289669)
                  ·
                    refine ⟨441941845070855001991813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2357023173711226677289669 441941845070855001991813)
                    ·
                      rfl

theorem cell23_2582036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2582036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582036 prefixEnd_2582036 := by exact prefixLift 2582036
  have htrace : WordTrace (prefixWord ++ tailWord_2582036) baseStart_2582036 baseEnd_2582036 := by
    simpa [prefixWord, tailWord_2582036, baseEnd_2582036] using wordTrace_append hprefix tailTrace_2582036
  have hstable : (prefixWord ++ tailWord_2582036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582036).length < 2 ^ (prefixWord ++ tailWord_2582036).sum := by decide
  have hdescent : baseEnd_2582036 < baseStart_2582036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582076 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_2582076 : Nat := 118140960795 + 2582076 * 2 ^ 59
def prefixEnd_2582076 : Nat := 4983230072969 + 3 ^ 40 * 2582076 * 2
def baseEnd_2582076 : Nat := 1325846074438744849475255

theorem tailTrace_2582076 : CollatzResearch.WordTrace tailWord_2582076 prefixEnd_2582076 1325846074438744849475255 := by
  unfold tailWord_2582076
  simp only [CollatzResearch.WordTrace]
  refine ⟨47088024296793555158711041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62784032395724740211614721 47088024296793555158711041)
  ·
    refine ⟨35316018222595166369033281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47088024296793555158711041 35316018222595166369033281)
    ·
      refine ⟨26487013666946374776774961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35316018222595166369033281 26487013666946374776774961)
      ·
        refine ⟨19865260250209781082581221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26487013666946374776774961 19865260250209781082581221)
        ·
          refine ⟨3724736296914333952983979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19865260250209781082581221 3724736296914333952983979)
          ·
            refine ⟨5587104445371500929475969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3724736296914333952983979 5587104445371500929475969)
            ·
              refine ⟨4190328334028625697106977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5587104445371500929475969 4190328334028625697106977)
              ·
                refine ⟨3142746250521469272830233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4190328334028625697106977 3142746250521469272830233)
                ·
                  refine ⟨2357059687891101954622675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3142746250521469272830233 2357059687891101954622675)
                  ·
                    refine ⟨3535589531836652931934013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2357059687891101954622675 3535589531836652931934013)
                    ·
                      refine ⟨1325846074438744849475255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3535589531836652931934013 1325846074438744849475255)
                      ·
                        rfl

theorem cell23_2582076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_2582076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582076 prefixEnd_2582076 := by exact prefixLift 2582076
  have htrace : WordTrace (prefixWord ++ tailWord_2582076) baseStart_2582076 baseEnd_2582076 := by
    simpa [prefixWord, tailWord_2582076, baseEnd_2582076] using wordTrace_append hprefix tailTrace_2582076
  have hstable : (prefixWord ++ tailWord_2582076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582076).length < 2 ^ (prefixWord ++ tailWord_2582076).sum := by decide
  have hdescent : baseEnd_2582076 < baseStart_2582076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582077 : List Nat := [1, 4, 1, 3, 4, 1, 2, 2, 1, 2, 2]
def baseStart_2582077 : Nat := 118140960795 + 2582077 * 2 ^ 59
def prefixEnd_2582077 : Nat := 4983230072969 + 3 ^ 40 * 2582077 * 2
def baseEnd_2582077 : Nat := 1325846587919399345562751

theorem tailTrace_2582077 : CollatzResearch.WordTrace tailWord_2582077 prefixEnd_2582077 1325846587919399345562751 := by
  unfold tailWord_2582077
  simp only [CollatzResearch.WordTrace]
  refine ⟨94176085066583487488208485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62784056711055658325472323 94176085066583487488208485)
  ·
    refine ⟨17658015949984403904039091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94176085066583487488208485 17658015949984403904039091)
    ·
      refine ⟨26487023924976605856058637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17658015949984403904039091 26487023924976605856058637)
      ·
        refine ⟨9932633971866227196021989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26487023924976605856058637 9932633971866227196021989)
        ·
          refine ⟨1862368869724917599254123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9932633971866227196021989 1862368869724917599254123)
          ·
            refine ⟨2793553304587376398881185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862368869724917599254123 2793553304587376398881185)
            ·
              refine ⟨2095164978440532299160889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2793553304587376398881185 2095164978440532299160889)
              ·
                refine ⟨1571373733830399224370667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2095164978440532299160889 1571373733830399224370667)
                ·
                  refine ⟨2357060600745598836556001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571373733830399224370667 2357060600745598836556001)
                  ·
                    refine ⟨1767795450559199127417001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2357060600745598836556001 1767795450559199127417001)
                    ·
                      refine ⟨1325846587919399345562751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767795450559199127417001 1325846587919399345562751)
                      ·
                        rfl

theorem cell23_2582077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_2582077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582077 prefixEnd_2582077 := by exact prefixLift 2582077
  have htrace : WordTrace (prefixWord ++ tailWord_2582077) baseStart_2582077 baseEnd_2582077 := by
    simpa [prefixWord, tailWord_2582077, baseEnd_2582077] using wordTrace_append hprefix tailTrace_2582077
  have hstable : (prefixWord ++ tailWord_2582077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582077).length < 2 ^ (prefixWord ++ tailWord_2582077).sum := by decide
  have hdescent : baseEnd_2582077 < baseStart_2582077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582085 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 1, 6, 3]
def baseStart_2582085 : Nat := 118140960795 + 2582085 * 2 ^ 59
def prefixEnd_2582085 : Nat := 4983230072969 + 3 ^ 40 * 2582085 * 2
def baseEnd_2582085 : Nat := 1325850695764635314262713

theorem tailTrace_2582085 : CollatzResearch.WordTrace tailWord_2582085 prefixEnd_2582085 1325850695764635314262713 := by
  unfold tailWord_2582085
  simp only [CollatzResearch.WordTrace]
  refine ⟨94176376850554504854499709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62784251233703003236333139 94176376850554504854499709)
  ·
    refine ⟨35316141318957939320437391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94176376850554504854499709 35316141318957939320437391)
    ·
      refine ⟨52974211978436908980656087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35316141318957939320437391 52974211978436908980656087)
      ·
        refine ⟨79461317967655363470984131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52974211978436908980656087 79461317967655363470984131)
        ·
          refine ⟨119191976951483045206476197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79461317967655363470984131 119191976951483045206476197)
          ·
            refine ⟨22348495678403070976214287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119191976951483045206476197 22348495678403070976214287)
            ·
              refine ⟨33522743517604606464321431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22348495678403070976214287 33522743517604606464321431)
              ·
                refine ⟨50284115276406909696482147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33522743517604606464321431 50284115276406909696482147)
                ·
                  refine ⟨75426172914610364544723221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50284115276406909696482147 75426172914610364544723221)
                  ·
                    refine ⟨3535601855372360838033901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75426172914610364544723221 3535601855372360838033901)
                    ·
                      refine ⟨1325850695764635314262713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3535601855372360838033901 1325850695764635314262713)
                      ·
                        rfl

theorem cell23_2582085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_2582085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582085 prefixEnd_2582085 := by exact prefixLift 2582085
  have htrace : WordTrace (prefixWord ++ tailWord_2582085) baseStart_2582085 baseEnd_2582085 := by
    simpa [prefixWord, tailWord_2582085, baseEnd_2582085] using wordTrace_append hprefix tailTrace_2582085
  have hstable : (prefixWord ++ tailWord_2582085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582085).length < 2 ^ (prefixWord ++ tailWord_2582085).sum := by decide
  have hdescent : baseEnd_2582085 < baseStart_2582085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582133 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2582133 : Nat := 118140960795 + 2582133 * 2 ^ 59
def prefixEnd_2582133 : Nat := 4983230072969 + 3 ^ 40 * 2582133 * 2
def baseEnd_2582133 : Nat := 1325875342836051126462493

theorem tailTrace_2582133 : CollatzResearch.WordTrace tailWord_2582133 prefixEnd_2582133 1325875342836051126462493 := by
  unfold tailWord_2582133
  simp only [CollatzResearch.WordTrace]
  refine ⟨94178127554380609052247053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62785418369587072701498035 94178127554380609052247053)
  ·
    refine ⟨35316797832892728394592645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94178127554380609052247053 35316797832892728394592645)
    ·
      refine ⟨6621899593667386573986121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35316797832892728394592645 6621899593667386573986121)
      ·
        refine ⟨4966424695250539930489591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6621899593667386573986121 4966424695250539930489591)
        ·
          refine ⟨7449637042875809895734387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4966424695250539930489591 7449637042875809895734387)
          ·
            refine ⟨11174455564313714843601581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7449637042875809895734387 11174455564313714843601581)
            ·
              refine ⟨4190420836617643066350593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11174455564313714843601581 4190420836617643066350593)
              ·
                refine ⟨3142815627463232299762945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4190420836617643066350593 3142815627463232299762945)
                ·
                  refine ⟨2357111720597424224822209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3142815627463232299762945 2357111720597424224822209)
                  ·
                    refine ⟨1767833790448068168616657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2357111720597424224822209 1767833790448068168616657)
                    ·
                      refine ⟨1325875342836051126462493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767833790448068168616657 1325875342836051126462493)
                      ·
                        rfl

theorem cell23_2582133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2582133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582133 prefixEnd_2582133 := by exact prefixLift 2582133
  have htrace : WordTrace (prefixWord ++ tailWord_2582133) baseStart_2582133 baseEnd_2582133 := by
    simpa [prefixWord, tailWord_2582133, baseEnd_2582133] using wordTrace_append hprefix tailTrace_2582133
  have hstable : (prefixWord ++ tailWord_2582133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582133).length < 2 ^ (prefixWord ++ tailWord_2582133).sum := by decide
  have hdescent : baseEnd_2582133 < baseStart_2582133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582135 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 4, 5]
def baseStart_2582135 : Nat := 118140960795 + 2582135 * 2 ^ 59
def prefixEnd_2582135 : Nat := 4983230072969 + 3 ^ 40 * 2582135 * 2
def baseEnd_2582135 : Nat := 441958789932453372879161

theorem tailTrace_2582135 : CollatzResearch.WordTrace tailWord_2582135 prefixEnd_2582135 441958789932453372879161 := by
  unfold tailWord_2582135
  simp only [CollatzResearch.WordTrace]
  refine ⟨94178200500373363393819859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62785467000248908929213239 94178200500373363393819859)
  ·
    refine ⟨141267300750560045090729789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94178200500373363393819859 141267300750560045090729789)
    ·
      refine ⟨52975237781460016909023671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141267300750560045090729789 52975237781460016909023671)
      ·
        refine ⟨79462856672190025363535507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52975237781460016909023671 79462856672190025363535507)
        ·
          refine ⟨119194285008285038045303261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79462856672190025363535507 119194285008285038045303261)
          ·
            refine ⟨44697856878106889266988723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119194285008285038045303261 44697856878106889266988723)
            ·
              refine ⟨67046785317160333900483085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44697856878106889266988723 67046785317160333900483085)
              ·
                refine ⟨25142544493935125212681157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67046785317160333900483085 25142544493935125212681157)
                ·
                  refine ⟨4714227092612835977377717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25142544493935125212681157 4714227092612835977377717)
                  ·
                    refine ⟨441958789932453372879161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4714227092612835977377717 441958789932453372879161)
                    ·
                      rfl

theorem cell23_2582135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_2582135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582135 prefixEnd_2582135 := by exact prefixLift 2582135
  have htrace : WordTrace (prefixWord ++ tailWord_2582135) baseStart_2582135 baseEnd_2582135 := by
    simpa [prefixWord, tailWord_2582135, baseEnd_2582135] using wordTrace_append hprefix tailTrace_2582135
  have hstable : (prefixWord ++ tailWord_2582135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582135).length < 2 ^ (prefixWord ++ tailWord_2582135).sum := by decide
  have hdescent : baseEnd_2582135 < baseStart_2582135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582155 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 4]
def baseStart_2582155 : Nat := 118140960795 + 2582155 * 2 ^ 59
def prefixEnd_2582155 : Nat := 4983230072969 + 3 ^ 40 * 2582155 * 2
def baseEnd_2582155 : Nat := 1325886639410450040387391

theorem tailTrace_2582155 : CollatzResearch.WordTrace tailWord_2582155 prefixEnd_2582155 1325886639410450040387391 := by
  unfold tailWord_2582155
  simp only [CollatzResearch.WordTrace]
  refine ⟨94178929960300906809547919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62785953306867271206365279 94178929960300906809547919)
  ·
    refine ⟨141268394940451360214321879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94178929960300906809547919 141268394940451360214321879)
    ·
      refine ⟨211902592410677040321482819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141268394940451360214321879 211902592410677040321482819)
      ·
        refine ⟨317853888616015560482224229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211902592410677040321482819 317853888616015560482224229)
        ·
          refine ⟨59597604115502917590417043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 317853888616015560482224229 59597604115502917590417043)
          ·
            refine ⟨89396406173254376385625565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59597604115502917590417043 89396406173254376385625565)
            ·
              refine ⟨33523652314970391144609587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89396406173254376385625565 33523652314970391144609587)
              ·
                refine ⟨50285478472455586716914381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33523652314970391144609587 50285478472455586716914381)
                ·
                  refine ⟨18857054427170845018842893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50285478472455586716914381 18857054427170845018842893)
                  ·
                    refine ⟨7071395410189066882066085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18857054427170845018842893 7071395410189066882066085)
                    ·
                      refine ⟨1325886639410450040387391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7071395410189066882066085 1325886639410450040387391)
                      ·
                        rfl

theorem cell23_2582155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 4].length) (baseStart_2582155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582155 prefixEnd_2582155 := by exact prefixLift 2582155
  have htrace : WordTrace (prefixWord ++ tailWord_2582155) baseStart_2582155 baseEnd_2582155 := by
    simpa [prefixWord, tailWord_2582155, baseEnd_2582155] using wordTrace_append hprefix tailTrace_2582155
  have hstable : (prefixWord ++ tailWord_2582155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582155).length < 2 ^ (prefixWord ++ tailWord_2582155).sum := by decide
  have hdescent : baseEnd_2582155 < baseStart_2582155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582185 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_2582185 : Nat := 118140960795 + 2582185 * 2 ^ 59
def prefixEnd_2582185 : Nat := 4983230072969 + 3 ^ 40 * 2582185 * 2
def baseEnd_2582185 : Nat := 1325902043830084923012253

theorem tailTrace_2582185 : CollatzResearch.WordTrace tailWord_2582185 prefixEnd_2582185 1325902043830084923012253 := by
  unfold tailWord_2582185
  simp only [CollatzResearch.WordTrace]
  refine ⟨94180024150192221933140009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62786682766794814622093339 94180024150192221933140009)
  ·
    refine ⟨70635018112644166449855007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94180024150192221933140009 70635018112644166449855007)
    ·
      refine ⟨105952527168966249674782511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70635018112644166449855007 105952527168966249674782511)
      ·
        refine ⟨158928790753449374512173767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105952527168966249674782511 158928790753449374512173767)
        ·
          refine ⟨238393186130174061768260651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158928790753449374512173767 238393186130174061768260651)
          ·
            refine ⟨357589779195261092652390977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238393186130174061768260651 357589779195261092652390977)
            ·
              refine ⟨268192334396445819489293233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357589779195261092652390977 268192334396445819489293233)
              ·
                refine ⟨201144250797334364616969925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268192334396445819489293233 201144250797334364616969925)
                ·
                  refine ⟨37714547024500193365681861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201144250797334364616969925 37714547024500193365681861)
                  ·
                    refine ⟨7071477567093786256065349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37714547024500193365681861 7071477567093786256065349)
                    ·
                      refine ⟨1325902043830084923012253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7071477567093786256065349 1325902043830084923012253)
                      ·
                        rfl

theorem cell23_2582185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_2582185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582185 prefixEnd_2582185 := by exact prefixLift 2582185
  have htrace : WordTrace (prefixWord ++ tailWord_2582185) baseStart_2582185 baseEnd_2582185 := by
    simpa [prefixWord, tailWord_2582185, baseEnd_2582185] using wordTrace_append hprefix tailTrace_2582185
  have hstable : (prefixWord ++ tailWord_2582185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582185).length < 2 ^ (prefixWord ++ tailWord_2582185).sum := by decide
  have hdescent : baseEnd_2582185 < baseStart_2582185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582189 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2582189 : Nat := 118140960795 + 2582189 * 2 ^ 59
def prefixEnd_2582189 : Nat := 4983230072969 + 3 ^ 40 * 2582189 * 2
def baseEnd_2582189 : Nat := 1325904097752702907362235

theorem tailTrace_2582189 : CollatzResearch.WordTrace tailWord_2582189 prefixEnd_2582189 1325904097752702907362235 := by
  unfold tailWord_2582189
  simp only [CollatzResearch.WordTrace]
  refine ⟨94180170042177730616285621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62786780028118487077523747 94180170042177730616285621)
  ·
    refine ⟨8829390941454162245276777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94180170042177730616285621 8829390941454162245276777)
    ·
      refine ⟨6622043206090621683957583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8829390941454162245276777 6622043206090621683957583)
      ·
        refine ⟨9933064809135932525936375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6622043206090621683957583 9933064809135932525936375)
        ·
          refine ⟨14899597213703898788904563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9933064809135932525936375 14899597213703898788904563)
          ·
            refine ⟨22349395820555848183356845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14899597213703898788904563 22349395820555848183356845)
            ·
              refine ⟨8381023432708443068758817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22349395820555848183356845 8381023432708443068758817)
              ·
                refine ⟨6285767574531332301569113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8381023432708443068758817 6285767574531332301569113)
                ·
                  refine ⟨4714325680898499226176835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6285767574531332301569113 4714325680898499226176835)
                  ·
                    refine ⟨7071488521347748839265253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4714325680898499226176835 7071488521347748839265253)
                    ·
                      refine ⟨1325904097752702907362235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7071488521347748839265253 1325904097752702907362235)
                      ·
                        rfl

theorem cell23_2582189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2582189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582189 prefixEnd_2582189 := by exact prefixLift 2582189
  have htrace : WordTrace (prefixWord ++ tailWord_2582189) baseStart_2582189 baseEnd_2582189 := by
    simpa [prefixWord, tailWord_2582189, baseEnd_2582189] using wordTrace_append hprefix tailTrace_2582189
  have hstable : (prefixWord ++ tailWord_2582189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582189).length < 2 ^ (prefixWord ++ tailWord_2582189).sum := by decide
  have hdescent : baseEnd_2582189 < baseStart_2582189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582192 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 3]
def baseStart_2582192 : Nat := 118140960795 + 2582192 * 2 ^ 59
def prefixEnd_2582192 : Nat := 4983230072969 + 3 ^ 40 * 2582192 * 2
def baseEnd_2582192 : Nat := 1325905638194666395624721

theorem tailTrace_2582192 : CollatzResearch.WordTrace tailWord_2582192 prefixEnd_2582192 1325905638194666395624721 := by
  unfold tailWord_2582192
  simp only [CollatzResearch.WordTrace]
  refine ⟨47090139730583431064322415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62786852974111241419096553 47090139730583431064322415)
  ·
    refine ⟨70635209595875146596483623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47090139730583431064322415 70635209595875146596483623)
    ·
      refine ⟨105952814393812719894725435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70635209595875146596483623 105952814393812719894725435)
      ·
        refine ⟨158929221590719079842088153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105952814393812719894725435 158929221590719079842088153)
        ·
          refine ⟨119196916193039309881566115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158929221590719079842088153 119196916193039309881566115)
          ·
            refine ⟨178795374289558964822349173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119196916193039309881566115 178795374289558964822349173)
            ·
              refine ⟨16762066339646152952095235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178795374289558964822349173 16762066339646152952095235)
              ·
                refine ⟨25143099509469229428142853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16762066339646152952095235 25143099509469229428142853)
                ·
                  refine ⟨4714331158025480517776785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25143099509469229428142853 4714331158025480517776785)
                  ·
                    refine ⟨3535748368519110388332589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4714331158025480517776785 3535748368519110388332589)
                    ·
                      refine ⟨1325905638194666395624721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3535748368519110388332589 1325905638194666395624721)
                      ·
                        rfl

theorem cell23_2582192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 3].length) (baseStart_2582192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582192 prefixEnd_2582192 := by exact prefixLift 2582192
  have htrace : WordTrace (prefixWord ++ tailWord_2582192) baseStart_2582192 baseEnd_2582192 := by
    simpa [prefixWord, tailWord_2582192, baseEnd_2582192] using wordTrace_append hprefix tailTrace_2582192
  have hstable : (prefixWord ++ tailWord_2582192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582192).length < 2 ^ (prefixWord ++ tailWord_2582192).sum := by decide
  have hdescent : baseEnd_2582192 < baseStart_2582192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582195 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 8]
def baseStart_2582195 : Nat := 118140960795 + 2582195 * 2 ^ 59
def prefixEnd_2582195 : Nat := 4983230072969 + 3 ^ 40 * 2582195 * 2
def baseEnd_2582195 : Nat := 147323019848514431543023

theorem tailTrace_2582195 : CollatzResearch.WordTrace tailWord_2582195 prefixEnd_2582195 147323019848514431543023 := by
  unfold tailWord_2582195
  simp only [CollatzResearch.WordTrace]
  refine ⟨94180388880155993641004039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62786925920103995760669359 94180388880155993641004039)
  ·
    refine ⟨141270583320233990461506059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94180388880155993641004039 141270583320233990461506059)
    ·
      refine ⟨211905874980350985692259089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141270583320233990461506059 211905874980350985692259089)
      ·
        refine ⟨158929406235263239269194317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211905874980350985692259089 158929406235263239269194317)
        ·
          refine ⟨59598527338223714725947869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158929406235263239269194317 59598527338223714725947869)
          ·
            refine ⟨22349447751833893022230451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59598527338223714725947869 22349447751833893022230451)
            ·
              refine ⟨33524171627750839533345677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22349447751833893022230451 33524171627750839533345677)
              ·
                refine ⟨12571564360406564825004629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33524171627750839533345677 12571564360406564825004629)
                ·
                  refine ⟨147323019848514431543023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12571564360406564825004629 147323019848514431543023)
                  ·
                    rfl

theorem cell23_2582195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 8].length) (baseStart_2582195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582195 prefixEnd_2582195 := by exact prefixLift 2582195
  have htrace : WordTrace (prefixWord ++ tailWord_2582195) baseStart_2582195 baseEnd_2582195 := by
    simpa [prefixWord, tailWord_2582195, baseEnd_2582195] using wordTrace_append hprefix tailTrace_2582195
  have hstable : (prefixWord ++ tailWord_2582195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582195).length < 2 ^ (prefixWord ++ tailWord_2582195).sum := by decide
  have hdescent : baseEnd_2582195 < baseStart_2582195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582199 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 3, 4]
def baseStart_2582199 : Nat := 118140960795 + 2582199 * 2 ^ 59
def prefixEnd_2582199 : Nat := 4983230072969 + 3 ^ 40 * 2582199 * 2
def baseEnd_2582199 : Nat := 441969744186415956079063

theorem tailTrace_2582199 : CollatzResearch.WordTrace tailWord_2582199 prefixEnd_2582199 441969744186415956079063 := by
  unfold tailWord_2582199
  simp only [CollatzResearch.WordTrace]
  refine ⟨94180534772141502324149651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62787023181427668216099767 94180534772141502324149651)
  ·
    refine ⟨141270802158212253486224477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94180534772141502324149651 141270802158212253486224477)
    ·
      refine ⟨52976550809329595057334179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141270802158212253486224477 52976550809329595057334179)
      ·
        refine ⟨79464826213994392586001269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52976550809329595057334179 79464826213994392586001269)
        ·
          refine ⟨7449827457561974304937619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79464826213994392586001269 7449827457561974304937619)
          ·
            refine ⟨11174741186342961457406429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7449827457561974304937619 11174741186342961457406429)
            ·
              refine ⟨4190527944878610546527411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11174741186342961457406429 4190527944878610546527411)
              ·
                refine ⟨6285791917317915819791117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4190527944878610546527411 6285791917317915819791117)
                ·
                  refine ⟨2357171968994218432421669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6285791917317915819791117 2357171968994218432421669)
                  ·
                    refine ⟨441969744186415956079063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2357171968994218432421669 441969744186415956079063)
                    ·
                      rfl

theorem cell23_2582199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_2582199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582199 prefixEnd_2582199 := by exact prefixLift 2582199
  have htrace : WordTrace (prefixWord ++ tailWord_2582199) baseStart_2582199 baseEnd_2582199 := by
    simpa [prefixWord, tailWord_2582199, baseEnd_2582199] using wordTrace_append hprefix tailTrace_2582199
  have hstable : (prefixWord ++ tailWord_2582199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582199).length < 2 ^ (prefixWord ++ tailWord_2582199).sum := by decide
  have hdescent : baseEnd_2582199 < baseStart_2582199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582226 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2582226 : Nat := 118140960795 + 2582226 * 2 ^ 59
def prefixEnd_2582226 : Nat := 4983230072969 + 3 ^ 40 * 2582226 * 2
def baseEnd_2582226 : Nat := 1325923096536919262599565

theorem tailTrace_2582226 : CollatzResearch.WordTrace tailWord_2582226 prefixEnd_2582226 1325923096536919262599565 := by
  unfold tailWord_2582226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23545379885760921483845633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62787679695362457290255021 23545379885760921483845633)
  ·
    refine ⟨17659034914320691112884225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23545379885760921483845633 17659034914320691112884225)
    ·
      refine ⟨13244276185740518334663169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17659034914320691112884225 13244276185740518334663169)
      ·
        refine ⟨9933207139305388750997377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13244276185740518334663169 9933207139305388750997377)
        ·
          refine ⟨7449905354479041563248033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9933207139305388750997377 7449905354479041563248033)
          ·
            refine ⟨5587429015859281172436025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7449905354479041563248033 5587429015859281172436025)
            ·
              refine ⟨4190571761894460879327019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5587429015859281172436025 4190571761894460879327019)
              ·
                refine ⟨6285857642841691318990529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4190571761894460879327019 6285857642841691318990529)
                ·
                  refine ⟨4714393232131268489242897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6285857642841691318990529 4714393232131268489242897)
                  ·
                    refine ⟨3535794924098451366932173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4714393232131268489242897 3535794924098451366932173)
                    ·
                      refine ⟨1325923096536919262599565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3535794924098451366932173 1325923096536919262599565)
                      ·
                        rfl

theorem cell23_2582226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2582226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582226 prefixEnd_2582226 := by exact prefixLift 2582226
  have htrace : WordTrace (prefixWord ++ tailWord_2582226) baseStart_2582226 baseEnd_2582226 := by
    simpa [prefixWord, tailWord_2582226, baseEnd_2582226] using wordTrace_append hprefix tailTrace_2582226
  have hstable : (prefixWord ++ tailWord_2582226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582226).length < 2 ^ (prefixWord ++ tailWord_2582226).sum := by decide
  have hdescent : baseEnd_2582226 < baseStart_2582226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582290 : List Nat := [3, 2, 4, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_2582290 : Nat := 118140960795 + 2582290 * 2 ^ 59
def prefixEnd_2582290 : Nat := 4983230072969 + 3 ^ 40 * 2582290 * 2
def baseEnd_2582290 : Nat := 1325955959298807012199271

theorem tailTrace_2582290 : CollatzResearch.WordTrace tailWord_2582290 prefixEnd_2582290 1325955959298807012199271 := by
  unfold tailWord_2582290
  simp only [CollatzResearch.WordTrace]
  refine ⟨23545963453702956216428081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62789235876541216577141549 23545963453702956216428081)
  ·
    refine ⟨17659472590277217162321061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23545963453702956216428081 17659472590277217162321061)
    ·
      refine ⟨3311151110676978217935199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17659472590277217162321061 3311151110676978217935199)
      ·
        refine ⟨4966726666015467326902799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3311151110676978217935199 4966726666015467326902799)
        ·
          refine ⟨7450089999023200990354199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4966726666015467326902799 7450089999023200990354199)
          ·
            refine ⟨11175134998534801485531299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7450089999023200990354199 11175134998534801485531299)
            ·
              refine ⟨16762702497802202228296949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11175134998534801485531299 16762702497802202228296949)
              ·
                refine ⟨1571503359168956458902839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16762702497802202228296949 1571503359168956458902839)
                ·
                  refine ⟨2357255038753434688354259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571503359168956458902839 2357255038753434688354259)
                  ·
                    refine ⟨3535882558130152032531389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2357255038753434688354259 3535882558130152032531389)
                    ·
                      refine ⟨1325955959298807012199271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3535882558130152032531389 1325955959298807012199271)
                      ·
                        rfl

theorem cell23_2582290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_2582290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582290 prefixEnd_2582290 := by exact prefixLift 2582290
  have htrace : WordTrace (prefixWord ++ tailWord_2582290) baseStart_2582290 baseEnd_2582290 := by
    simpa [prefixWord, tailWord_2582290, baseEnd_2582290] using wordTrace_append hprefix tailTrace_2582290
  have hstable : (prefixWord ++ tailWord_2582290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582290).length < 2 ^ (prefixWord ++ tailWord_2582290).sum := by decide
  have hdescent : baseEnd_2582290 < baseStart_2582290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582296 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 1, 1, 4]
def baseStart_2582296 : Nat := 118140960795 + 2582296 * 2 ^ 59
def prefixEnd_2582296 : Nat := 4983230072969 + 3 ^ 40 * 2582296 * 2
def baseEnd_2582296 : Nat := 1325959040182733988724243

theorem tailTrace_2582296 : CollatzResearch.WordTrace tailWord_2582296 prefixEnd_2582296 1325959040182733988724243 := by
  unfold tailWord_2582296
  simp only [CollatzResearch.WordTrace]
  refine ⟨47092036326395043945215371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62789381768526725260287161 47092036326395043945215371)
  ·
    refine ⟨70638054489592565917823057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47092036326395043945215371 70638054489592565917823057)
    ·
      refine ⟨52978540867194424438367293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70638054489592565917823057 52978540867194424438367293)
      ·
        refine ⟨19866952825197909164387735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52978540867194424438367293 19866952825197909164387735)
        ·
          refine ⟨29800429237796863746581603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19866952825197909164387735 29800429237796863746581603)
          ·
            refine ⟨44700643856695295619872405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29800429237796863746581603 44700643856695295619872405)
            ·
              refine ⟨2095342680782591982181519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44700643856695295619872405 2095342680782591982181519)
              ·
                refine ⟨3143014021173887973272279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095342680782591982181519 3143014021173887973272279)
                ·
                  refine ⟨4714521031760831959908419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143014021173887973272279 4714521031760831959908419)
                  ·
                    refine ⟨7071781547641247939862629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4714521031760831959908419 7071781547641247939862629)
                    ·
                      refine ⟨1325959040182733988724243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7071781547641247939862629 1325959040182733988724243)
                      ·
                        rfl

theorem cell23_2582296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_2582296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582296 prefixEnd_2582296 := by exact prefixLift 2582296
  have htrace : WordTrace (prefixWord ++ tailWord_2582296) baseStart_2582296 baseEnd_2582296 := by
    simpa [prefixWord, tailWord_2582296, baseEnd_2582296] using wordTrace_append hprefix tailTrace_2582296
  have hstable : (prefixWord ++ tailWord_2582296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582296).length < 2 ^ (prefixWord ++ tailWord_2582296).sum := by decide
  have hdescent : baseEnd_2582296 < baseStart_2582296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582299 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 1, 2, 3]
def baseStart_2582299 : Nat := 118140960795 + 2582299 * 2 ^ 59
def prefixEnd_2582299 : Nat := 4983230072969 + 3 ^ 40 * 2582299 * 2
def baseEnd_2582299 : Nat := 1325960580624697476986729

theorem tailTrace_2582299 : CollatzResearch.WordTrace tailWord_2582299 prefixEnd_2582299 1325960580624697476986729 := by
  unfold tailWord_2582299
  simp only [CollatzResearch.WordTrace]
  refine ⟨94184182071779219402789951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62789454714519479601859967 94184182071779219402789951)
  ·
    refine ⟨141276273107668829104184927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94184182071779219402789951 141276273107668829104184927)
    ·
      refine ⟨211914409661503243656277391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141276273107668829104184927 211914409661503243656277391)
      ·
        refine ⟨317871614492254865484416087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211914409661503243656277391 317871614492254865484416087)
        ·
          refine ⟨476807421738382298226624131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317871614492254865484416087 476807421738382298226624131)
          ·
            refine ⟨715211132607573447339936197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476807421738382298226624131 715211132607573447339936197)
            ·
              refine ⟨134102087363920021376238037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 715211132607573447339936197 134102087363920021376238037)
              ·
                refine ⟨3143017672591875501005579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 134102087363920021376238037 3143017672591875501005579)
                ·
                  refine ⟨4714526508887813251508369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143017672591875501005579 4714526508887813251508369)
                  ·
                    refine ⟨3535894881665859938631277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4714526508887813251508369 3535894881665859938631277)
                    ·
                      refine ⟨1325960580624697476986729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3535894881665859938631277 1325960580624697476986729)
                      ·
                        rfl

theorem cell23_2582299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 2, 3].length) (baseStart_2582299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582299 prefixEnd_2582299 := by exact prefixLift 2582299
  have htrace : WordTrace (prefixWord ++ tailWord_2582299) baseStart_2582299 baseEnd_2582299 := by
    simpa [prefixWord, tailWord_2582299, baseEnd_2582299] using wordTrace_append hprefix tailTrace_2582299
  have hstable : (prefixWord ++ tailWord_2582299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582299).length < 2 ^ (prefixWord ++ tailWord_2582299).sum := by decide
  have hdescent : baseEnd_2582299 < baseStart_2582299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582323 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 2, 4]
def baseStart_2582323 : Nat := 118140960795 + 2582323 * 2 ^ 59
def prefixEnd_2582323 : Nat := 4983230072969 + 3 ^ 40 * 2582323 * 2
def baseEnd_2582323 : Nat := 441990968053468461028873

theorem tailTrace_2582323 : CollatzResearch.WordTrace tailWord_2582323 prefixEnd_2582323 441990968053468461028873 := by
  unfold tailWord_2582323
  simp only [CollatzResearch.WordTrace]
  refine ⟨94185057423692271501663623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62790038282461514334442415 94185057423692271501663623)
  ·
    refine ⟨141277586135538407252495435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94185057423692271501663623 141277586135538407252495435)
    ·
      refine ⟨211916379203307610878743153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141277586135538407252495435 211916379203307610878743153)
      ·
        refine ⟨158937284402480708159057365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211916379203307610878743153 158937284402480708159057365)
        ·
          refine ⟨3725092603183141597477907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 158937284402480708159057365 3725092603183141597477907)
          ·
            refine ⟨5587638904774712396216861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725092603183141597477907 5587638904774712396216861)
            ·
              refine ⟨2095364589290517148581323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5587638904774712396216861 2095364589290517148581323)
              ·
                refine ⟨3143046883935775722871985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095364589290517148581323 3143046883935775722871985)
                ·
                  refine ⟨2357285162951831792153989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3143046883935775722871985 2357285162951831792153989)
                  ·
                    refine ⟨441990968053468461028873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2357285162951831792153989 441990968053468461028873)
                    ·
                      rfl

theorem cell23_2582323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 2, 4].length) (baseStart_2582323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582323 prefixEnd_2582323 := by exact prefixLift 2582323
  have htrace : WordTrace (prefixWord ++ tailWord_2582323) baseStart_2582323 baseEnd_2582323 := by
    simpa [prefixWord, tailWord_2582323, baseEnd_2582323] using wordTrace_append hprefix tailTrace_2582323
  have hstable : (prefixWord ++ tailWord_2582323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582323).length < 2 ^ (prefixWord ++ tailWord_2582323).sum := by decide
  have hdescent : baseEnd_2582323 < baseStart_2582323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582326 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2582326 : Nat := 118140960795 + 2582326 * 2 ^ 59
def prefixEnd_2582326 : Nat := 4983230072969 + 3 ^ 40 * 2582326 * 2
def baseEnd_2582326 : Nat := 1325974444602368871349105

theorem tailTrace_2582326 : CollatzResearch.WordTrace tailWord_2582326 prefixEnd_2582326 1325974444602368871349105 := by
  unfold tailWord_2582326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5886572927667587688376427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62790111228454268676015221 5886572927667587688376427)
  ·
    refine ⟨8829859391501381532564641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5886572927667587688376427 8829859391501381532564641)
    ·
      refine ⟨6622394543626036149423481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8829859391501381532564641 6622394543626036149423481)
      ·
        refine ⟨4966795907719527112067611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6622394543626036149423481 4966795907719527112067611)
        ·
          refine ⟨7450193861579290668101417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4966795907719527112067611 7450193861579290668101417)
          ·
            refine ⟨5587645396184468001076063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7450193861579290668101417 5587645396184468001076063)
            ·
              refine ⟨8381468094276702001614095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5587645396184468001076063 8381468094276702001614095)
              ·
                refine ⟨12572202141415053002421143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8381468094276702001614095 12572202141415053002421143)
                ·
                  refine ⟨18858303212122579503631715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12572202141415053002421143 18858303212122579503631715)
                  ·
                    refine ⟨28287454818183869255447573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18858303212122579503631715 28287454818183869255447573)
                    ·
                      refine ⟨1325974444602368871349105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28287454818183869255447573 1325974444602368871349105)
                      ·
                        rfl

theorem cell23_2582326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2582326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582326 prefixEnd_2582326 := by exact prefixLift 2582326
  have htrace : WordTrace (prefixWord ++ tailWord_2582326) baseStart_2582326 baseEnd_2582326 := by
    simpa [prefixWord, tailWord_2582326, baseEnd_2582326] using wordTrace_append hprefix tailTrace_2582326
  have hstable : (prefixWord ++ tailWord_2582326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582326).length < 2 ^ (prefixWord ++ tailWord_2582326).sum := by decide
  have hdescent : baseEnd_2582326 < baseStart_2582326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582332 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_2582332 : Nat := 118140960795 + 2582332 * 2 ^ 59
def prefixEnd_2582332 : Nat := 4983230072969 + 3 ^ 40 * 2582332 * 2
def baseEnd_2582332 : Nat := 441992508495431949291359

theorem tailTrace_2582332 : CollatzResearch.WordTrace tailWord_2582332 prefixEnd_2582332 441992508495431949291359 := by
  unfold tailWord_2582332
  simp only [CollatzResearch.WordTrace]
  refine ⟨47092692840329833019370625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62790257120439777359160833 47092692840329833019370625)
  ·
    refine ⟨35319519630247374764527969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47092692840329833019370625 35319519630247374764527969)
    ·
      refine ⟨26489639722685531073395977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35319519630247374764527969 26489639722685531073395977)
      ·
        refine ⟨19867229792014148305046983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26489639722685531073395977 19867229792014148305046983)
        ·
          refine ⟨29800844688021222457570475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19867229792014148305046983 29800844688021222457570475)
          ·
            refine ⟨44701267032031833686355713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29800844688021222457570475 44701267032031833686355713)
            ·
              refine ⟨33525950274023875264766785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44701267032031833686355713 33525950274023875264766785)
              ·
                refine ⟨25144462705517906448575089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33525950274023875264766785 25144462705517906448575089)
                ·
                  refine ⟨18858347029138429836431317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25144462705517906448575089 18858347029138429836431317)
                  ·
                    refine ⟨441992508495431949291359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18858347029138429836431317 441992508495431949291359)
                    ·
                      rfl

theorem cell23_2582332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_2582332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582332 prefixEnd_2582332 := by exact prefixLift 2582332
  have htrace : WordTrace (prefixWord ++ tailWord_2582332) baseStart_2582332 baseEnd_2582332 := by
    simpa [prefixWord, tailWord_2582332, baseEnd_2582332] using wordTrace_append hprefix tailTrace_2582332
  have hstable : (prefixWord ++ tailWord_2582332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582332).length < 2 ^ (prefixWord ++ tailWord_2582332).sum := by decide
  have hdescent : baseEnd_2582332 < baseStart_2582332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582333 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2582333 : Nat := 118140960795 + 2582333 * 2 ^ 59
def prefixEnd_2582333 : Nat := 4983230072969 + 3 ^ 40 * 2582333 * 2
def baseEnd_2582333 : Nat := 1325978038966950343961573

theorem tailTrace_2582333 : CollatzResearch.WordTrace tailWord_2582333 prefixEnd_2582333 1325978038966950343961573 := by
  unfold tailWord_2582333
  simp only [CollatzResearch.WordTrace]
  refine ⟨94185422153656043209527653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62790281435770695473018435 94185422153656043209527653)
  ·
    refine ⟨17659766653810508101786435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94185422153656043209527653 17659766653810508101786435)
    ·
      refine ⟨26489649980715762152679653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17659766653810508101786435 26489649980715762152679653)
      ·
        refine ⟨4966809371384205403627435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26489649980715762152679653 4966809371384205403627435)
        ·
          refine ⟨7450214057076308105441153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4966809371384205403627435 7450214057076308105441153)
          ·
            refine ⟨5587660542807231079080865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7450214057076308105441153 5587660542807231079080865)
            ·
              refine ⟨4190745407105423309310649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5587660542807231079080865 4190745407105423309310649)
              ·
                refine ⟨3143059055329067481982987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4190745407105423309310649 3143059055329067481982987)
                ·
                  refine ⟨4714588582993601222974481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143059055329067481982987 4714588582993601222974481)
                  ·
                    refine ⟨3535941437245200917230861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4714588582993601222974481 3535941437245200917230861)
                    ·
                      refine ⟨1325978038966950343961573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3535941437245200917230861 1325978038966950343961573)
                      ·
                        rfl

theorem cell23_2582333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2582333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582333 prefixEnd_2582333 := by exact prefixLift 2582333
  have htrace : WordTrace (prefixWord ++ tailWord_2582333) baseStart_2582333 baseEnd_2582333 := by
    simpa [prefixWord, tailWord_2582333, baseEnd_2582333] using wordTrace_append hprefix tailTrace_2582333
  have hstable : (prefixWord ++ tailWord_2582333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582333).length < 2 ^ (prefixWord ++ tailWord_2582333).sum := by decide
  have hdescent : baseEnd_2582333 < baseStart_2582333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582352 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_2582352 : Nat := 118140960795 + 2582352 * 2 ^ 59
def prefixEnd_2582352 : Nat := 4983230072969 + 3 ^ 40 * 2582352 * 2
def baseEnd_2582352 : Nat := 1325987795099385769623985

theorem tailTrace_2582352 : CollatzResearch.WordTrace tailWord_2582352 prefixEnd_2582352 1325987795099385769623985 := by
  unfold tailWord_2582352
  simp only [CollatzResearch.WordTrace]
  refine ⟨47093057570293604727234655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62790743427058139636312873 47093057570293604727234655)
  ·
    refine ⟨70639586355440407090851983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47093057570293604727234655 70639586355440407090851983)
    ·
      refine ⟨105959379533160610636277975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70639586355440407090851983 105959379533160610636277975)
      ·
        refine ⟨158939069299740915954416963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105959379533160610636277975 158939069299740915954416963)
        ·
          refine ⟨238408603949611373931625445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158939069299740915954416963 238408603949611373931625445)
          ·
            refine ⟨44701613240552132612179771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238408603949611373931625445 44701613240552132612179771)
            ·
              refine ⟨67052419860828198918269657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44701613240552132612179771 67052419860828198918269657)
              ·
                refine ⟨50289314895621149188702243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67052419860828198918269657 50289314895621149188702243)
                ·
                  refine ⟨75433972343431723783053365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50289314895621149188702243 75433972343431723783053365)
                  ·
                    refine ⟨7071934907196724104661253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75433972343431723783053365 7071934907196724104661253)
                    ·
                      refine ⟨1325987795099385769623985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7071934907196724104661253 1325987795099385769623985)
                      ·
                        rfl

theorem cell23_2582352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_2582352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582352 prefixEnd_2582352 := by exact prefixLift 2582352
  have htrace : WordTrace (prefixWord ++ tailWord_2582352) baseStart_2582352 baseEnd_2582352 := by
    simpa [prefixWord, tailWord_2582352, baseEnd_2582352] using wordTrace_append hprefix tailTrace_2582352
  have hstable : (prefixWord ++ tailWord_2582352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582352).length < 2 ^ (prefixWord ++ tailWord_2582352).sum := by decide
  have hdescent : baseEnd_2582352 < baseStart_2582352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582364 : List Nat := [2, 2, 4, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_2582364 : Nat := 118140960795 + 2582364 * 2 ^ 59
def prefixEnd_2582364 : Nat := 4983230072969 + 3 ^ 40 * 2582364 * 2
def baseEnd_2582364 : Nat := 1325993956867239722673931

theorem tailTrace_2582364 : CollatzResearch.WordTrace tailWord_2582364 prefixEnd_2582364 1325993956867239722673931 := by
  unfold tailWord_2582364
  simp only [CollatzResearch.WordTrace]
  refine ⟨47093276408271867751953073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62791035211029157002604097 47093276408271867751953073)
  ·
    refine ⟨35319957306203900813964805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47093276408271867751953073 35319957306203900813964805)
    ·
      refine ⟨6622491994913231402618401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35319957306203900813964805 6622491994913231402618401)
      ·
        refine ⟨4966868996184923551963801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6622491994913231402618401 4966868996184923551963801)
        ·
          refine ⟨3725151747138692663972851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4966868996184923551963801 3725151747138692663972851)
          ·
            refine ⟨5587727620708038995959277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725151747138692663972851 5587727620708038995959277)
            ·
              refine ⟨2095397857765514623484729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5587727620708038995959277 2095397857765514623484729)
              ·
                refine ⟨1571548393324135967613547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2095397857765514623484729 1571548393324135967613547)
                ·
                  refine ⟨2357322589986203951420321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571548393324135967613547 2357322589986203951420321)
                  ·
                    refine ⟨1767991942489652963565241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2357322589986203951420321 1767991942489652963565241)
                    ·
                      refine ⟨1325993956867239722673931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1767991942489652963565241 1325993956867239722673931)
                      ·
                        rfl

theorem cell23_2582364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_2582364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582364 prefixEnd_2582364 := by exact prefixLift 2582364
  have htrace : WordTrace (prefixWord ++ tailWord_2582364) baseStart_2582364 baseEnd_2582364 := by
    simpa [prefixWord, tailWord_2582364, baseEnd_2582364] using wordTrace_append hprefix tailTrace_2582364
  have hstable : (prefixWord ++ tailWord_2582364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582364).length < 2 ^ (prefixWord ++ tailWord_2582364).sum := by decide
  have hdescent : baseEnd_2582364 < baseStart_2582364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582380 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 3]
def baseStart_2582380 : Nat := 118140960795 + 2582380 * 2 ^ 59
def prefixEnd_2582380 : Nat := 4983230072969 + 3 ^ 40 * 2582380 * 2
def baseEnd_2582380 : Nat := 1326002172557711660073857

theorem tailTrace_2582380 : CollatzResearch.WordTrace tailWord_2582380 prefixEnd_2582380 1326002172557711660073857 := by
  unfold tailWord_2582380
  simp only [CollatzResearch.WordTrace]
  refine ⟨47093568192242885118244297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62791424256323846824325729 47093568192242885118244297)
  ·
    refine ⟨35320176144182163838683223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47093568192242885118244297 35320176144182163838683223)
    ·
      refine ⟨52980264216273245758024835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35320176144182163838683223 52980264216273245758024835)
      ·
        refine ⟨79470396324409868637037253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52980264216273245758024835 79470396324409868637037253)
        ·
          refine ⟨14900699310826850369444485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79470396324409868637037253 14900699310826850369444485)
          ·
            refine ⟨2793881120780034444270841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14900699310826850369444485 2793881120780034444270841)
            ·
              refine ⟨2095410840585025833203131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2793881120780034444270841 2095410840585025833203131)
              ·
                refine ⟨3143116260877538749804697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095410840585025833203131 3143116260877538749804697)
                ·
                  refine ⟨2357337195658154062353523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3143116260877538749804697 2357337195658154062353523)
                  ·
                    refine ⟨3536005793487231093530285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2357337195658154062353523 3536005793487231093530285)
                    ·
                      refine ⟨1326002172557711660073857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3536005793487231093530285 1326002172557711660073857)
                      ·
                        rfl

theorem cell23_2582380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_2582380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582380 prefixEnd_2582380 := by exact prefixLift 2582380
  have htrace : WordTrace (prefixWord ++ tailWord_2582380) baseStart_2582380 baseEnd_2582380 := by
    simpa [prefixWord, tailWord_2582380, baseEnd_2582380] using wordTrace_append hprefix tailTrace_2582380
  have hstable : (prefixWord ++ tailWord_2582380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582380).length < 2 ^ (prefixWord ++ tailWord_2582380).sum := by decide
  have hdescent : baseEnd_2582380 < baseStart_2582380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582386 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 1, 4, 2]
def baseStart_2582386 : Nat := 118140960795 + 2582386 * 2 ^ 59
def prefixEnd_2582386 : Nat := 4983230072969 + 3 ^ 40 * 2582386 * 2
def baseEnd_2582386 : Nat := 1326005253441638636598829

theorem tailTrace_2582386 : CollatzResearch.WordTrace tailWord_2582386 prefixEnd_2582386 1326005253441638636598829 := by
  unfold tailWord_2582386
  simp only [CollatzResearch.WordTrace]
  refine ⟨23546838805616008315301753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62791570148309355507471341 23546838805616008315301753)
  ·
    refine ⟨17660129104212006236476315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23546838805616008315301753 17660129104212006236476315)
    ·
      refine ⟨26490193656318009354714473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17660129104212006236476315 26490193656318009354714473)
      ·
        refine ⟨19867645242238507016035855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26490193656318009354714473 19867645242238507016035855)
        ·
          refine ⟨29801467863357760524053783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19867645242238507016035855 29801467863357760524053783)
          ·
            refine ⟨44702201795036640786080675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29801467863357760524053783 44702201795036640786080675)
            ·
              refine ⟨67053302692554961179121013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44702201795036640786080675 67053302692554961179121013)
              ·
                refine ⟨6286247127427027610542595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67053302692554961179121013 6286247127427027610542595)
                ·
                  refine ⟨9429370691140541415813893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6286247127427027610542595 9429370691140541415813893)
                  ·
                    refine ⟨1768007004588851515465105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9429370691140541415813893 1768007004588851515465105)
                    ·
                      refine ⟨1326005253441638636598829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768007004588851515465105 1326005253441638636598829)
                      ·
                        rfl

theorem cell23_2582386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_2582386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582386 prefixEnd_2582386 := by exact prefixLift 2582386
  have htrace : WordTrace (prefixWord ++ tailWord_2582386) baseStart_2582386 baseEnd_2582386 := by
    simpa [prefixWord, tailWord_2582386, baseEnd_2582386] using wordTrace_append hprefix tailTrace_2582386
  have hstable : (prefixWord ++ tailWord_2582386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582386).length < 2 ^ (prefixWord ++ tailWord_2582386).sum := by decide
  have hdescent : baseEnd_2582386 < baseStart_2582386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582389 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2582389 : Nat := 118140960795 + 2582389 * 2 ^ 59
def prefixEnd_2582389 : Nat := 4983230072969 + 3 ^ 40 * 2582389 * 2
def baseEnd_2582389 : Nat := 1326006793883602124861315

theorem tailTrace_2582389 : CollatzResearch.WordTrace tailWord_2582389 prefixEnd_2582389 1326006793883602124861315 := by
  unfold tailWord_2582389
  simp only [CollatzResearch.WordTrace]
  refine ⟨94187464641453164773566221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62791643094302109849044147 94187464641453164773566221)
  ·
    refine ⟨35320299240544936790087333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94187464641453164773566221 35320299240544936790087333)
    ·
      refine ⟨6622556107602175648141375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35320299240544936790087333 6622556107602175648141375)
      ·
        refine ⟨9933834161403263472212063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6622556107602175648141375 9933834161403263472212063)
        ·
          refine ⟨14900751242104895208318095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9933834161403263472212063 14900751242104895208318095)
          ·
            refine ⟨22351126863157342812477143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14900751242104895208318095 22351126863157342812477143)
            ·
              refine ⟨33526690294736014218715715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22351126863157342812477143 33526690294736014218715715)
              ·
                refine ⟨50290035442104021328073573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33526690294736014218715715 50290035442104021328073573)
                ·
                  refine ⟨9429381645394503999013795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50290035442104021328073573 9429381645394503999013795)
                  ·
                    refine ⟨14144072468091755998520693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9429381645394503999013795 14144072468091755998520693)
                    ·
                      refine ⟨1326006793883602124861315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14144072468091755998520693 1326006793883602124861315)
                      ·
                        rfl

theorem cell23_2582389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2582389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582389 prefixEnd_2582389 := by exact prefixLift 2582389
  have htrace : WordTrace (prefixWord ++ tailWord_2582389) baseStart_2582389 baseEnd_2582389 := by
    simpa [prefixWord, tailWord_2582389, baseEnd_2582389] using wordTrace_append hprefix tailTrace_2582389
  have hstable : (prefixWord ++ tailWord_2582389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582389).length < 2 ^ (prefixWord ++ tailWord_2582389).sum := by decide
  have hdescent : baseEnd_2582389 < baseStart_2582389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582390 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2582390 : Nat := 118140960795 + 2582390 * 2 ^ 59
def prefixEnd_2582390 : Nat := 4983230072969 + 3 ^ 40 * 2582390 * 2
def baseEnd_2582390 : Nat := 1326007307364256620948811

theorem tailTrace_2582390 : CollatzResearch.WordTrace tailWord_2582390 prefixEnd_2582390 1326007307364256620948811 := by
  unfold tailWord_2582390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5886718819653096371522039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62791667409633027962901749 5886718819653096371522039)
  ·
    refine ⟨8830078229479644557283059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5886718819653096371522039 8830078229479644557283059)
    ·
      refine ⟨13245117344219466835924589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8830078229479644557283059 13245117344219466835924589)
      ·
        refine ⟨4966919004082300063471721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13245117344219466835924589 4966919004082300063471721)
        ·
          refine ⟨3725189253061725047603791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4966919004082300063471721 3725189253061725047603791)
          ·
            refine ⟨5587783879592587571405687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725189253061725047603791 5587783879592587571405687)
            ·
              refine ⟨8381675819388881357108531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5587783879592587571405687 8381675819388881357108531)
              ·
                refine ⟨12572513729083322035662797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8381675819388881357108531 12572513729083322035662797)
                ·
                  refine ⟨4714692648406245763373549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12572513729083322035662797 4714692648406245763373549)
                  ·
                    refine ⟨1768009743152342161265081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4714692648406245763373549 1768009743152342161265081)
                    ·
                      refine ⟨1326007307364256620948811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768009743152342161265081 1326007307364256620948811)
                      ·
                        rfl

theorem cell23_2582390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2582390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582390 prefixEnd_2582390 := by exact prefixLift 2582390
  have htrace : WordTrace (prefixWord ++ tailWord_2582390) baseStart_2582390 baseEnd_2582390 := by
    simpa [prefixWord, tailWord_2582390, baseEnd_2582390] using wordTrace_append hprefix tailTrace_2582390
  have hstable : (prefixWord ++ tailWord_2582390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582390).length < 2 ^ (prefixWord ++ tailWord_2582390).sum := by decide
  have hdescent : baseEnd_2582390 < baseStart_2582390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582420 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_2582420 : Nat := 118140960795 + 2582420 * 2 ^ 59
def prefixEnd_2582420 : Nat := 4983230072969 + 3 ^ 40 * 2582420 * 2
def baseEnd_2582420 : Nat := 1326022711783891503573673

theorem tailTrace_2582420 : CollatzResearch.WordTrace tailWord_2582420 prefixEnd_2582420 1326022711783891503573673 := by
  unfold tailWord_2582420
  simp only [CollatzResearch.WordTrace]
  refine ⟨47094297652170428533972357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62792396869560571378629809 47094297652170428533972357)
  ·
    refine ⟨8830180809781955350119817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47094297652170428533972357 8830180809781955350119817)
    ·
      refine ⟨6622635607336466512589863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8830180809781955350119817 6622635607336466512589863)
      ·
        refine ⟨9933953411004699768884795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6622635607336466512589863 9933953411004699768884795)
        ·
          refine ⟨14900930116507049653327193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9933953411004699768884795 14900930116507049653327193)
          ·
            refine ⟨11175697587380287239995395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14900930116507049653327193 11175697587380287239995395)
            ·
              refine ⟨16763546381070430859993093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11175697587380287239995395 16763546381070430859993093)
              ·
                refine ⟨3143164946450705786248705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16763546381070430859993093 3143164946450705786248705)
                ·
                  refine ⟨2357373709838029339686529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3143164946450705786248705 2357373709838029339686529)
                  ·
                    refine ⟨1768030282378522004764897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2357373709838029339686529 1768030282378522004764897)
                    ·
                      refine ⟨1326022711783891503573673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768030282378522004764897 1326022711783891503573673)
                      ·
                        rfl

theorem cell23_2582420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_2582420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582420 prefixEnd_2582420 := by exact prefixLift 2582420
  have htrace : WordTrace (prefixWord ++ tailWord_2582420) baseStart_2582420 baseEnd_2582420 := by
    simpa [prefixWord, tailWord_2582420, baseEnd_2582420] using wordTrace_append hprefix tailTrace_2582420
  have hstable : (prefixWord ++ tailWord_2582420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582420).length < 2 ^ (prefixWord ++ tailWord_2582420).sum := by decide
  have hdescent : baseEnd_2582420 < baseStart_2582420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582436 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_2582436 : Nat := 118140960795 + 2582436 * 2 ^ 59
def prefixEnd_2582436 : Nat := 4983230072969 + 3 ^ 40 * 2582436 * 2
def baseEnd_2582436 : Nat := 1326030927474363440973599

theorem tailTrace_2582436 : CollatzResearch.WordTrace tailWord_2582436 prefixEnd_2582436 1326030927474363440973599 := by
  unfold tailWord_2582436
  simp only [CollatzResearch.WordTrace]
  refine ⟨47094589436141445900263581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62792785914855261200351441 47094589436141445900263581)
  ·
    refine ⟨17660471038553042212598843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47094589436141445900263581 17660471038553042212598843)
    ·
      refine ⟨26490706557829563318898265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17660471038553042212598843 26490706557829563318898265)
      ·
        refine ⟨19868029918372172489173699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26490706557829563318898265 19868029918372172489173699)
        ·
          refine ⟨29802044877558258733760549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19868029918372172489173699 29802044877558258733760549)
          ·
            refine ⟨5587883414542173512580103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29802044877558258733760549 5587883414542173512580103)
            ·
              refine ⟨8381825121813260268870155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5587883414542173512580103 8381825121813260268870155)
              ·
                refine ⟨12572737682719890403305233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8381825121813260268870155 12572737682719890403305233)
                ·
                  refine ⟨9429553262039917802478925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12572737682719890403305233 9429553262039917802478925)
                  ·
                    refine ⟨3536082473264969175929597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9429553262039917802478925 3536082473264969175929597)
                    ·
                      refine ⟨1326030927474363440973599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3536082473264969175929597 1326030927474363440973599)
                      ·
                        rfl

theorem cell23_2582436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_2582436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582436 prefixEnd_2582436 := by exact prefixLift 2582436
  have htrace : WordTrace (prefixWord ++ tailWord_2582436) baseStart_2582436 baseEnd_2582436 := by
    simpa [prefixWord, tailWord_2582436, baseEnd_2582436] using wordTrace_append hprefix tailTrace_2582436
  have hstable : (prefixWord ++ tailWord_2582436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582436).length < 2 ^ (prefixWord ++ tailWord_2582436).sum := by decide
  have hdescent : baseEnd_2582436 < baseStart_2582436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582460 : List Nat := [2, 2, 2, 5, 1, 1, 2, 3, 5]
def baseStart_2582460 : Nat := 118140960795 + 2582460 * 2 ^ 59
def prefixEnd_2582460 : Nat := 4983230072969 + 3 ^ 40 * 2582460 * 2
def baseEnd_2582460 : Nat := 147338139001119038563721

theorem tailTrace_2582460 : CollatzResearch.WordTrace tailWord_2582460 prefixEnd_2582460 147338139001119038563721 := by
  unfold tailWord_2582460
  simp only [CollatzResearch.WordTrace]
  refine ⟨47095027112097971949700417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62793369482797295932933889 47095027112097971949700417)
  ·
    refine ⟨35321270334073478962275313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47095027112097971949700417 35321270334073478962275313)
    ·
      refine ⟨26490952750555109221706485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35321270334073478962275313 26490952750555109221706485)
      ·
        refine ⟨2483526820364541489534983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26490952750555109221706485 2483526820364541489534983)
        ·
          refine ⟨3725290230546812234302475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2483526820364541489534983 3725290230546812234302475)
          ·
            refine ⟨5587935345820218351453713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725290230546812234302475 5587935345820218351453713)
            ·
              refine ⟨4190951509365163763590285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5587935345820218351453713 4190951509365163763590285)
              ·
                refine ⟨1571606816011936411346357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4190951509365163763590285 1571606816011936411346357)
                ·
                  refine ⟨147338139001119038563721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1571606816011936411346357 147338139001119038563721)
                  ·
                    rfl

theorem cell23_2582460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_2582460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582460 prefixEnd_2582460 := by exact prefixLift 2582460
  have htrace : WordTrace (prefixWord ++ tailWord_2582460) baseStart_2582460 baseEnd_2582460 := by
    simpa [prefixWord, tailWord_2582460, baseEnd_2582460] using wordTrace_append hprefix tailTrace_2582460
  have hstable : (prefixWord ++ tailWord_2582460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582460).length < 2 ^ (prefixWord ++ tailWord_2582460).sum := by decide
  have hdescent : baseEnd_2582460 < baseStart_2582460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582570 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_2582570 : Nat := 118140960795 + 2582570 * 2 ^ 59
def prefixEnd_2582570 : Nat := 4983230072969 + 3 ^ 40 * 2582570 * 2
def baseEnd_2582570 : Nat := 1326099733882065916697983

theorem tailTrace_2582570 : CollatzResearch.WordTrace tailWord_2582570 prefixEnd_2582570 1326099733882065916697983 := by
  unfold tailWord_2582570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23548516563449358171476291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62796044169198288457270109 23548516563449358171476291)
  ·
    refine ⟨35322774845174037257214437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23548516563449358171476291 35322774845174037257214437)
    ·
      refine ⟨6623020283470131985727707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35322774845174037257214437 6623020283470131985727707)
      ·
        refine ⟨9934530425205197978591561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6623020283470131985727707 9934530425205197978591561)
        ·
          refine ⟨7450897818903898483943671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9934530425205197978591561 7450897818903898483943671)
          ·
            refine ⟨11176346728355847725915507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7450897818903898483943671 11176346728355847725915507)
            ·
              refine ⟨16764520092533771588873261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11176346728355847725915507 16764520092533771588873261)
              ·
                refine ⟨6286695034700164345827473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16764520092533771588873261 6286695034700164345827473)
                ·
                  refine ⟨4715021276025123259370605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6286695034700164345827473 4715021276025123259370605)
                  ·
                    refine ⟨1768132978509421222263977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4715021276025123259370605 1768132978509421222263977)
                    ·
                      refine ⟨1326099733882065916697983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768132978509421222263977 1326099733882065916697983)
                      ·
                        rfl

theorem cell23_2582570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_2582570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582570 prefixEnd_2582570 := by exact prefixLift 2582570
  have htrace : WordTrace (prefixWord ++ tailWord_2582570) baseStart_2582570 baseEnd_2582570 := by
    simpa [prefixWord, tailWord_2582570, baseEnd_2582570] using wordTrace_append hprefix tailTrace_2582570
  have hstable : (prefixWord ++ tailWord_2582570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582570).length < 2 ^ (prefixWord ++ tailWord_2582570).sum := by decide
  have hdescent : baseEnd_2582570 < baseStart_2582570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582576 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 1, 6]
def baseStart_2582576 : Nat := 118140960795 + 2582576 * 2 ^ 59
def prefixEnd_2582576 : Nat := 4983230072969 + 3 ^ 40 * 2582576 * 2
def baseEnd_2582576 : Nat := 442034271588664297740985

theorem tailTrace_2582576 : CollatzResearch.WordTrace tailWord_2582576 prefixEnd_2582576 442034271588664297740985 := by
  unfold tailWord_2582576
  simp only [CollatzResearch.WordTrace]
  refine ⟨47097142545887847855311791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62796190061183797140415721 47097142545887847855311791)
  ·
    refine ⟨70645713818831771782967687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47097142545887847855311791 70645713818831771782967687)
    ·
      refine ⟨105968570728247657674451531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70645713818831771782967687 105968570728247657674451531)
      ·
        refine ⟨158952856092371486511677297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105968570728247657674451531 158952856092371486511677297)
        ·
          refine ⟨119214642069278614883757973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158952856092371486511677297 119214642069278614883757973)
          ·
            refine ⟨5588186346997435072676155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119214642069278614883757973 5588186346997435072676155)
            ·
              refine ⟨8382279520496152609014233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5588186346997435072676155 8382279520496152609014233)
              ·
                refine ⟨6286709640372114456760675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8382279520496152609014233 6286709640372114456760675)
                ·
                  refine ⟨9430064460558171685141013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6286709640372114456760675 9430064460558171685141013)
                  ·
                    refine ⟨442034271588664297740985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9430064460558171685141013 442034271588664297740985)
                    ·
                      rfl

theorem cell23_2582576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_2582576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582576 prefixEnd_2582576 := by exact prefixLift 2582576
  have htrace : WordTrace (prefixWord ++ tailWord_2582576) baseStart_2582576 baseEnd_2582576 := by
    simpa [prefixWord, tailWord_2582576, baseEnd_2582576] using wordTrace_append hprefix tailTrace_2582576
  have hstable : (prefixWord ++ tailWord_2582576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582576).length < 2 ^ (prefixWord ++ tailWord_2582576).sum := by decide
  have hdescent : baseEnd_2582576 < baseStart_2582576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582606 : List Nat := [4, 1, 1, 1, 1, 4, 3, 8]
def baseStart_2582606 : Nat := 118140960795 + 2582606 * 2 ^ 59
def prefixEnd_2582606 : Nat := 4983230072969 + 3 ^ 40 * 2582606 * 2
def baseEnd_2582606 : Nat := 49115489599467695401771

theorem tailTrace_2582606 : CollatzResearch.WordTrace tailWord_2582606 prefixEnd_2582606 49115489599467695401771 := by
  unfold tailWord_2582606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11774422410208376354276959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62796919521111340556143781 11774422410208376354276959)
  ·
    refine ⟨17661633615312564531415439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11774422410208376354276959 17661633615312564531415439)
    ·
      refine ⟨26492450422968846797123159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17661633615312564531415439 26492450422968846797123159)
      ·
        refine ⟨39738675634453270195684739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26492450422968846797123159 39738675634453270195684739)
        ·
          refine ⟨59608013451679905293527109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39738675634453270195684739 59608013451679905293527109)
          ·
            refine ⟨11176502522189982242536333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59608013451679905293527109 11176502522189982242536333)
            ·
              refine ⟨4191188445821243340951125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11176502522189982242536333 4191188445821243340951125)
              ·
                refine ⟨49115489599467695401771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4191188445821243340951125 49115489599467695401771)
                ·
                  rfl

theorem cell23_2582606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_2582606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582606 prefixEnd_2582606 := by exact prefixLift 2582606
  have htrace : WordTrace (prefixWord ++ tailWord_2582606) baseStart_2582606 baseEnd_2582606 := by
    simpa [prefixWord, tailWord_2582606, baseEnd_2582606] using wordTrace_append hprefix tailTrace_2582606
  have hstable : (prefixWord ++ tailWord_2582606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582606).length < 2 ^ (prefixWord ++ tailWord_2582606).sum := by decide
  have hdescent : baseEnd_2582606 < baseStart_2582606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582613 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_2582613 : Nat := 118140960795 + 2582613 * 2 ^ 59
def prefixEnd_2582613 : Nat := 4983230072969 + 3 ^ 40 * 2582613 * 2
def baseEnd_2582613 : Nat := 1326121813550209248460285

theorem tailTrace_2582613 : CollatzResearch.WordTrace tailWord_2582613 prefixEnd_2582613 1326121813550209248460285 := by
  unfold tailWord_2582613
  simp only [CollatzResearch.WordTrace]
  refine ⟨94195634592641651029720493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62797089728427767353146995 94195634592641651029720493)
  ·
    refine ⟨35323362972240619136145185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94195634592641651029720493 35323362972240619136145185)
    ·
      refine ⟨26492522229180464352108889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35323362972240619136145185 26492522229180464352108889)
      ·
        refine ⟨19869391671885348264081667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26492522229180464352108889 19869391671885348264081667)
        ·
          refine ⟨29804087507828022396122501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19869391671885348264081667 29804087507828022396122501)
          ·
            refine ⟨5588266407717754199272969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29804087507828022396122501 5588266407717754199272969)
            ·
              refine ⟨4191199805788315649454727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5588266407717754199272969 4191199805788315649454727)
              ·
                refine ⟨6286799708682473474182091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4191199805788315649454727 6286799708682473474182091)
                ·
                  refine ⟨9430199563023710211273137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6286799708682473474182091 9430199563023710211273137)
                  ·
                    refine ⟨7072649672267782658454853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9430199563023710211273137 7072649672267782658454853)
                    ·
                      refine ⟨1326121813550209248460285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7072649672267782658454853 1326121813550209248460285)
                      ·
                        rfl

theorem cell23_2582613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_2582613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582613 prefixEnd_2582613 := by exact prefixLift 2582613
  have htrace : WordTrace (prefixWord ++ tailWord_2582613) baseStart_2582613 baseEnd_2582613 := by
    simpa [prefixWord, tailWord_2582613, baseEnd_2582613] using wordTrace_append hprefix tailTrace_2582613
  have hstable : (prefixWord ++ tailWord_2582613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582613).length < 2 ^ (prefixWord ++ tailWord_2582613).sum := by decide
  have hdescent : baseEnd_2582613 < baseStart_2582613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582633 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 4, 1, 3]
def baseStart_2582633 : Nat := 118140960795 + 2582633 * 2 ^ 59
def prefixEnd_2582633 : Nat := 4983230072969 + 3 ^ 40 * 2582633 * 2
def baseEnd_2582633 : Nat := 1326132083163299170210193

theorem tailTrace_2582633 : CollatzResearch.WordTrace tailWord_2582633 prefixEnd_2582633 1326132083163299170210193 := by
  unfold tailWord_2582633
  simp only [CollatzResearch.WordTrace]
  refine ⟨94196364052569194445448553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62797576035046129630299035 94196364052569194445448553)
  ·
    refine ⟨70647273039426895834086415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94196364052569194445448553 70647273039426895834086415)
    ·
      refine ⟨105970909559140343751129623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70647273039426895834086415 105970909559140343751129623)
      ·
        refine ⟨158956364338710515626694435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105970909559140343751129623 158956364338710515626694435)
        ·
          refine ⟨238434546508065773440041653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158956364338710515626694435 238434546508065773440041653)
          ·
            refine ⟨22353238735131166260003905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 238434546508065773440041653 22353238735131166260003905)
            ·
              refine ⟨16764929051348374695002929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22353238735131166260003905 16764929051348374695002929)
              ·
                refine ⟨12573696788511281021252197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16764929051348374695002929 12573696788511281021252197)
                ·
                  refine ⟨2357568147845865191484787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12573696788511281021252197 2357568147845865191484787)
                  ·
                    refine ⟨3536352221768797787227181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2357568147845865191484787 3536352221768797787227181)
                    ·
                      refine ⟨1326132083163299170210193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3536352221768797787227181 1326132083163299170210193)
                      ·
                        rfl

theorem cell23_2582633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 1, 3].length) (baseStart_2582633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582633 prefixEnd_2582633 := by exact prefixLift 2582633
  have htrace : WordTrace (prefixWord ++ tailWord_2582633) baseStart_2582633 baseEnd_2582633 := by
    simpa [prefixWord, tailWord_2582633, baseEnd_2582633] using wordTrace_append hprefix tailTrace_2582633
  have hstable : (prefixWord ++ tailWord_2582633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582633).length < 2 ^ (prefixWord ++ tailWord_2582633).sum := by decide
  have hdescent : baseEnd_2582633 < baseStart_2582633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582634 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_2582634 : Nat := 118140960795 + 2582634 * 2 ^ 59
def prefixEnd_2582634 : Nat := 4983230072969 + 3 ^ 40 * 2582634 * 2
def baseEnd_2582634 : Nat := 1326132596643953666297689

theorem tailTrace_2582634 : CollatzResearch.WordTrace tailWord_2582634 prefixEnd_2582634 1326132596643953666297689 := by
  unfold tailWord_2582634
  simp only [CollatzResearch.WordTrace]
  refine ⟨23549100131391392904058739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62797600350377047744156637 23549100131391392904058739)
  ·
    refine ⟨35323650197087089356088109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23549100131391392904058739 35323650197087089356088109)
    ·
      refine ⟨13246368823907658508533041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35323650197087089356088109 13246368823907658508533041)
      ·
        refine ⟨9934776617930743881399781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13246368823907658508533041 9934776617930743881399781)
        ·
          refine ⟨1862770615862014477762459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9934776617930743881399781 1862770615862014477762459)
          ·
            refine ⟨2794155923793021716643689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862770615862014477762459 2794155923793021716643689)
            ·
              refine ⟨2095616942844766287482767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2794155923793021716643689 2095616942844766287482767)
              ·
                refine ⟨3143425414267149431224151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095616942844766287482767 3143425414267149431224151)
                ·
                  refine ⟨4715138121400724146836227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143425414267149431224151 4715138121400724146836227)
                  ·
                    refine ⟨7072707182101086220254341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4715138121400724146836227 7072707182101086220254341)
                    ·
                      refine ⟨1326132596643953666297689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7072707182101086220254341 1326132596643953666297689)
                      ·
                        rfl

theorem cell23_2582634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_2582634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582634 prefixEnd_2582634 := by exact prefixLift 2582634
  have htrace : WordTrace (prefixWord ++ tailWord_2582634) baseStart_2582634 baseEnd_2582634 := by
    simpa [prefixWord, tailWord_2582634, baseEnd_2582634] using wordTrace_append hprefix tailTrace_2582634
  have hstable : (prefixWord ++ tailWord_2582634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582634).length < 2 ^ (prefixWord ++ tailWord_2582634).sum := by decide
  have hdescent : baseEnd_2582634 < baseStart_2582634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582706 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_2582706 : Nat := 118140960795 + 2582706 * 2 ^ 59
def prefixEnd_2582706 : Nat := 4983230072969 + 3 ^ 40 * 2582706 * 2
def baseEnd_2582706 : Nat := 1326169567251077384597357

theorem tailTrace_2582706 : CollatzResearch.WordTrace tailWord_2582706 prefixEnd_2582706 1326169567251077384597357 := by
  unfold tailWord_2582706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23549756645326181978213993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62799351054203151941903981 23549756645326181978213993)
  ·
    refine ⟨17662317483994636483660495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23549756645326181978213993 17662317483994636483660495)
    ·
      refine ⟨26493476225991954725490743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17662317483994636483660495 26493476225991954725490743)
      ·
        refine ⟨39740214338987932088236115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26493476225991954725490743 39740214338987932088236115)
        ·
          refine ⟨59610321508481898132354173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39740214338987932088236115 59610321508481898132354173)
          ·
            refine ⟨22353870565680711799632815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59610321508481898132354173 22353870565680711799632815)
            ·
              refine ⟨33530805848521067699449223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22353870565680711799632815 33530805848521067699449223)
              ·
                refine ⟨50296208772781601549173835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33530805848521067699449223 50296208772781601549173835)
                ·
                  refine ⟨75444313159172402323760753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50296208772781601549173835 75444313159172402323760753)
                  ·
                    refine ⟨56583234869379301742820565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75444313159172402323760753 56583234869379301742820565)
                    ·
                      refine ⟨1326169567251077384597357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56583234869379301742820565 1326169567251077384597357)
                      ·
                        rfl

theorem cell23_2582706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_2582706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582706 prefixEnd_2582706 := by exact prefixLift 2582706
  have htrace : WordTrace (prefixWord ++ tailWord_2582706) baseStart_2582706 baseEnd_2582706 := by
    simpa [prefixWord, tailWord_2582706, baseEnd_2582706] using wordTrace_append hprefix tailTrace_2582706
  have hstable : (prefixWord ++ tailWord_2582706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582706).length < 2 ^ (prefixWord ++ tailWord_2582706).sum := by decide
  have hdescent : baseEnd_2582706 < baseStart_2582706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582724 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_2582724 : Nat := 118140960795 + 2582724 * 2 ^ 59
def prefixEnd_2582724 : Nat := 4983230072969 + 3 ^ 40 * 2582724 * 2
def baseEnd_2582724 : Nat := 1326178809902858314172275

theorem tailTrace_2582724 : CollatzResearch.WordTrace tailWord_2582724 prefixEnd_2582724 1326178809902858314172275 := by
  unfold tailWord_2582724
  simp only [CollatzResearch.WordTrace]
  refine ⟨47099841547619758493505613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62799788730159677991340817 47099841547619758493505613)
  ·
    refine ⟨17662440580357409435064605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47099841547619758493505613 17662440580357409435064605)
    ·
      refine ⟨6623415217634028538149227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17662440580357409435064605 6623415217634028538149227)
      ·
        refine ⟨9935122826451042807223841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6623415217634028538149227 9935122826451042807223841)
        ·
          refine ⟨7451342119838282105417881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9935122826451042807223841 7451342119838282105417881)
          ·
            refine ⟨5588506589878711579063411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7451342119838282105417881 5588506589878711579063411)
            ·
              refine ⟨8382759884818067368595117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5588506589878711579063411 8382759884818067368595117)
              ·
                refine ⟨3143534956806775263223169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8382759884818067368595117 3143534956806775263223169)
                ·
                  refine ⟨2357651217605081447417377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3143534956806775263223169 2357651217605081447417377)
                  ·
                    refine ⟨1768238413203811085563033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2357651217605081447417377 1768238413203811085563033)
                    ·
                      refine ⟨1326178809902858314172275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768238413203811085563033 1326178809902858314172275)
                      ·
                        rfl

theorem cell23_2582724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_2582724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582724 prefixEnd_2582724 := by exact prefixLift 2582724
  have htrace : WordTrace (prefixWord ++ tailWord_2582724) baseStart_2582724 baseEnd_2582724 := by
    simpa [prefixWord, tailWord_2582724, baseEnd_2582724] using wordTrace_append hprefix tailTrace_2582724
  have hstable : (prefixWord ++ tailWord_2582724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582724).length < 2 ^ (prefixWord ++ tailWord_2582724).sum := by decide
  have hdescent : baseEnd_2582724 < baseStart_2582724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582763 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 4]
def baseStart_2582763 : Nat := 118140960795 + 2582763 * 2 ^ 59
def prefixEnd_2582763 : Nat := 4983230072969 + 3 ^ 40 * 2582763 * 2
def baseEnd_2582763 : Nat := 1326198835648383661584595

theorem tailTrace_2582763 : CollatzResearch.WordTrace tailWord_2582763 prefixEnd_2582763 1326198835648383661584595 := by
  unfold tailWord_2582763
  simp only [CollatzResearch.WordTrace]
  refine ⟨94201105542098226647680943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62800737028065484431787295 94201105542098226647680943)
  ·
    refine ⟨141301658313147339971521415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94201105542098226647680943 141301658313147339971521415)
    ·
      refine ⟨211952487469721009957282123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141301658313147339971521415 211952487469721009957282123)
      ·
        refine ⟨317928731204581514935923185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211952487469721009957282123 317928731204581514935923185)
        ·
          refine ⟨238446548403436136201942389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317928731204581514935923185 238446548403436136201942389)
          ·
            refine ⟨22354363912822137768932099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 238446548403436136201942389 22354363912822137768932099)
            ·
              refine ⟨33531545869233206653398149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22354363912822137768932099 33531545869233206653398149)
              ·
                refine ⟨6287164850481226247512153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33531545869233206653398149 6287164850481226247512153)
                ·
                  refine ⟨4715373637860919685634115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6287164850481226247512153 4715373637860919685634115)
                  ·
                    refine ⟨7073060456791379528451173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4715373637860919685634115 7073060456791379528451173)
                    ·
                      refine ⟨1326198835648383661584595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7073060456791379528451173 1326198835648383661584595)
                      ·
                        rfl

theorem cell23_2582763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 4].length) (baseStart_2582763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582763 prefixEnd_2582763 := by exact prefixLift 2582763
  have htrace : WordTrace (prefixWord ++ tailWord_2582763) baseStart_2582763 baseEnd_2582763 := by
    simpa [prefixWord, tailWord_2582763, baseEnd_2582763] using wordTrace_append hprefix tailTrace_2582763
  have hstable : (prefixWord ++ tailWord_2582763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582763).length < 2 ^ (prefixWord ++ tailWord_2582763).sum := by decide
  have hdescent : baseEnd_2582763 < baseStart_2582763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582780 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 1, 6, 2]
def baseStart_2582780 : Nat := 118140960795 + 2582780 * 2 ^ 59
def prefixEnd_2582780 : Nat := 4983230072969 + 3 ^ 40 * 2582780 * 2
def baseEnd_2582780 : Nat := 1326207564819510095072017

theorem tailTrace_2582780 : CollatzResearch.WordTrace tailWord_2582780 prefixEnd_2582780 1326207564819510095072017 := by
  unfold tailWord_2582780
  simp only [CollatzResearch.WordTrace]
  refine ⟨47100862791518319275524897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62801150388691092367366529 47100862791518319275524897)
  ·
    refine ⟨35325647093638739456643673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47100862791518319275524897 35325647093638739456643673)
    ·
      refine ⟨26494235320229054592482755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35325647093638739456643673 26494235320229054592482755)
      ·
        refine ⟨39741352980343581888724133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26494235320229054592482755 39741352980343581888724133)
        ·
          refine ⟨7451503683814421604135775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39741352980343581888724133 7451503683814421604135775)
          ·
            refine ⟨11177255525721632406203663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7451503683814421604135775 11177255525721632406203663)
            ·
              refine ⟨16765883288582448609305495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11177255525721632406203663 16765883288582448609305495)
              ·
                refine ⟨25148824932873672913958243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16765883288582448609305495 25148824932873672913958243)
                ·
                  refine ⟨37723237399310509370937365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25148824932873672913958243 37723237399310509370937365)
                  ·
                    refine ⟨1768276753092680126762689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37723237399310509370937365 1768276753092680126762689)
                    ·
                      refine ⟨1326207564819510095072017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768276753092680126762689 1326207564819510095072017)
                      ·
                        rfl

theorem cell23_2582780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_2582780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582780 prefixEnd_2582780 := by exact prefixLift 2582780
  have htrace : WordTrace (prefixWord ++ tailWord_2582780) baseStart_2582780 baseEnd_2582780 := by
    simpa [prefixWord, tailWord_2582780, baseEnd_2582780] using wordTrace_append hprefix tailTrace_2582780
  have hstable : (prefixWord ++ tailWord_2582780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582780).length < 2 ^ (prefixWord ++ tailWord_2582780).sum := by decide
  have hdescent : baseEnd_2582780 < baseStart_2582780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582783 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 3]
def baseStart_2582783 : Nat := 118140960795 + 2582783 * 2 ^ 59
def prefixEnd_2582783 : Nat := 4983230072969 + 3 ^ 40 * 2582783 * 2
def baseEnd_2582783 : Nat := 1326209105261473583334503

theorem tailTrace_2582783 : CollatzResearch.WordTrace tailWord_2582783 prefixEnd_2582783 1326209105261473583334503 := by
  unfold tailWord_2582783
  simp only [CollatzResearch.WordTrace]
  refine ⟨94201835002025770063409003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62801223334683846708939335 94201835002025770063409003)
  ·
    refine ⟨141302752503038655095113505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94201835002025770063409003 141302752503038655095113505)
    ·
      refine ⟨105977064377278991321335129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141302752503038655095113505 105977064377278991321335129)
      ·
        refine ⟨79482798282959243491001347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105977064377278991321335129 79482798282959243491001347)
        ·
          refine ⟨119224197424438865236502021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79482798282959243491001347 119224197424438865236502021)
          ·
            refine ⟨22354537017082287231844129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119224197424438865236502021 22354537017082287231844129)
            ·
              refine ⟨16765902762811715423883097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22354537017082287231844129 16765902762811715423883097)
              ·
                refine ⟨12574427072108786567912323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16765902762811715423883097 12574427072108786567912323)
                ·
                  refine ⟨18861640608163179851868485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12574427072108786567912323 18861640608163179851868485)
                  ·
                    refine ⟨3536557614030596222225341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18861640608163179851868485 3536557614030596222225341)
                    ·
                      refine ⟨1326209105261473583334503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3536557614030596222225341 1326209105261473583334503)
                      ·
                        rfl

theorem cell23_2582783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_2582783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582783 prefixEnd_2582783 := by exact prefixLift 2582783
  have htrace : WordTrace (prefixWord ++ tailWord_2582783) baseStart_2582783 baseEnd_2582783 := by
    simpa [prefixWord, tailWord_2582783, baseEnd_2582783] using wordTrace_append hprefix tailTrace_2582783
  have hstable : (prefixWord ++ tailWord_2582783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582783).length < 2 ^ (prefixWord ++ tailWord_2582783).sum := by decide
  have hdescent : baseEnd_2582783 < baseStart_2582783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582807 : List Nat := [1, 1, 3, 4, 1, 2, 1, 5, 1, 4]
def baseStart_2582807 : Nat := 118140960795 + 2582807 * 2 ^ 59
def prefixEnd_2582807 : Nat := 4983230072969 + 3 ^ 40 * 2582807 * 2
def baseEnd_2582807 : Nat := 442073809599060496478131

theorem tailTrace_2582807 : CollatzResearch.WordTrace tailWord_2582807 prefixEnd_2582807 442073809599060496478131 := by
  unfold tailWord_2582807
  simp only [CollatzResearch.WordTrace]
  refine ⟨94202710353938822162282675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62801806902625881441521783 94202710353938822162282675)
  ·
    refine ⟨141304065530908233243424013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94202710353938822162282675 141304065530908233243424013)
    ·
      refine ⟨52989024574090587466284005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141304065530908233243424013 52989024574090587466284005)
      ·
        refine ⟨9935442107641985149928251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52989024574090587466284005 9935442107641985149928251)
        ·
          refine ⟨14903163161462977724892377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9935442107641985149928251 14903163161462977724892377)
          ·
            refine ⟨11177372371097233293669283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14903163161462977724892377 11177372371097233293669283)
            ·
              refine ⟨16766058556645849940503925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11177372371097233293669283 16766058556645849940503925)
              ·
                refine ⟨1571817989685548431922243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16766058556645849940503925 1571817989685548431922243)
                ·
                  refine ⟨2357726984528322647883365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571817989685548431922243 2357726984528322647883365)
                  ·
                    refine ⟨442073809599060496478131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2357726984528322647883365 442073809599060496478131)
                    ·
                      rfl

theorem cell23_2582807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_2582807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582807 prefixEnd_2582807 := by exact prefixLift 2582807
  have htrace : WordTrace (prefixWord ++ tailWord_2582807) baseStart_2582807 baseEnd_2582807 := by
    simpa [prefixWord, tailWord_2582807, baseEnd_2582807] using wordTrace_append hprefix tailTrace_2582807
  have hstable : (prefixWord ++ tailWord_2582807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582807).length < 2 ^ (prefixWord ++ tailWord_2582807).sum := by decide
  have hdescent : baseEnd_2582807 < baseStart_2582807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582814 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_2582814 : Nat := 118140960795 + 2582814 * 2 ^ 59
def prefixEnd_2582814 : Nat := 4983230072969 + 3 ^ 40 * 2582814 * 2
def baseEnd_2582814 : Nat := 1326225023161762962046861

theorem tailTrace_2582814 : CollatzResearch.WordTrace tailWord_2582814 prefixEnd_2582814 1326225023161762962046861 := by
  unfold tailWord_2582814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11775370708114182794723437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62801977109942308238524997 11775370708114182794723437)
  ·
    refine ⟨4415764015542818548021289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11775370708114182794723437 4415764015542818548021289)
    ·
      refine ⟨3311823011657113911015967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4415764015542818548021289 3311823011657113911015967)
      ·
        refine ⟨4967734517485670866523951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3311823011657113911015967 4967734517485670866523951)
        ·
          refine ⟨7451601776228506299785927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4967734517485670866523951 7451601776228506299785927)
          ·
            refine ⟨11177402664342759449678891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7451601776228506299785927 11177402664342759449678891)
            ·
              refine ⟨16766103996514139174518337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11177402664342759449678891 16766103996514139174518337)
              ·
                refine ⟨12574577997385604380888753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16766103996514139174518337 12574577997385604380888753)
                ·
                  refine ⟨9430933498039203285666565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12574577997385604380888753 9430933498039203285666565)
                  ·
                    refine ⟨1768300030882350616062481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9430933498039203285666565 1768300030882350616062481)
                    ·
                      refine ⟨1326225023161762962046861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768300030882350616062481 1326225023161762962046861)
                      ·
                        rfl

theorem cell23_2582814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_2582814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582814 prefixEnd_2582814 := by exact prefixLift 2582814
  have htrace : WordTrace (prefixWord ++ tailWord_2582814) baseStart_2582814 baseEnd_2582814 := by
    simpa [prefixWord, tailWord_2582814, baseEnd_2582814] using wordTrace_append hprefix tailTrace_2582814
  have hstable : (prefixWord ++ tailWord_2582814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582814).length < 2 ^ (prefixWord ++ tailWord_2582814).sum := by decide
  have hdescent : baseEnd_2582814 < baseStart_2582814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582820 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 6]
def baseStart_2582820 : Nat := 118140960795 + 2582820 * 2 ^ 59
def prefixEnd_2582820 : Nat := 4983230072969 + 3 ^ 40 * 2582820 * 2
def baseEnd_2582820 : Nat := 147358678227298882063537

theorem tailTrace_2582820 : CollatzResearch.WordTrace tailWord_2582820 prefixEnd_2582820 147358678227298882063537 := by
  unfold tailWord_2582820
  simp only [CollatzResearch.WordTrace]
  refine ⟨47101592251445862691252957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62802123001927816921670609 47101592251445862691252957)
  ·
    refine ⟨17663097094292198509219859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47101592251445862691252957 17663097094292198509219859)
    ·
      refine ⟨26494645641438297763829789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17663097094292198509219859 26494645641438297763829789)
      ·
        refine ⟨9935492115539361661436171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26494645641438297763829789 9935492115539361661436171)
        ·
          refine ⟨14903238173309042492154257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9935492115539361661436171 14903238173309042492154257)
          ·
            refine ⟨11177428629981781869115693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14903238173309042492154257 11177428629981781869115693)
            ·
              refine ⟨4191535736243168200918385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11177428629981781869115693 4191535736243168200918385)
              ·
                refine ⟨3143651802182376150688789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4191535736243168200918385 3143651802182376150688789)
                ·
                  refine ⟨147358678227298882063537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3143651802182376150688789 147358678227298882063537)
                  ·
                    rfl

theorem cell23_2582820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_2582820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582820 prefixEnd_2582820 := by exact prefixLift 2582820
  have htrace : WordTrace (prefixWord ++ tailWord_2582820) baseStart_2582820 baseEnd_2582820 := by
    simpa [prefixWord, tailWord_2582820, baseEnd_2582820] using wordTrace_append hprefix tailTrace_2582820
  have hstable : (prefixWord ++ tailWord_2582820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582820).length < 2 ^ (prefixWord ++ tailWord_2582820).sum := by decide
  have hdescent : baseEnd_2582820 < baseStart_2582820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582840 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 1, 5, 2]
def baseStart_2582840 : Nat := 118140960795 + 2582840 * 2 ^ 59
def prefixEnd_2582840 : Nat := 4983230072969 + 3 ^ 40 * 2582840 * 2
def baseEnd_2582840 : Nat := 1326238373658779860321741

theorem tailTrace_2582840 : CollatzResearch.WordTrace tailWord_2582840 prefixEnd_2582840 1326238373658779860321741 := by
  unfold tailWord_2582840
  simp only [CollatzResearch.WordTrace]
  refine ⟨47101956981409634399116987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62802609308546179198822649 47101956981409634399116987)
  ·
    refine ⟨70652935472114451598675481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47101956981409634399116987 70652935472114451598675481)
    ·
      refine ⟨52989701604085838699006611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70652935472114451598675481 52989701604085838699006611)
      ·
        refine ⟨79484552406128758048509917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52989701604085838699006611 79484552406128758048509917)
        ·
          refine ⟨29806707152298284268191219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79484552406128758048509917 29806707152298284268191219)
          ·
            refine ⟨44710060728447426402286829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29806707152298284268191219 44710060728447426402286829)
            ·
              refine ⟨16766272773167784900857561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44710060728447426402286829 16766272773167784900857561)
              ·
                refine ⟨12574704579875838675643171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16766272773167784900857561 12574704579875838675643171)
                ·
                  refine ⟨18862056869813758013464757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12574704579875838675643171 18862056869813758013464757)
                  ·
                    refine ⟨1768317831545039813762321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18862056869813758013464757 1768317831545039813762321)
                    ·
                      refine ⟨1326238373658779860321741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768317831545039813762321 1326238373658779860321741)
                      ·
                        rfl

theorem cell23_2582840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_2582840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582840 prefixEnd_2582840 := by exact prefixLift 2582840
  have htrace : WordTrace (prefixWord ++ tailWord_2582840) baseStart_2582840 baseEnd_2582840 := by
    simpa [prefixWord, tailWord_2582840, baseEnd_2582840] using wordTrace_append hprefix tailTrace_2582840
  have hstable : (prefixWord ++ tailWord_2582840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582840).length < 2 ^ (prefixWord ++ tailWord_2582840).sum := by decide
  have hdescent : baseEnd_2582840 < baseStart_2582840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582864 : List Nat := [2, 1, 1, 1, 1, 6, 3, 3, 1, 1, 3]
def baseStart_2582864 : Nat := 118140960795 + 2582864 * 2 ^ 59
def prefixEnd_2582864 : Nat := 4983230072969 + 3 ^ 40 * 2582864 * 2
def baseEnd_2582864 : Nat := 1326250697194487766421631

theorem tailTrace_2582864 : CollatzResearch.WordTrace tailWord_2582864 prefixEnd_2582864 1326250697194487766421631 := by
  unfold tailWord_2582864
  simp only [CollatzResearch.WordTrace]
  refine ⟨47102394657366160448553823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62803192876488213931405097 47102394657366160448553823)
  ·
    refine ⟨70653591986049240672830735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47102394657366160448553823 70653591986049240672830735)
    ·
      refine ⟨105980387979073861009246103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70653591986049240672830735 105980387979073861009246103)
      ·
        refine ⟨158970581968610791513869155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105980387979073861009246103 158970581968610791513869155)
        ·
          refine ⟨238455872952916187270803733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158970581968610791513869155 238455872952916187270803733)
          ·
            refine ⟨11177619044667946278318925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 238455872952916187270803733 11177619044667946278318925)
            ·
              refine ⟨4191607141750479854369597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11177619044667946278318925 4191607141750479854369597)
              ·
                refine ⟨1571852678156429945388599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4191607141750479854369597 1571852678156429945388599)
                ·
                  refine ⟨2357779017234644918082899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571852678156429945388599 2357779017234644918082899)
                  ·
                    refine ⟨3536668525851967377124349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2357779017234644918082899 3536668525851967377124349)
                    ·
                      refine ⟨1326250697194487766421631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3536668525851967377124349 1326250697194487766421631)
                      ·
                        rfl

theorem cell23_2582864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 1, 1, 3].length) (baseStart_2582864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582864 prefixEnd_2582864 := by exact prefixLift 2582864
  have htrace : WordTrace (prefixWord ++ tailWord_2582864) baseStart_2582864 baseEnd_2582864 := by
    simpa [prefixWord, tailWord_2582864, baseEnd_2582864] using wordTrace_append hprefix tailTrace_2582864
  have hstable : (prefixWord ++ tailWord_2582864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582864).length < 2 ^ (prefixWord ++ tailWord_2582864).sum := by decide
  have hdescent : baseEnd_2582864 < baseStart_2582864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582883 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2582883 : Nat := 118140960795 + 2582883 * 2 ^ 59
def prefixEnd_2582883 : Nat := 4983230072969 + 3 ^ 40 * 2582883 * 2
def baseEnd_2582883 : Nat := 1326260453326923192084043

theorem tailTrace_2582883 : CollatzResearch.WordTrace tailWord_2582883 prefixEnd_2582883 1326260453326923192084043 := by
  unfold tailWord_2582883
  simp only [CollatzResearch.WordTrace]
  refine ⟨94205482301663487142049303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62803654867775658094699535 94205482301663487142049303)
  ·
    refine ⟨141308223452495230713073955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94205482301663487142049303 141308223452495230713073955)
    ·
      refine ⟨211962335178742846069610933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141308223452495230713073955 211962335178742846069610933)
      ·
        refine ⟨19871468923007141819026025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211962335178742846069610933 19871468923007141819026025)
        ·
          refine ⟨14903601692255356364269519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19871468923007141819026025 14903601692255356364269519)
          ·
            refine ⟨22355402538383034546404279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14903601692255356364269519 22355402538383034546404279)
            ·
              refine ⟨33533103807574551819606419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22355402538383034546404279 33533103807574551819606419)
              ·
                refine ⟨50299655711361827729409629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33533103807574551819606419 50299655711361827729409629)
                ·
                  refine ⟨18862370891760685398528611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50299655711361827729409629 18862370891760685398528611)
                  ·
                    refine ⟨28293556337641028097792917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18862370891760685398528611 28293556337641028097792917)
                    ·
                      refine ⟨1326260453326923192084043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28293556337641028097792917 1326260453326923192084043)
                      ·
                        rfl

theorem cell23_2582883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2582883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582883 prefixEnd_2582883 := by exact prefixLift 2582883
  have htrace : WordTrace (prefixWord ++ tailWord_2582883) baseStart_2582883 baseEnd_2582883 := by
    simpa [prefixWord, tailWord_2582883, baseEnd_2582883] using wordTrace_append hprefix tailTrace_2582883
  have hstable : (prefixWord ++ tailWord_2582883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582883).length < 2 ^ (prefixWord ++ tailWord_2582883).sum := by decide
  have hdescent : baseEnd_2582883 < baseStart_2582883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582907 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 1, 2, 3]
def baseStart_2582907 : Nat := 118140960795 + 2582907 * 2 ^ 59
def prefixEnd_2582907 : Nat := 4983230072969 + 3 ^ 40 * 2582907 * 2
def baseEnd_2582907 : Nat := 1326272776862631098183933

theorem tailTrace_2582907 : CollatzResearch.WordTrace tailWord_2582907 prefixEnd_2582907 1326272776862631098183933 := by
  unfold tailWord_2582907
  simp only [CollatzResearch.WordTrace]
  refine ⟨94206357653576539240922975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62804238435717692827281983 94206357653576539240922975)
  ·
    refine ⟨141309536480364808861384463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94206357653576539240922975 141309536480364808861384463)
    ·
      refine ⟨211964304720547213292076695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141309536480364808861384463 211964304720547213292076695)
      ·
        refine ⟨317946457080820819938115043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211964304720547213292076695 317946457080820819938115043)
        ·
          refine ⟨476919685621231229907172565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317946457080820819938115043 476919685621231229907172565)
          ·
            refine ⟨11177805131747606950949357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 476919685621231229907172565 11177805131747606950949357)
            ·
              refine ⟨4191676924405352606606009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11177805131747606950949357 4191676924405352606606009)
              ·
                refine ⟨3143757693304014454954507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4191676924405352606606009 3143757693304014454954507)
                ·
                  refine ⟨4715636539956021682431761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143757693304014454954507 4715636539956021682431761)
                  ·
                    refine ⟨3536727404967016261823821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715636539956021682431761 3536727404967016261823821)
                    ·
                      refine ⟨1326272776862631098183933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3536727404967016261823821 1326272776862631098183933)
                      ·
                        rfl

theorem cell23_2582907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 2, 3].length) (baseStart_2582907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582907 prefixEnd_2582907 := by exact prefixLift 2582907
  have htrace : WordTrace (prefixWord ++ tailWord_2582907) baseStart_2582907 baseEnd_2582907 := by
    simpa [prefixWord, tailWord_2582907, baseEnd_2582907] using wordTrace_append hprefix tailTrace_2582907
  have hstable : (prefixWord ++ tailWord_2582907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582907).length < 2 ^ (prefixWord ++ tailWord_2582907).sum := by decide
  have hdescent : baseEnd_2582907 < baseStart_2582907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582914 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2582914 : Nat := 118140960795 + 2582914 * 2 ^ 59
def prefixEnd_2582914 : Nat := 4983230072969 + 3 ^ 40 * 2582914 * 2
def baseEnd_2582914 : Nat := 442092123742404190265467

theorem tailTrace_2582914 : CollatzResearch.WordTrace tailWord_2582914 prefixEnd_2582914 442092123742404190265467 := by
  unfold tailWord_2582914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23551653241137794859106949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62804408643034119624285197 23551653241137794859106949)
  ·
    refine ⟨4415934982713336536082553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23551653241137794859106949 4415934982713336536082553)
    ·
      refine ⟨3311951237035002402061915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4415934982713336536082553 3311951237035002402061915)
      ·
        refine ⟨4967926855552503603092873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3311951237035002402061915 4967926855552503603092873)
        ·
          refine ⟨3725945141664377702319655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4967926855552503603092873 3725945141664377702319655)
          ·
            refine ⟨5588917712496566553479483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725945141664377702319655 5588917712496566553479483)
            ·
              refine ⟨8383376568744849830219225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5588917712496566553479483 8383376568744849830219225)
              ·
                refine ⟨6287532426558637372664419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8383376568744849830219225 6287532426558637372664419)
                ·
                  refine ⟨9431298639837956058996629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6287532426558637372664419 9431298639837956058996629)
                  ·
                    refine ⟨442092123742404190265467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9431298639837956058996629 442092123742404190265467)
                    ·
                      rfl

theorem cell23_2582914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2582914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582914 prefixEnd_2582914 := by exact prefixLift 2582914
  have htrace : WordTrace (prefixWord ++ tailWord_2582914) baseStart_2582914 baseEnd_2582914 := by
    simpa [prefixWord, tailWord_2582914, baseEnd_2582914] using wordTrace_append hprefix tailTrace_2582914
  have hstable : (prefixWord ++ tailWord_2582914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582914).length < 2 ^ (prefixWord ++ tailWord_2582914).sum := by decide
  have hdescent : baseEnd_2582914 < baseStart_2582914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582924 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 1, 2, 3]
def baseStart_2582924 : Nat := 118140960795 + 2582924 * 2 ^ 59
def prefixEnd_2582924 : Nat := 4983230072969 + 3 ^ 40 * 2582924 * 2
def baseEnd_2582924 : Nat := 1326281506033757531671355

theorem tailTrace_2582924 : CollatzResearch.WordTrace tailWord_2582924 prefixEnd_2582924 1326281506033757531671355 := by
  unfold tailWord_2582924
  simp only [CollatzResearch.WordTrace]
  refine ⟨47103488847257475572145913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62804651796343300762861217 47103488847257475572145913)
  ·
    refine ⟨35327616635443106679109435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47103488847257475572145913 35327616635443106679109435)
    ·
      refine ⟨52991424953164660018664153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35327616635443106679109435 52991424953164660018664153)
      ·
        refine ⟨39743568714873495013998115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52991424953164660018664153 39743568714873495013998115)
        ·
          refine ⟨59615353072310242520997173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39743568714873495013998115 59615353072310242520997173)
          ·
            refine ⟨5588939350529085236343485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59615353072310242520997173 5588939350529085236343485)
            ·
              refine ⟨2095852256448406963628807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5588939350529085236343485 2095852256448406963628807)
              ·
                refine ⟨3143778384672610445443211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095852256448406963628807 3143778384672610445443211)
                ·
                  refine ⟨4715667577008915668164817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143778384672610445443211 4715667577008915668164817)
                  ·
                    refine ⟨3536750682756686751123613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715667577008915668164817 3536750682756686751123613)
                    ·
                      refine ⟨1326281506033757531671355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3536750682756686751123613 1326281506033757531671355)
                      ·
                        rfl

theorem cell23_2582924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_2582924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582924 prefixEnd_2582924 := by exact prefixLift 2582924
  have htrace : WordTrace (prefixWord ++ tailWord_2582924) baseStart_2582924 baseEnd_2582924 := by
    simpa [prefixWord, tailWord_2582924, baseEnd_2582924] using wordTrace_append hprefix tailTrace_2582924
  have hstable : (prefixWord ++ tailWord_2582924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582924).length < 2 ^ (prefixWord ++ tailWord_2582924).sum := by decide
  have hdescent : baseEnd_2582924 < baseStart_2582924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582938 : List Nat := [3, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2]
def baseStart_2582938 : Nat := 118140960795 + 2582938 * 2 ^ 59
def prefixEnd_2582938 : Nat := 4983230072969 + 3 ^ 40 * 2582938 * 2
def baseEnd_2582938 : Nat := 1326288694762920476896291

theorem tailTrace_2582938 : CollatzResearch.WordTrace tailWord_2582938 prefixEnd_2582938 1326288694762920476896291 := by
  unfold tailWord_2582938
  simp only [CollatzResearch.WordTrace]
  refine ⟨23551872079116057883825367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62804992210976154356867645 23551872079116057883825367)
  ·
    refine ⟨35327808118674086825738051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23551872079116057883825367 35327808118674086825738051)
    ·
      refine ⟨52991712178011130238607077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35327808118674086825738051 52991712178011130238607077)
      ·
        refine ⟨9935946033377086919738827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52991712178011130238607077 9935946033377086919738827)
        ·
          refine ⟨14903919050065630379608241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9935946033377086919738827 14903919050065630379608241)
          ·
            refine ⟨11177939287549222784706181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14903919050065630379608241 11177939287549222784706181)
            ·
              refine ⟨2095863616415479272132409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11177939287549222784706181 2095863616415479272132409)
              ·
                refine ⟨1571897712311609454099307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2095863616415479272132409 1571897712311609454099307)
                ·
                  refine ⟨2357846568467414181148961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571897712311609454099307 2357846568467414181148961)
                  ·
                    refine ⟨1768384926350560635861721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2357846568467414181148961 1768384926350560635861721)
                    ·
                      refine ⟨1326288694762920476896291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768384926350560635861721 1326288694762920476896291)
                      ·
                        rfl

theorem cell23_2582938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_2582938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582938 prefixEnd_2582938 := by exact prefixLift 2582938
  have htrace : WordTrace (prefixWord ++ tailWord_2582938) baseStart_2582938 baseEnd_2582938 := by
    simpa [prefixWord, tailWord_2582938, baseEnd_2582938] using wordTrace_append hprefix tailTrace_2582938
  have hstable : (prefixWord ++ tailWord_2582938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582938).length < 2 ^ (prefixWord ++ tailWord_2582938).sum := by decide
  have hdescent : baseEnd_2582938 < baseStart_2582938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582947 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 3, 3, 2]
def baseStart_2582947 : Nat := 118140960795 + 2582947 * 2 ^ 59
def prefixEnd_2582947 : Nat := 4983230072969 + 3 ^ 40 * 2582947 * 2
def baseEnd_2582947 : Nat := 1326293316088810941683749

theorem tailTrace_2582947 : CollatzResearch.WordTrace tailWord_2582947 prefixEnd_2582947 1326293316088810941683749 := by
  unfold tailWord_2582947
  simp only [CollatzResearch.WordTrace]
  refine ⟨94207816573431626072379095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62805211048954417381586063 94207816573431626072379095)
  ·
    refine ⟨141311724860147439108568643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94207816573431626072379095 141311724860147439108568643)
    ·
      refine ⟨211967587290221158662852965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141311724860147439108568643 211967587290221158662852965)
      ·
        refine ⟨39743922616916467249284931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211967587290221158662852965 39743922616916467249284931)
        ·
          refine ⟨59615883925374700873927397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39743922616916467249284931 59615883925374700873927397)
          ·
            refine ⟨11177978236007756413861387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59615883925374700873927397 11177978236007756413861387)
            ·
              refine ⟨16766967354011634620792081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11177978236007756413861387 16766967354011634620792081)
              ·
                refine ⟨12575225515508725965594061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16766967354011634620792081 12575225515508725965594061)
                ·
                  refine ⟨4715709568315772237097773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12575225515508725965594061 4715709568315772237097773)
                  ·
                    refine ⟨1768391088118414588911665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4715709568315772237097773 1768391088118414588911665)
                    ·
                      refine ⟨1326293316088810941683749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768391088118414588911665 1326293316088810941683749)
                      ·
                        rfl

theorem cell23_2582947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_2582947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582947 prefixEnd_2582947 := by exact prefixLift 2582947
  have htrace : WordTrace (prefixWord ++ tailWord_2582947) baseStart_2582947 baseEnd_2582947 := by
    simpa [prefixWord, tailWord_2582947, baseEnd_2582947] using wordTrace_append hprefix tailTrace_2582947
  have hstable : (prefixWord ++ tailWord_2582947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582947).length < 2 ^ (prefixWord ++ tailWord_2582947).sum := by decide
  have hdescent : baseEnd_2582947 < baseStart_2582947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582988 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 2, 1, 3]
def baseStart_2582988 : Nat := 118140960795 + 2582988 * 2 ^ 59
def prefixEnd_2582988 : Nat := 4983230072969 + 3 ^ 40 * 2582988 * 2
def baseEnd_2582988 : Nat := 1326314368795645281271061

theorem tailTrace_2582988 : CollatzResearch.WordTrace tailWord_2582988 prefixEnd_2582988 1326314368795645281271061 := by
  unfold tailWord_2582988
  simp only [CollatzResearch.WordTrace]
  refine ⟨47104655983141545037310809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62806207977522060049747745 47104655983141545037310809)
  ·
    refine ⟨35328491987356158777983107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47104655983141545037310809 35328491987356158777983107)
    ·
      refine ⟨52992737981034238166974661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35328491987356158777983107 52992737981034238166974661)
      ·
        refine ⟨9936138371443919656307749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52992737981034238166974661 9936138371443919656307749)
        ·
          refine ⟨1863025944645734935557703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9936138371443919656307749 1863025944645734935557703)
          ·
            refine ⟨2794538916968602403336555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863025944645734935557703 2794538916968602403336555)
            ·
              refine ⟨4191808375452903605004833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2794538916968602403336555 4191808375452903605004833)
              ·
                refine ⟨3143856281589677703753625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4191808375452903605004833 3143856281589677703753625)
                ·
                  refine ⟨2357892211192258277815219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3143856281589677703753625 2357892211192258277815219)
                  ·
                    refine ⟨3536838316788387416722829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2357892211192258277815219 3536838316788387416722829)
                    ·
                      refine ⟨1326314368795645281271061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3536838316788387416722829 1326314368795645281271061)
                      ·
                        rfl

theorem cell23_2582988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_2582988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2582988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2582988 prefixEnd_2582988 := by exact prefixLift 2582988
  have htrace : WordTrace (prefixWord ++ tailWord_2582988) baseStart_2582988 baseEnd_2582988 := by
    simpa [prefixWord, tailWord_2582988, baseEnd_2582988] using wordTrace_append hprefix tailTrace_2582988
  have hstable : (prefixWord ++ tailWord_2582988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582988).length < 2 ^ (prefixWord ++ tailWord_2582988).sum := by decide
  have hdescent : baseEnd_2582988 < baseStart_2582988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583011 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 1, 4, 2]
def baseStart_2583011 : Nat := 118140960795 + 2583011 * 2 ^ 59
def prefixEnd_2583011 : Nat := 4983230072969 + 3 ^ 40 * 2583011 * 2
def baseEnd_2583011 : Nat := 1326326178850698691283455

theorem tailTrace_2583011 : CollatzResearch.WordTrace tailWord_2583011 prefixEnd_2583011 1326326178850698691283455 := by
  unfold tailWord_2583011
  simp only [CollatzResearch.WordTrace]
  refine ⟨94210150845199765002708887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62806767230133176668472591 94210150845199765002708887)
  ·
    refine ⟨141315226267799647504063331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94210150845199765002708887 141315226267799647504063331)
    ·
      refine ⟨211972839401699471256094997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141315226267799647504063331 211972839401699471256094997)
      ·
        refine ⟨9936226846954662715129453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 211972839401699471256094997 9936226846954662715129453)
        ·
          refine ⟨3726085067607998518173545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9936226846954662715129453 3726085067607998518173545)
          ·
            refine ⟨2794563800705998888630159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3726085067607998518173545 2794563800705998888630159)
            ·
              refine ⟨4191845701058998332945239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2794563800705998888630159 4191845701058998332945239)
              ·
                refine ⟨6287768551588497499417859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4191845701058998332945239 6287768551588497499417859)
                ·
                  refine ⟨9431652827382746249126789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6287768551588497499417859 9431652827382746249126789)
                  ·
                    refine ⟨1768434905134264921711273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9431652827382746249126789 1768434905134264921711273)
                    ·
                      refine ⟨1326326178850698691283455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768434905134264921711273 1326326178850698691283455)
                      ·
                        rfl

theorem cell23_2583011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_2583011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583011 prefixEnd_2583011 := by exact prefixLift 2583011
  have htrace : WordTrace (prefixWord ++ tailWord_2583011) baseStart_2583011 baseEnd_2583011 := by
    simpa [prefixWord, tailWord_2583011, baseEnd_2583011] using wordTrace_append hprefix tailTrace_2583011
  have hstable : (prefixWord ++ tailWord_2583011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583011).length < 2 ^ (prefixWord ++ tailWord_2583011).sum := by decide
  have hdescent : baseEnd_2583011 < baseStart_2583011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583077 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_2583077 : Nat := 118140960795 + 2583077 * 2 ^ 59
def prefixEnd_2583077 : Nat := 4983230072969 + 3 ^ 40 * 2583077 * 2
def baseEnd_2583077 : Nat := 442120022857965144352717

theorem tailTrace_2583077 : CollatzResearch.WordTrace tailWord_2583077 prefixEnd_2583077 442120022857965144352717 := by
  unfold tailWord_2583077
  simp only [CollatzResearch.WordTrace]
  refine ⟨94212558062960658274611485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62808372041973772183074323 94212558062960658274611485)
  ·
    refine ⟨35329709273610246852979307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94212558062960658274611485 35329709273610246852979307)
    ·
      refine ⟨52994563910415370279468961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35329709273610246852979307 52994563910415370279468961)
      ·
        refine ⟨39745922932811527709601721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52994563910415370279468961 39745922932811527709601721)
        ·
          refine ⟨29809442199608645782201291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39745922932811527709601721 29809442199608645782201291)
          ·
            refine ⟨44714163299412968673301937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29809442199608645782201291 44714163299412968673301937)
            ·
              refine ⟨33535622474559726504976453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44714163299412968673301937 33535622474559726504976453)
              ·
                refine ⟨6287929213979948719683085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33535622474559726504976453 6287929213979948719683085)
                ·
                  refine ⟨2357973455242480769881157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6287929213979948719683085 2357973455242480769881157)
                  ·
                    refine ⟨442120022857965144352717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2357973455242480769881157 442120022857965144352717)
                    ·
                      rfl

theorem cell23_2583077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_2583077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583077 prefixEnd_2583077 := by exact prefixLift 2583077
  have htrace : WordTrace (prefixWord ++ tailWord_2583077) baseStart_2583077 baseEnd_2583077 := by
    simpa [prefixWord, tailWord_2583077, baseEnd_2583077] using wordTrace_append hprefix tailTrace_2583077
  have hstable : (prefixWord ++ tailWord_2583077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583077).length < 2 ^ (prefixWord ++ tailWord_2583077).sum := by decide
  have hdescent : baseEnd_2583077 < baseStart_2583077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583090 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 10]
def baseStart_2583090 : Nat := 118140960795 + 2583090 * 2 ^ 59
def prefixEnd_2583090 : Nat := 4983230072969 + 3 ^ 40 * 2583090 * 2
def baseEnd_2583090 : Nat := 147374082646933764688399

theorem tailTrace_2583090 : CollatzResearch.WordTrace tailWord_2583090 prefixEnd_2583090 147374082646933764688399 := by
  unfold tailWord_2583090
  simp only [CollatzResearch.WordTrace]
  refine ⟨23553258052978390373708681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62808688141275707663223149 23553258052978390373708681)
  ·
    refine ⟨17664943539733792780281511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23553258052978390373708681 17664943539733792780281511)
    ·
      refine ⟨26497415309600689170422267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17664943539733792780281511 26497415309600689170422267)
      ·
        refine ⟨39746122964401033755633401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26497415309600689170422267 39746122964401033755633401)
        ·
          refine ⟨29809592223300775316725051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39746122964401033755633401 29809592223300775316725051)
          ·
            refine ⟨44714388334951162975087577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29809592223300775316725051 44714388334951162975087577)
            ·
              refine ⟨33535791251213372231315683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44714388334951162975087577 33535791251213372231315683)
              ·
                refine ⟨50303686876820058346973525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33535791251213372231315683 50303686876820058346973525)
                ·
                  refine ⟨147374082646933764688399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 50303686876820058346973525 147374082646933764688399)
                  ·
                    rfl

theorem cell23_2583090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_2583090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583090 prefixEnd_2583090 := by exact prefixLift 2583090
  have htrace : WordTrace (prefixWord ++ tailWord_2583090) baseStart_2583090 baseEnd_2583090 := by
    simpa [prefixWord, tailWord_2583090, baseEnd_2583090] using wordTrace_append hprefix tailTrace_2583090
  have hstable : (prefixWord ++ tailWord_2583090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583090).length < 2 ^ (prefixWord ++ tailWord_2583090).sum := by decide
  have hdescent : baseEnd_2583090 < baseStart_2583090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583111 : List Nat := [1, 1, 4, 1, 4, 2, 1, 4, 1, 4]
def baseStart_2583111 : Nat := 118140960795 + 2583111 * 2 ^ 59
def prefixEnd_2583111 : Nat := 4983230072969 + 3 ^ 40 * 2583111 * 2
def baseEnd_2583111 : Nat := 442125842305382766677665

theorem tailTrace_2583111 : CollatzResearch.WordTrace tailWord_2583111 prefixEnd_2583111 442125842305382766677665 := by
  unfold tailWord_2583111
  simp only [CollatzResearch.WordTrace]
  refine ⟨94213798144837482081349187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62809198763224988054232791 94213798144837482081349187)
  ·
    refine ⟨141320697217256223122023781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94213798144837482081349187 141320697217256223122023781)
    ·
      refine ⟨26497630728235541835379459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141320697217256223122023781 26497630728235541835379459)
      ·
        refine ⟨39746446092353312753069189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26497630728235541835379459 39746446092353312753069189)
        ·
          refine ⟨7452458642316246141200473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39746446092353312753069189 7452458642316246141200473)
          ·
            refine ⟨5589343981737184605900355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7452458642316246141200473 5589343981737184605900355)
            ·
              refine ⟨8384015972605776908850533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5589343981737184605900355 8384015972605776908850533)
              ·
                refine ⟨1572002994863583170409475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8384015972605776908850533 1572002994863583170409475)
                ·
                  refine ⟨2358004492295374755614213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572002994863583170409475 2358004492295374755614213)
                  ·
                    refine ⟨442125842305382766677665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2358004492295374755614213 442125842305382766677665)
                    ·
                      rfl

theorem cell23_2583111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_2583111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583111 prefixEnd_2583111 := by exact prefixLift 2583111
  have htrace : WordTrace (prefixWord ++ tailWord_2583111) baseStart_2583111 baseEnd_2583111 := by
    simpa [prefixWord, tailWord_2583111, baseEnd_2583111] using wordTrace_append hprefix tailTrace_2583111
  have hstable : (prefixWord ++ tailWord_2583111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583111).length < 2 ^ (prefixWord ++ tailWord_2583111).sum := by decide
  have hdescent : baseEnd_2583111 < baseStart_2583111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583137 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 3, 5]
def baseStart_2583137 : Nat := 118140960795 + 2583137 * 2 ^ 59
def prefixEnd_2583137 : Nat := 4983230072969 + 3 ^ 40 * 2583137 * 2
def baseEnd_2583137 : Nat := 442130292471055066102625

theorem tailTrace_2583137 : CollatzResearch.WordTrace tailWord_2583137 prefixEnd_2583137 442130292471055066102625 := by
  unfold tailWord_2583137
  simp only [CollatzResearch.WordTrace]
  refine ⟨94214746442743288521795665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62809830961828859014530443 94214746442743288521795665)
  ·
    refine ⟨70661059832057466391346749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94214746442743288521795665 70661059832057466391346749)
    ·
      refine ⟨26497897437021549896755031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70661059832057466391346749 26497897437021549896755031)
      ·
        refine ⟨39746846155532324845132547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26497897437021549896755031 39746846155532324845132547)
        ·
          refine ⟨59620269233298487267698821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39746846155532324845132547 59620269233298487267698821)
          ·
            refine ⟨11178800481243466362693529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59620269233298487267698821 11178800481243466362693529)
            ·
              refine ⟨8384100360932599772020147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11178800481243466362693529 8384100360932599772020147)
              ·
                refine ⟨12576150541398899658030221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8384100360932599772020147 12576150541398899658030221)
                ·
                  refine ⟨4716056453024587371761333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12576150541398899658030221 4716056453024587371761333)
                  ·
                    refine ⟨442130292471055066102625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4716056453024587371761333 442130292471055066102625)
                    ·
                      rfl

theorem cell23_2583137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_2583137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583137 prefixEnd_2583137 := by exact prefixLift 2583137
  have htrace : WordTrace (prefixWord ++ tailWord_2583137) baseStart_2583137 baseEnd_2583137 := by
    simpa [prefixWord, tailWord_2583137, baseEnd_2583137] using wordTrace_append hprefix tailTrace_2583137
  have hstable : (prefixWord ++ tailWord_2583137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583137).length < 2 ^ (prefixWord ++ tailWord_2583137).sum := by decide
  have hdescent : baseEnd_2583137 < baseStart_2583137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583151 : List Nat := [1, 1, 2, 1, 3, 2, 3, 5, 1, 1, 3]
def baseStart_2583151 : Nat := 118140960795 + 2583151 * 2 ^ 59
def prefixEnd_2583151 : Nat := 4983230072969 + 3 ^ 40 * 2583151 * 2
def baseEnd_2583151 : Nat := 1326398066142328143532811

theorem tailTrace_2583151 : CollatzResearch.WordTrace tailWord_2583151 prefixEnd_2583151 1326398066142328143532811 := by
  unfold tailWord_2583151
  simp only [CollatzResearch.WordTrace]
  refine ⟨94215257064692568912805307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62810171376461712608536871 94215257064692568912805307)
  ·
    refine ⟨141322885597038853369207961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94215257064692568912805307 141322885597038853369207961)
    ·
      refine ⟨105992164197779140026905971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141322885597038853369207961 105992164197779140026905971)
      ·
        refine ⟨158988246296668710040358957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105992164197779140026905971 158988246296668710040358957)
        ·
          refine ⟨59620592361250766265134609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158988246296668710040358957 59620592361250766265134609)
          ·
            refine ⟨44715444270938074698850957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59620592361250766265134609 44715444270938074698850957)
            ·
              refine ⟨16768291601601778012069109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44715444270938074698850957 16768291601601778012069109)
              ·
                refine ⟨1572027337650166688631479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16768291601601778012069109 1572027337650166688631479)
                ·
                  refine ⟨2358041006475250032947219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572027337650166688631479 2358041006475250032947219)
                  ·
                    refine ⟨3537061509712875049420829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2358041006475250032947219 3537061509712875049420829)
                    ·
                      refine ⟨1326398066142328143532811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3537061509712875049420829 1326398066142328143532811)
                      ·
                        rfl

theorem cell23_2583151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 1, 1, 3].length) (baseStart_2583151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583151 prefixEnd_2583151 := by exact prefixLift 2583151
  have htrace : WordTrace (prefixWord ++ tailWord_2583151) baseStart_2583151 baseEnd_2583151 := by
    simpa [prefixWord, tailWord_2583151, baseEnd_2583151] using wordTrace_append hprefix tailTrace_2583151
  have hstable : (prefixWord ++ tailWord_2583151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583151).length < 2 ^ (prefixWord ++ tailWord_2583151).sum := by decide
  have hdescent : baseEnd_2583151 < baseStart_2583151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583158 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_2583158 : Nat := 118140960795 + 2583158 * 2 ^ 59
def prefixEnd_2583158 : Nat := 4983230072969 + 3 ^ 40 * 2583158 * 2
def baseEnd_2583158 : Nat := 147377962278545512905031

theorem tailTrace_2583158 : CollatzResearch.WordTrace tailWord_2583158 prefixEnd_2583158 147377962278545512905031 := by
  unfold tailWord_2583158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5888469523479200569269383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62810341583778139405540085 5888469523479200569269383)
  ·
    refine ⟨8832704285218800853904075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5888469523479200569269383 8832704285218800853904075)
    ·
      refine ⟨13249056427828201280856113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8832704285218800853904075 13249056427828201280856113)
      ·
        refine ⟨9936792320871150960642085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13249056427828201280856113 9936792320871150960642085)
        ·
          refine ⟨1863148560163340805120391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9936792320871150960642085 1863148560163340805120391)
          ·
            refine ⟨2794722840245011207680587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863148560163340805120391 2794722840245011207680587)
            ·
              refine ⟨4192084260367516811520881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2794722840245011207680587 4192084260367516811520881)
              ·
                refine ⟨3144063195275637608640661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4192084260367516811520881 3144063195275637608640661)
                ·
                  refine ⟨147377962278545512905031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3144063195275637608640661 147377962278545512905031)
                  ·
                    rfl

theorem cell23_2583158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_2583158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583158 prefixEnd_2583158 := by exact prefixLift 2583158
  have htrace : WordTrace (prefixWord ++ tailWord_2583158) baseStart_2583158 baseEnd_2583158 := by
    simpa [prefixWord, tailWord_2583158, baseEnd_2583158] using wordTrace_append hprefix tailTrace_2583158
  have hstable : (prefixWord ++ tailWord_2583158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583158).length < 2 ^ (prefixWord ++ tailWord_2583158).sum := by decide
  have hdescent : baseEnd_2583158 < baseStart_2583158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583191 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 3, 2, 2]
def baseStart_2583191 : Nat := 118140960795 + 2583191 * 2 ^ 59
def prefixEnd_2583191 : Nat := 4983230072969 + 3 ^ 40 * 2583191 * 2
def baseEnd_2583191 : Nat := 1326418605368507987032627

theorem tailTrace_2583191 : CollatzResearch.WordTrace tailWord_2583191 prefixEnd_2583191 1326418605368507987032627 := by
  unfold tailWord_2583191
  simp only [CollatzResearch.WordTrace]
  refine ⟨94216715984547655744261427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62811143989698437162840951 94216715984547655744261427)
  ·
    refine ⟨141325073976821483616392141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94216715984547655744261427 141325073976821483616392141)
    ·
      refine ⟨52996902741308056356147053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141325073976821483616392141 52996902741308056356147053)
      ·
        refine ⟨19873838527990521133555145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52996902741308056356147053 19873838527990521133555145)
        ·
          refine ⟨14905378895992890850166359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19873838527990521133555145 14905378895992890850166359)
          ·
            refine ⟨22358068343989336275249539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14905378895992890850166359 22358068343989336275249539)
            ·
              refine ⟨33537102515984004412874309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22358068343989336275249539 33537102515984004412874309)
              ·
                refine ⟨6288206721747000827413933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33537102515984004412874309 6288206721747000827413933)
                ·
                  refine ⟨2358077520655125310280225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6288206721747000827413933 2358077520655125310280225)
                  ·
                    refine ⟨1768558140491343982710169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2358077520655125310280225 1768558140491343982710169)
                    ·
                      refine ⟨1326418605368507987032627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768558140491343982710169 1326418605368507987032627)
                      ·
                        rfl

theorem cell23_2583191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_2583191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583191 prefixEnd_2583191 := by exact prefixLift 2583191
  have htrace : WordTrace (prefixWord ++ tailWord_2583191) baseStart_2583191 baseEnd_2583191 := by
    simpa [prefixWord, tailWord_2583191, baseEnd_2583191] using wordTrace_append hprefix tailTrace_2583191
  have hstable : (prefixWord ++ tailWord_2583191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583191).length < 2 ^ (prefixWord ++ tailWord_2583191).sum := by decide
  have hdescent : baseEnd_2583191 < baseStart_2583191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583214 : List Nat := [4, 1, 4, 1, 1, 1, 11]
def baseStart_2583214 : Nat := 118140960795 + 2583214 * 2 ^ 59
def prefixEnd_2583214 : Nat := 4983230072969 + 3 ^ 40 * 2583214 * 2
def baseEnd_2583214 : Nat := 16375684141031622185741

theorem tailTrace_2583214 : CollatzResearch.WordTrace tailWord_2583214 prefixEnd_2583214 16375684141031622185741 := by
  unfold tailWord_2583214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11777194357933041334043587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62811703242309553781565797 11777194357933041334043587)
  ·
    refine ⟨17665791536899562001065381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11777194357933041334043587 17665791536899562001065381)
    ·
      refine ⟨3312335913168667875199759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17665791536899562001065381 3312335913168667875199759)
      ·
        refine ⟨4968503869753001812799639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3312335913168667875199759 4968503869753001812799639)
        ·
          refine ⟨7452755804629502719199459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4968503869753001812799639 7452755804629502719199459)
          ·
            refine ⟨11179133706944254078799189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7452755804629502719199459 11179133706944254078799189)
            ·
              refine ⟨16375684141031622185741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11179133706944254078799189 16375684141031622185741)
              ·
                rfl

theorem cell23_2583214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 11].length) (baseStart_2583214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583214 prefixEnd_2583214 := by exact prefixLift 2583214
  have htrace : WordTrace (prefixWord ++ tailWord_2583214) baseStart_2583214 baseEnd_2583214 := by
    simpa [prefixWord, tailWord_2583214, baseEnd_2583214] using wordTrace_append hprefix tailTrace_2583214
  have hstable : (prefixWord ++ tailWord_2583214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583214).length < 2 ^ (prefixWord ++ tailWord_2583214).sum := by decide
  have hdescent : baseEnd_2583214 < baseStart_2583214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583287 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 7]
def baseStart_2583287 : Nat := 118140960795 + 2583287 * 2 ^ 59
def prefixEnd_2583287 : Nat := 4983230072969 + 3 ^ 40 * 2583287 * 2
def baseEnd_2583287 : Nat := 147385322167926623492465

theorem tailTrace_2583287 : CollatzResearch.WordTrace tailWord_2583287 prefixEnd_2583287 147385322167926623492465 := by
  unfold tailWord_2583287
  simp only [CollatzResearch.WordTrace]
  refine ⟨94220217392199864139756115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62813478261466576093170743 94220217392199864139756115)
  ·
    refine ⟨141330326088299796209634173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94220217392199864139756115 141330326088299796209634173)
    ·
      refine ⟨52998872283112423578612815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141330326088299796209634173 52998872283112423578612815)
      ·
        refine ⟨79498308424668635367919223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52998872283112423578612815 79498308424668635367919223)
        ·
          refine ⟨119247462637002953051878835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79498308424668635367919223 119247462637002953051878835)
          ·
            refine ⟨178871193955504429577818253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119247462637002953051878835 178871193955504429577818253)
            ·
              refine ⟨67076697733314161091681845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178871193955504429577818253 67076697733314161091681845)
              ·
                refine ⟨6288440412498202602345173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67076697733314161091681845 6288440412498202602345173)
                ·
                  refine ⟨147385322167926623492465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6288440412498202602345173 147385322167926623492465)
                  ·
                    rfl

theorem cell23_2583287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 7].length) (baseStart_2583287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583287 prefixEnd_2583287 := by exact prefixLift 2583287
  have htrace : WordTrace (prefixWord ++ tailWord_2583287) baseStart_2583287 baseEnd_2583287 := by
    simpa [prefixWord, tailWord_2583287, baseEnd_2583287] using wordTrace_append hprefix tailTrace_2583287
  have hstable : (prefixWord ++ tailWord_2583287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583287).length < 2 ^ (prefixWord ++ tailWord_2583287).sum := by decide
  have hdescent : baseEnd_2583287 < baseStart_2583287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583298 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_2583298 : Nat := 118140960795 + 2583298 * 2 ^ 59
def prefixEnd_2583298 : Nat := 4983230072969 + 3 ^ 40 * 2583298 * 2
def baseEnd_2583298 : Nat := 1326473547798539068394635

theorem tailTrace_2583298 : CollatzResearch.WordTrace tailWord_2583298 prefixEnd_2583298 1326473547798539068394635 := by
  unfold tailWord_2583298
  simp only [CollatzResearch.WordTrace]
  refine ⟨23555154648790003254601637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62813745730106675345604365 23555154648790003254601637)
  ·
    refine ⟨4416591496648125610237807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23555154648790003254601637 4416591496648125610237807)
    ·
      refine ⟨6624887244972188415356711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4416591496648125610237807 6624887244972188415356711)
      ·
        refine ⟨9937330867458282623035067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6624887244972188415356711 9937330867458282623035067)
        ·
          refine ⟨14905996301187423934552601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9937330867458282623035067 14905996301187423934552601)
          ·
            refine ⟨11179497225890567950914451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14905996301187423934552601 11179497225890567950914451)
            ·
              refine ⟨16769245838835851926371677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11179497225890567950914451 16769245838835851926371677)
              ·
                refine ⟨6288467189563444472389379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16769245838835851926371677 6288467189563444472389379)
                ·
                  refine ⟨9432700784345166708584069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6288467189563444472389379 9432700784345166708584069)
                  ·
                    refine ⟨1768631397064718757859513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9432700784345166708584069 1768631397064718757859513)
                    ·
                      refine ⟨1326473547798539068394635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768631397064718757859513 1326473547798539068394635)
                      ·
                        rfl

theorem cell23_2583298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_2583298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583298 prefixEnd_2583298 := by exact prefixLift 2583298
  have htrace : WordTrace (prefixWord ++ tailWord_2583298) baseStart_2583298 baseEnd_2583298 := by
    simpa [prefixWord, tailWord_2583298, baseEnd_2583298] using wordTrace_append hprefix tailTrace_2583298
  have hstable : (prefixWord ++ tailWord_2583298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583298).length < 2 ^ (prefixWord ++ tailWord_2583298).sum := by decide
  have hdescent : baseEnd_2583298 < baseStart_2583298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583304 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 7]
def baseStart_2583304 : Nat := 118140960795 + 2583304 * 2 ^ 59
def prefixEnd_2583304 : Nat := 4983230072969 + 3 ^ 40 * 2583304 * 2
def baseEnd_2583304 : Nat := 147386292075829560546623

theorem tailTrace_2583304 : CollatzResearch.WordTrace tailWord_2583304 prefixEnd_2583304 147386292075829560546623 := by
  unfold tailWord_2583304
  simp only [CollatzResearch.WordTrace]
  refine ⟨47110418716569138021562483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62813891622092184028749977 47110418716569138021562483)
  ·
    refine ⟨70665628074853707032343725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47110418716569138021562483 70665628074853707032343725)
    ·
      refine ⟨26499610528070140137128897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70665628074853707032343725 26499610528070140137128897)
      ·
        refine ⟨19874707896052605102846673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26499610528070140137128897 19874707896052605102846673)
        ·
          refine ⟨14906030922039453827135005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19874707896052605102846673 14906030922039453827135005)
          ·
            refine ⟨5589761595764795185175627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14906030922039453827135005 5589761595764795185175627)
            ·
              refine ⟨8384642393647192777763441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5589761595764795185175627 8384642393647192777763441)
              ·
                refine ⟨6288481795235394583322581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8384642393647192777763441 6288481795235394583322581)
                ·
                  refine ⟨147386292075829560546623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6288481795235394583322581 147386292075829560546623)
                  ·
                    rfl

theorem cell23_2583304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 7].length) (baseStart_2583304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583304 prefixEnd_2583304 := by exact prefixLift 2583304
  have htrace : WordTrace (prefixWord ++ tailWord_2583304) baseStart_2583304 baseEnd_2583304 := by
    simpa [prefixWord, tailWord_2583304, baseEnd_2583304] using wordTrace_append hprefix tailTrace_2583304
  have hstable : (prefixWord ++ tailWord_2583304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583304).length < 2 ^ (prefixWord ++ tailWord_2583304).sum := by decide
  have hdescent : baseEnd_2583304 < baseStart_2583304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583332 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 2, 2, 2]
def baseStart_2583332 : Nat := 118140960795 + 2583332 * 2 ^ 59
def prefixEnd_2583332 : Nat := 4983230072969 + 3 ^ 40 * 2583332 * 2
def baseEnd_2583332 : Nat := 1326491006140791935369479

theorem tailTrace_2583332 : CollatzResearch.WordTrace tailWord_2583332 prefixEnd_2583332 1326491006140791935369479 := by
  unfold tailWord_2583332
  simp only [CollatzResearch.WordTrace]
  refine ⟨47110929338518418412572125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62814572451357891216762833 47110929338518418412572125)
  ·
    refine ⟨17666598501944406904714547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47110929338518418412572125 17666598501944406904714547)
    ·
      refine ⟨26499897752916610357071821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17666598501944406904714547 26499897752916610357071821)
      ·
        refine ⟨9937461657343728883901933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26499897752916610357071821 9937461657343728883901933)
        ·
          refine ⟨3726548121503898331463225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9937461657343728883901933 3726548121503898331463225)
          ·
            refine ⟨2794911091127923748597419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3726548121503898331463225 2794911091127923748597419)
            ·
              refine ⟨4192366636691885622896129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2794911091127923748597419 4192366636691885622896129)
              ·
                refine ⟨3144274977518914217172097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4192366636691885622896129 3144274977518914217172097)
                ·
                  refine ⟨2358206233139185662879073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3144274977518914217172097 2358206233139185662879073)
                  ·
                    refine ⟨1768654674854389247159305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2358206233139185662879073 1768654674854389247159305)
                    ·
                      refine ⟨1326491006140791935369479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768654674854389247159305 1326491006140791935369479)
                      ·
                        rfl

theorem cell23_2583332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_2583332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583332 prefixEnd_2583332 := by exact prefixLift 2583332
  have htrace : WordTrace (prefixWord ++ tailWord_2583332) baseStart_2583332 baseEnd_2583332 := by
    simpa [prefixWord, tailWord_2583332, baseEnd_2583332] using wordTrace_append hprefix tailTrace_2583332
  have hstable : (prefixWord ++ tailWord_2583332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583332).length < 2 ^ (prefixWord ++ tailWord_2583332).sum := by decide
  have hdescent : baseEnd_2583332 < baseStart_2583332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583338 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 7]
def baseStart_2583338 : Nat := 118140960795 + 2583338 * 2 ^ 59
def prefixEnd_2583338 : Nat := 4983230072969 + 3 ^ 40 * 2583338 * 2
def baseEnd_2583338 : Nat := 147388231891635434654939

theorem tailTrace_2583338 : CollatzResearch.WordTrace tailWord_2583338 prefixEnd_2583338 147388231891635434654939 := by
  unfold tailWord_2583338
  simp only [CollatzResearch.WordTrace]
  refine ⟨23555519378753774962465667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62814718343343399899908445 23555519378753774962465667)
  ·
    refine ⟨35333279068130662443698501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23555519378753774962465667 35333279068130662443698501)
    ·
      refine ⟨6624989825274499208193469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35333279068130662443698501 6624989825274499208193469)
      ·
        refine ⟨2484371184477937203072551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6624989825274499208193469 2484371184477937203072551)
        ·
          refine ⟨3726556776716905804608827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484371184477937203072551 3726556776716905804608827)
          ·
            refine ⟨5589835165075358706913241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3726556776716905804608827 5589835165075358706913241)
            ·
              refine ⟨4192376373806519030184931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5589835165075358706913241 4192376373806519030184931)
              ·
                refine ⟨6288564560709778545277397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4192376373806519030184931 6288564560709778545277397)
                ·
                  refine ⟨147388231891635434654939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6288564560709778545277397 147388231891635434654939)
                  ·
                    rfl

theorem cell23_2583338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_2583338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583338 prefixEnd_2583338 := by exact prefixLift 2583338
  have htrace : WordTrace (prefixWord ++ tailWord_2583338) baseStart_2583338 baseEnd_2583338 := by
    simpa [prefixWord, tailWord_2583338, baseEnd_2583338] using wordTrace_append hprefix tailTrace_2583338
  have hstable : (prefixWord ++ tailWord_2583338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583338).length < 2 ^ (prefixWord ++ tailWord_2583338).sum := by decide
  have hdescent : baseEnd_2583338 < baseStart_2583338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583388 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2583388 : Nat := 118140960795 + 2583388 * 2 ^ 59
def prefixEnd_2583388 : Nat := 4983230072969 + 3 ^ 40 * 2583388 * 2
def baseEnd_2583388 : Nat := 1326519761057443716269221

theorem tailTrace_2583388 : CollatzResearch.WordTrace tailWord_2583388 prefixEnd_2583388 1326519761057443716269221 := by
  unfold tailWord_2583388
  simp only [CollatzResearch.WordTrace]
  refine ⟨47111950582416979194591409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62815934109889305592788545 47111950582416979194591409)
  ·
    refine ⟨35333962936812734395943557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47111950582416979194591409 35333962936812734395943557)
    ·
      refine ⟨6625118050652387699239417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35333962936812734395943557 6625118050652387699239417)
      ·
        refine ⟨4968838537989290774429563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6625118050652387699239417 4968838537989290774429563)
        ·
          refine ⟨7453257806983936161644345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4968838537989290774429563 7453257806983936161644345)
          ·
            refine ⟨5589943355237952121233259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7453257806983936161644345 5589943355237952121233259)
            ·
              refine ⟨8384915032856928181849889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5589943355237952121233259 8384915032856928181849889)
              ·
                refine ⟨6288686274642696136387417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8384915032856928181849889 6288686274642696136387417)
                ·
                  refine ⟨4716514705982022102290563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6288686274642696136387417 4716514705982022102290563)
                  ·
                    refine ⟨7074772058973033153435845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4716514705982022102290563 7074772058973033153435845)
                    ·
                      refine ⟨1326519761057443716269221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7074772058973033153435845 1326519761057443716269221)
                      ·
                        rfl

theorem cell23_2583388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2583388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583388 prefixEnd_2583388 := by exact prefixLift 2583388
  have htrace : WordTrace (prefixWord ++ tailWord_2583388) baseStart_2583388 baseEnd_2583388 := by
    simpa [prefixWord, tailWord_2583388, baseEnd_2583388] using wordTrace_append hprefix tailTrace_2583388
  have hstable : (prefixWord ++ tailWord_2583388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583388).length < 2 ^ (prefixWord ++ tailWord_2583388).sum := by decide
  have hdescent : baseEnd_2583388 < baseStart_2583388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583391 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 3]
def baseStart_2583391 : Nat := 118140960795 + 2583391 * 2 ^ 59
def prefixEnd_2583391 : Nat := 4983230072969 + 3 ^ 40 * 2583391 * 2
def baseEnd_2583391 : Nat := 1326521301499407204531707

theorem tailTrace_2583391 : CollatzResearch.WordTrace tailWord_2583391 prefixEnd_2583391 1326521301499407204531707 := by
  unfold tailWord_2583391
  simp only [CollatzResearch.WordTrace]
  refine ⟨94224010583823089901542027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62816007055882059934361351 94224010583823089901542027)
  ·
    refine ⟨141336015875734634852313041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94224010583823089901542027 141336015875734634852313041)
    ·
      refine ⟨106002011906800976139234781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141336015875734634852313041 106002011906800976139234781)
      ·
        refine ⟨39750754465050366052213043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106002011906800976139234781 39750754465050366052213043)
        ·
          refine ⟨59626131697575549078319565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39750754465050366052213043 59626131697575549078319565)
          ·
            refine ⟨22359799386590830904369837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59626131697575549078319565 22359799386590830904369837)
            ·
              refine ⟨8384924769971561589138689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22359799386590830904369837 8384924769971561589138689)
              ·
                refine ⟨6288693577478671191854017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8384924769971561589138689 6288693577478671191854017)
                ·
                  refine ⟨4716520183109003393890513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6288693577478671191854017 4716520183109003393890513)
                  ·
                    refine ⟨3537390137331752545417885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4716520183109003393890513 3537390137331752545417885)
                    ·
                      refine ⟨1326521301499407204531707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3537390137331752545417885 1326521301499407204531707)
                      ·
                        rfl

theorem cell23_2583391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_2583391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583391 prefixEnd_2583391 := by exact prefixLift 2583391
  have htrace : WordTrace (prefixWord ++ tailWord_2583391) baseStart_2583391 baseEnd_2583391 := by
    simpa [prefixWord, tailWord_2583391, baseEnd_2583391] using wordTrace_append hprefix tailTrace_2583391
  have hstable : (prefixWord ++ tailWord_2583391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583391).length < 2 ^ (prefixWord ++ tailWord_2583391).sum := by decide
  have hdescent : baseEnd_2583391 < baseStart_2583391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583411 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 6]
def baseStart_2583411 : Nat := 118140960795 + 2583411 * 2 ^ 59
def prefixEnd_2583411 : Nat := 4983230072969 + 3 ^ 40 * 2583411 * 2
def baseEnd_2583411 : Nat := 147392396790277458475735

theorem tailTrace_2583411 : CollatzResearch.WordTrace tailWord_2583411 prefixEnd_2583411 147392396790277458475735 := by
  unfold tailWord_2583411
  simp only [CollatzResearch.WordTrace]
  refine ⟨94224740043750633317270087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62816493362500422211513391 94224740043750633317270087)
  ·
    refine ⟨141337110065625949975905131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94224740043750633317270087 141337110065625949975905131)
    ·
      refine ⟨212005665098438924963857697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141337110065625949975905131 212005665098438924963857697)
      ·
        refine ⟨159004248823829193722893273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212005665098438924963857697 159004248823829193722893273)
        ·
          refine ⟨119253186617871895292169955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159004248823829193722893273 119253186617871895292169955)
          ·
            refine ⟨178879779926807842938254933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119253186617871895292169955 178879779926807842938254933)
            ·
              refine ⟨2096247421017279409432675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 178879779926807842938254933 2096247421017279409432675)
              ·
                refine ⟨3144371131525919114149013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096247421017279409432675 3144371131525919114149013)
                ·
                  refine ⟨147392396790277458475735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3144371131525919114149013 147392396790277458475735)
                  ·
                    rfl

theorem cell23_2583411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 6].length) (baseStart_2583411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583411 prefixEnd_2583411 := by exact prefixLift 2583411
  have htrace : WordTrace (prefixWord ++ tailWord_2583411) baseStart_2583411 baseEnd_2583411 := by
    simpa [prefixWord, tailWord_2583411, baseEnd_2583411] using wordTrace_append hprefix tailTrace_2583411
  have hstable : (prefixWord ++ tailWord_2583411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583411).length < 2 ^ (prefixWord ++ tailWord_2583411).sum := by decide
  have hdescent : baseEnd_2583411 < baseStart_2583411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583461 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 4, 6, 2]
def baseStart_2583461 : Nat := 118140960795 + 2583461 * 2 ^ 59
def prefixEnd_2583461 : Nat := 4983230072969 + 3 ^ 40 * 2583461 * 2
def baseEnd_2583461 : Nat := 1326557245145221930656385

theorem tailTrace_2583461 : CollatzResearch.WordTrace tailWord_2583461 prefixEnd_2583461 1326557245145221930656385 := by
  unfold tailWord_2583461
  simp only [CollatzResearch.WordTrace]
  refine ⟨94226563693569491856590237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62817709129046327904393491 94226563693569491856590237)
  ·
    refine ⟨35334961385088559446221339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94226563693569491856590237 35334961385088559446221339)
    ·
      refine ⟨53002442077632839169332009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35334961385088559446221339 53002442077632839169332009)
      ·
        refine ⟨39751831558224629376999007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53002442077632839169332009 39751831558224629376999007)
        ·
          refine ⟨59627747337336944065498511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39751831558224629376999007 59627747337336944065498511)
          ·
            refine ⟨89441621006005416098247767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59627747337336944065498511 89441621006005416098247767)
            ·
              refine ⟨134162431509008124147371651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89441621006005416098247767 134162431509008124147371651)
              ·
                refine ⟨201243647263512186221057477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134162431509008124147371651 201243647263512186221057477)
                ·
                  refine ⟨37733183861908534916448277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201243647263512186221057477 37733183861908534916448277)
                  ·
                    refine ⟨1768742993526962574208513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37733183861908534916448277 1768742993526962574208513)
                    ·
                      refine ⟨1326557245145221930656385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768742993526962574208513 1326557245145221930656385)
                      ·
                        rfl

theorem cell23_2583461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_2583461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583461 prefixEnd_2583461 := by exact prefixLift 2583461
  have htrace : WordTrace (prefixWord ++ tailWord_2583461) baseStart_2583461 baseEnd_2583461 := by
    simpa [prefixWord, tailWord_2583461, baseEnd_2583461] using wordTrace_append hprefix tailTrace_2583461
  have hstable : (prefixWord ++ tailWord_2583461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583461).length < 2 ^ (prefixWord ++ tailWord_2583461).sum := by decide
  have hdescent : baseEnd_2583461 < baseStart_2583461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583504 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_2583504 : Nat := 118140960795 + 2583504 * 2 ^ 59
def prefixEnd_2583504 : Nat := 4983230072969 + 3 ^ 40 * 2583504 * 2
def baseEnd_2583504 : Nat := 1326579324813365262418687

theorem tailTrace_2583504 : CollatzResearch.WordTrace tailWord_2583504 prefixEnd_2583504 1326579324813365262418687 := by
  unfold tailWord_2583504
  simp only [CollatzResearch.WordTrace]
  refine ⟨47114066016206855100202783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62818754688275806800270377 47114066016206855100202783)
  ·
    refine ⟨70671099024310282650304175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47114066016206855100202783 70671099024310282650304175)
    ·
      refine ⟨106006648536465423975456263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70671099024310282650304175 106006648536465423975456263)
      ·
        refine ⟨159009972804698135963184395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106006648536465423975456263 159009972804698135963184395)
        ·
          refine ⟨238514959207047203944776593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159009972804698135963184395 238514959207047203944776593)
          ·
            refine ⟨178886219405285402958582445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238514959207047203944776593 178886219405285402958582445)
            ·
              refine ⟨67082332276982026109468417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178886219405285402958582445 67082332276982026109468417)
              ·
                refine ⟨50311749207736519582101313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67082332276982026109468417 50311749207736519582101313)
                ·
                  refine ⟨37733811905802389686575985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50311749207736519582101313 37733811905802389686575985)
                  ·
                    refine ⟨28300358929351792264931989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37733811905802389686575985 28300358929351792264931989)
                    ·
                      refine ⟨1326579324813365262418687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28300358929351792264931989 1326579324813365262418687)
                      ·
                        rfl

theorem cell23_2583504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_2583504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583504 prefixEnd_2583504 := by exact prefixLift 2583504
  have htrace : WordTrace (prefixWord ++ tailWord_2583504) baseStart_2583504 baseEnd_2583504 := by
    simpa [prefixWord, tailWord_2583504, baseEnd_2583504] using wordTrace_append hprefix tailTrace_2583504
  have hstable : (prefixWord ++ tailWord_2583504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583504).length < 2 ^ (prefixWord ++ tailWord_2583504).sum := by decide
  have hdescent : baseEnd_2583504 < baseStart_2583504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583512 : List Nat := [2, 1, 2, 2, 2, 3, 2, 4, 1, 2, 2]
def baseStart_2583512 : Nat := 118140960795 + 2583512 * 2 ^ 59
def prefixEnd_2583512 : Nat := 4983230072969 + 3 ^ 40 * 2583512 * 2
def baseEnd_2583512 : Nat := 1326583432658601231118651

theorem tailTrace_2583512 : CollatzResearch.WordTrace tailWord_2583512 prefixEnd_2583512 1326583432658601231118651 := by
  unfold tailWord_2583512
  simp only [CollatzResearch.WordTrace]
  refine ⟨47114211908192363783348395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62818949210923151711131193 47114211908192363783348395)
  ·
    refine ⟨70671317862288545675022593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47114211908192363783348395 70671317862288545675022593)
    ·
      refine ⟨53003488396716409256266945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70671317862288545675022593 53003488396716409256266945)
      ·
        refine ⟨39752616297537306942200209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53003488396716409256266945 39752616297537306942200209)
        ·
          refine ⟨29814462223152980206650157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39752616297537306942200209 29814462223152980206650157)
          ·
            refine ⟨11180423333682367577493809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29814462223152980206650157 11180423333682367577493809)
            ·
              refine ⟨8385317500261775683120357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11180423333682367577493809 8385317500261775683120357)
              ·
                refine ⟨1572247031299082940585067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8385317500261775683120357 1572247031299082940585067)
                ·
                  refine ⟨2358370546948624410877601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572247031299082940585067 2358370546948624410877601)
                  ·
                    refine ⟨1768777910211468308158201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2358370546948624410877601 1768777910211468308158201)
                    ·
                      refine ⟨1326583432658601231118651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768777910211468308158201 1326583432658601231118651)
                      ·
                        rfl

theorem cell23_2583512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_2583512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583512 prefixEnd_2583512 := by exact prefixLift 2583512
  have htrace : WordTrace (prefixWord ++ tailWord_2583512) baseStart_2583512 baseEnd_2583512 := by
    simpa [prefixWord, tailWord_2583512, baseEnd_2583512] using wordTrace_append hprefix tailTrace_2583512
  have hstable : (prefixWord ++ tailWord_2583512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583512).length < 2 ^ (prefixWord ++ tailWord_2583512).sum := by decide
  have hdescent : baseEnd_2583512 < baseStart_2583512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583528 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_2583528 : Nat := 118140960795 + 2583528 * 2 ^ 59
def prefixEnd_2583528 : Nat := 4983230072969 + 3 ^ 40 * 2583528 * 2
def baseEnd_2583528 : Nat := 1326591648349073168518577

theorem tailTrace_2583528 : CollatzResearch.WordTrace tailWord_2583528 prefixEnd_2583528 1326591648349073168518577 := by
  unfold tailWord_2583528
  simp only [CollatzResearch.WordTrace]
  refine ⟨47114503692163381149639619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62819338256217841532852825 47114503692163381149639619)
  ·
    refine ⟨70671755538245071724459429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47114503692163381149639619 70671755538245071724459429)
    ·
      refine ⟨13250954163420950948336143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70671755538245071724459429 13250954163420950948336143)
      ·
        refine ⟨19876431245131426422504215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13250954163420950948336143 19876431245131426422504215)
        ·
          refine ⟨29814646867697139633756323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19876431245131426422504215 29814646867697139633756323)
          ·
            refine ⟨44721970301545709450634485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29814646867697139633756323 44721970301545709450634485)
            ·
              refine ⟨4192684715769910260996983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44721970301545709450634485 4192684715769910260996983)
              ·
                refine ⟨6289027073654865391495475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4192684715769910260996983 6289027073654865391495475)
                ·
                  refine ⟨9433540610482298087243213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6289027073654865391495475 9433540610482298087243213)
                  ·
                    refine ⟨3537577728930861782716205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9433540610482298087243213 3537577728930861782716205)
                    ·
                      refine ⟨1326591648349073168518577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3537577728930861782716205 1326591648349073168518577)
                      ·
                        rfl

theorem cell23_2583528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_2583528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583528 prefixEnd_2583528 := by exact prefixLift 2583528
  have htrace : WordTrace (prefixWord ++ tailWord_2583528) baseStart_2583528 baseEnd_2583528 := by
    simpa [prefixWord, tailWord_2583528, baseEnd_2583528] using wordTrace_append hprefix tailTrace_2583528
  have hstable : (prefixWord ++ tailWord_2583528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583528).length < 2 ^ (prefixWord ++ tailWord_2583528).sum := by decide
  have hdescent : baseEnd_2583528 < baseStart_2583528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583540 : List Nat := [2, 6, 2, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2583540 : Nat := 118140960795 + 2583540 * 2 ^ 59
def prefixEnd_2583540 : Nat := 4983230072969 + 3 ^ 40 * 2583540 * 2
def baseEnd_2583540 : Nat := 1326597810116927121568523

theorem tailTrace_2583540 : CollatzResearch.WordTrace tailWord_2583540 prefixEnd_2583540 1326597810116927121568523 := by
  unfold tailWord_2583540
  simp only [CollatzResearch.WordTrace]
  refine ⟨47114722530141644174358037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62819630040188858899144049 47114722530141644174358037)
  ·
    refine ⟨2208502618600389570673033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47114722530141644174358037 2208502618600389570673033)
    ·
      refine ⟨1656376963950292178004775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2208502618600389570673033 1656376963950292178004775)
      ·
        refine ⟨2484565445925438267007163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1656376963950292178004775 2484565445925438267007163)
        ·
          refine ⟨3726848168888157400510745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484565445925438267007163 3726848168888157400510745)
          ·
            refine ⟨2795136126666118050383059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3726848168888157400510745 2795136126666118050383059)
            ·
              refine ⟨4192704189999177075574589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795136126666118050383059 4192704189999177075574589)
              ·
                refine ⟨1572264071249691403340471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4192704189999177075574589 1572264071249691403340471)
                ·
                  refine ⟨2358396106874537105010707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572264071249691403340471 2358396106874537105010707)
                  ·
                    refine ⟨3537594160311805657516061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2358396106874537105010707 3537594160311805657516061)
                    ·
                      refine ⟨1326597810116927121568523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3537594160311805657516061 1326597810116927121568523)
                      ·
                        rfl

theorem cell23_2583540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2583540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583540 prefixEnd_2583540 := by exact prefixLift 2583540
  have htrace : WordTrace (prefixWord ++ tailWord_2583540) baseStart_2583540 baseEnd_2583540 := by
    simpa [prefixWord, tailWord_2583540, baseEnd_2583540] using wordTrace_append hprefix tailTrace_2583540
  have hstable : (prefixWord ++ tailWord_2583540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583540).length < 2 ^ (prefixWord ++ tailWord_2583540).sum := by decide
  have hdescent : baseEnd_2583540 < baseStart_2583540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583571 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 3]
def baseStart_2583571 : Nat := 118140960795 + 2583571 * 2 ^ 59
def prefixEnd_2583571 : Nat := 4983230072969 + 3 ^ 40 * 2583571 * 2
def baseEnd_2583571 : Nat := 1326613728017216500280879

theorem tailTrace_2583571 : CollatzResearch.WordTrace tailWord_2583571 prefixEnd_2583571 1326613728017216500280879 := by
  unfold tailWord_2583571
  simp only [CollatzResearch.WordTrace]
  refine ⟨94230575723170980643094567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62820383815447320428729711 94230575723170980643094567)
  ·
    refine ⟨141345863584756470964641851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94230575723170980643094567 141345863584756470964641851)
    ·
      refine ⟨212018795377134706446962777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141345863584756470964641851 212018795377134706446962777)
      ·
        refine ⟨159014096532851029835222083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212018795377134706446962777 159014096532851029835222083)
        ·
          refine ⟨238521144799276544752833125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159014096532851029835222083 238521144799276544752833125)
          ·
            refine ⟨44722714649864352141156211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238521144799276544752833125 44722714649864352141156211)
            ·
              refine ⟨67084071974796528211734317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44722714649864352141156211 67084071974796528211734317)
              ·
                refine ⟨25156526990548698079400369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67084071974796528211734317 25156526990548698079400369)
                ·
                  refine ⟨18867395242911523559550277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25156526990548698079400369 18867395242911523559550277)
                  ·
                    refine ⟨3537636608045910667415677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18867395242911523559550277 3537636608045910667415677)
                    ·
                      refine ⟨1326613728017216500280879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3537636608045910667415677 1326613728017216500280879)
                      ·
                        rfl

theorem cell23_2583571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 3].length) (baseStart_2583571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583571 prefixEnd_2583571 := by exact prefixLift 2583571
  have htrace : WordTrace (prefixWord ++ tailWord_2583571) baseStart_2583571 baseEnd_2583571 := by
    simpa [prefixWord, tailWord_2583571, baseEnd_2583571] using wordTrace_append hprefix tailTrace_2583571
  have hstable : (prefixWord ++ tailWord_2583571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583571).length < 2 ^ (prefixWord ++ tailWord_2583571).sum := by decide
  have hdescent : baseEnd_2583571 < baseStart_2583571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583588 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2583588 : Nat := 118140960795 + 2583588 * 2 ^ 59
def prefixEnd_2583588 : Nat := 4983230072969 + 3 ^ 40 * 2583588 * 2
def baseEnd_2583588 : Nat := 1326622457188342933768301

theorem tailTrace_2583588 : CollatzResearch.WordTrace tailWord_2583588 prefixEnd_2583588 1326622457188342933768301 := by
  unfold tailWord_2583588
  simp only [CollatzResearch.WordTrace]
  refine ⟨47115597882054696273231709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62820797176072928364308945 47115597882054696273231709)
  ·
    refine ⟨17668349205770511102461891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47115597882054696273231709 17668349205770511102461891)
    ·
      refine ⟨26502523808655766653692837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17668349205770511102461891 26502523808655766653692837)
      ·
        refine ⟨4969223214122956247567407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26502523808655766653692837 4969223214122956247567407)
        ·
          refine ⟨7453834821184434371351111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969223214122956247567407 7453834821184434371351111)
          ·
            refine ⟨11180752231776651557026667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7453834821184434371351111 11180752231776651557026667)
            ·
              refine ⟨16771128347664977335540001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11180752231776651557026667 16771128347664977335540001)
              ·
                refine ⟨12578346260748733001655001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16771128347664977335540001 12578346260748733001655001)
                ·
                  refine ⟨9433759695561549751241251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12578346260748733001655001 9433759695561549751241251)
                  ·
                    refine ⟨14150639543342324626861877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9433759695561549751241251 14150639543342324626861877)
                    ·
                      refine ⟨1326622457188342933768301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14150639543342324626861877 1326622457188342933768301)
                      ·
                        rfl

theorem cell23_2583588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2583588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583588 prefixEnd_2583588 := by exact prefixLift 2583588
  have htrace : WordTrace (prefixWord ++ tailWord_2583588) baseStart_2583588 baseEnd_2583588 := by
    simpa [prefixWord, tailWord_2583588, baseEnd_2583588] using wordTrace_append hprefix tailTrace_2583588
  have hstable : (prefixWord ++ tailWord_2583588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583588).length < 2 ^ (prefixWord ++ tailWord_2583588).sum := by decide
  have hdescent : baseEnd_2583588 < baseStart_2583588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583655 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 2, 5]
def baseStart_2583655 : Nat := 118140960795 + 2583655 * 2 ^ 59
def prefixEnd_2583655 : Nat := 4983230072969 + 3 ^ 40 * 2583655 * 2
def baseEnd_2583655 : Nat := 442218953464064723876831

theorem tailTrace_2583655 : CollatzResearch.WordTrace tailWord_2583655 prefixEnd_2583655 442218953464064723876831 := by
  unfold tailWord_2583655
  simp only [CollatzResearch.WordTrace]
  refine ⟨94233639454866662989152419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62822426303244441992768279 94233639454866662989152419)
  ·
    refine ⟨141350459182299994483728629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94233639454866662989152419 141350459182299994483728629)
    ·
      refine ⟨13251605548340624482849559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141350459182299994483728629 13251605548340624482849559)
      ·
        refine ⟨19877408322510936724274339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13251605548340624482849559 19877408322510936724274339)
        ·
          refine ⟨29816112483766405086411509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19877408322510936724274339 29816112483766405086411509)
          ·
            refine ⟨2795260545353100476851079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29816112483766405086411509 2795260545353100476851079)
            ·
              refine ⟨4192890818029650715276619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795260545353100476851079 4192890818029650715276619)
              ·
                refine ⟨6289336227044476072914929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4192890818029650715276619 6289336227044476072914929)
                ·
                  refine ⟨4717002170283357054686197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6289336227044476072914929 4717002170283357054686197)
                  ·
                    refine ⟨442218953464064723876831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4717002170283357054686197 442218953464064723876831)
                    ·
                      rfl

theorem cell23_2583655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_2583655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583655 prefixEnd_2583655 := by exact prefixLift 2583655
  have htrace : WordTrace (prefixWord ++ tailWord_2583655) baseStart_2583655 baseEnd_2583655 := by
    simpa [prefixWord, tailWord_2583655, baseEnd_2583655] using wordTrace_append hprefix tailTrace_2583655
  have hstable : (prefixWord ++ tailWord_2583655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583655).length < 2 ^ (prefixWord ++ tailWord_2583655).sum := by decide
  have hdescent : baseEnd_2583655 < baseStart_2583655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583671 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_2583671 : Nat := 118140960795 + 2583671 * 2 ^ 59
def prefixEnd_2583671 : Nat := 4983230072969 + 3 ^ 40 * 2583671 * 2
def baseEnd_2583671 : Nat := 1326665076082666109030419

theorem tailTrace_2583671 : CollatzResearch.WordTrace tailWord_2583671 prefixEnd_2583671 1326665076082666109030419 := by
  unfold tailWord_2583671
  simp only [CollatzResearch.WordTrace]
  refine ⟨94234223022808697721734867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62822815348539131814489911 94234223022808697721734867)
  ·
    refine ⟨141351334534213046582602301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94234223022808697721734867 141351334534213046582602301)
    ·
      refine ⟨53006750450329892468475863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141351334534213046582602301 53006750450329892468475863)
      ·
        refine ⟨79510125675494838702713795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53006750450329892468475863 79510125675494838702713795)
        ·
          refine ⟨119265188513242258054070693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79510125675494838702713795 119265188513242258054070693)
          ·
            refine ⟨22362222846232923385138255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119265188513242258054070693 22362222846232923385138255)
            ·
              refine ⟨33543334269349385077707383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22362222846232923385138255 33543334269349385077707383)
              ·
                refine ⟨50315001404024077616561075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33543334269349385077707383 50315001404024077616561075)
                ·
                  refine ⟨75472502106036116424841613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50315001404024077616561075 75472502106036116424841613)
                  ·
                    refine ⟨28302188289763543659315605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75472502106036116424841613 28302188289763543659315605)
                    ·
                      refine ⟨1326665076082666109030419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28302188289763543659315605 1326665076082666109030419)
                      ·
                        rfl

theorem cell23_2583671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_2583671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583671 prefixEnd_2583671 := by exact prefixLift 2583671
  have htrace : WordTrace (prefixWord ++ tailWord_2583671) baseStart_2583671 baseEnd_2583671 := by
    simpa [prefixWord, tailWord_2583671, baseEnd_2583671] using wordTrace_append hprefix tailTrace_2583671
  have hstable : (prefixWord ++ tailWord_2583671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583671).length < 2 ^ (prefixWord ++ tailWord_2583671).sum := by decide
  have hdescent : baseEnd_2583671 < baseStart_2583671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
