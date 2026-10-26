import V185TrunkScan22Chunk464

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4145188 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_4145188 : Nat := 118140960795 + 4145188 * 2 ^ 59
def prefixEnd_4145188 : Nat := 4983230072969 + 3 ^ 40 * 4145188 * 2
def baseEnd_4145188 : Nat := 1418982564832955444391089

theorem tailTrace_4145188 : CollatzResearch.WordTrace tailWord_4145188 prefixEnd_4145188 1418982564832955444391089 := by
  unfold tailWord_4145188
  simp only [CollatzResearch.WordTrace]
  refine ⟨75593713453349646296694109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100791617937799528395592145 75593713453349646296694109)
  ·
    refine ⟨28347642545006117361260291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75593713453349646296694109 28347642545006117361260291)
    ·
      refine ⟨42521463817509176041890437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28347642545006117361260291 42521463817509176041890437)
      ·
        refine ⟨7972774465782970507854457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42521463817509176041890437 7972774465782970507854457)
        ·
          refine ⟨5979580849337227880890843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7972774465782970507854457 5979580849337227880890843)
          ·
            refine ⟨8969371274005841821336265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979580849337227880890843 8969371274005841821336265)
            ·
              refine ⟨6727028455504381366002199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8969371274005841821336265 6727028455504381366002199)
              ·
                refine ⟨10090542683256572049003299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6727028455504381366002199 10090542683256572049003299)
                ·
                  refine ⟨15135814024884858073504949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10090542683256572049003299 15135814024884858073504949)
                  ·
                    refine ⟨1418982564832955444391089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15135814024884858073504949 1418982564832955444391089)
                    ·
                      rfl

theorem cell22_4145188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_4145188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145188 prefixEnd_4145188 := by exact prefixLift 4145188
  have htrace : WordTrace (prefixWord ++ tailWord_4145188) baseStart_4145188 baseEnd_4145188 := by
    simpa [prefixWord, tailWord_4145188, baseEnd_4145188] using wordTrace_append hprefix tailTrace_4145188
  have hstable : (prefixWord ++ tailWord_4145188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145188).length < 2 ^ (prefixWord ++ tailWord_4145188).sum := by decide
  have hdescent : baseEnd_4145188 < baseStart_4145188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145201 : List Nat := [1, 2, 2, 3, 1, 4, 3, 6]
def baseStart_4145201 : Nat := 118140960795 + 4145201 * 2 ^ 59
def prefixEnd_4145201 : Nat := 4983230072969 + 3 ^ 40 * 4145201 * 2
def baseEnd_4145201 : Nat := 157665223888736415979561

theorem tailTrace_4145201 : CollatzResearch.WordTrace tailWord_4145201 prefixEnd_4145201 157665223888736415979561 := by
  unfold tailWord_4145201
  simp only [CollatzResearch.WordTrace]
  refine ⟨151187901055652195813611457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100791934037101463875740971 151187901055652195813611457)
  ·
    refine ⟨113390925791739146860208593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151187901055652195813611457 113390925791739146860208593)
    ·
      refine ⟨85043194343804360145156445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113390925791739146860208593 85043194343804360145156445)
      ·
        refine ⟨31891197878926635054433667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85043194343804360145156445 31891197878926635054433667)
        ·
          refine ⟨47836796818389952581650501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31891197878926635054433667 47836796818389952581650501)
          ·
            refine ⟨8969399403448116109059469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47836796818389952581650501 8969399403448116109059469)
            ·
              refine ⟨3363524776293043540897301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8969399403448116109059469 3363524776293043540897301)
              ·
                refine ⟨157665223888736415979561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3363524776293043540897301 157665223888736415979561)
                ·
                  rfl

theorem cell22_4145201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 6].length) (baseStart_4145201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145201 prefixEnd_4145201 := by exact prefixLift 4145201
  have htrace : WordTrace (prefixWord ++ tailWord_4145201) baseStart_4145201 baseEnd_4145201 := by
    simpa [prefixWord, tailWord_4145201, baseEnd_4145201] using wordTrace_append hprefix tailTrace_4145201
  have hstable : (prefixWord ++ tailWord_4145201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145201).length < 2 ^ (prefixWord ++ tailWord_4145201).sum := by decide
  have hdescent : baseEnd_4145201 < baseStart_4145201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145310 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4145310 : Nat := 118140960795 + 4145310 * 2 ^ 59
def prefixEnd_4145310 : Nat := 4983230072969 + 3 ^ 40 * 4145310 * 2
def baseEnd_4145310 : Nat := 1419024327926187792840715

theorem tailTrace_4145310 : CollatzResearch.WordTrace tailWord_4145310 prefixEnd_4145310 1419024327926187792840715 := by
  unfold tailWord_4145310
  simp only [CollatzResearch.WordTrace]
  refine ⟨18898984576532163428666173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100794584408171538286219589 18898984576532163428666173)
  ·
    refine ⟨7087119216199561285749815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18898984576532163428666173 7087119216199561285749815)
    ·
      refine ⟨10630678824299341928624723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7087119216199561285749815 10630678824299341928624723)
      ·
        refine ⟨15946018236449012892937085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10630678824299341928624723 15946018236449012892937085)
        ·
          refine ⟨5979756838668379834851407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15946018236449012892937085 5979756838668379834851407)
          ·
            refine ⟨8969635258002569752277111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979756838668379834851407 8969635258002569752277111)
            ·
              refine ⟨13454452887003854628415667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8969635258002569752277111 13454452887003854628415667)
              ·
                refine ⟨20181679330505781942623501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13454452887003854628415667 20181679330505781942623501)
                ·
                  refine ⟨7568129748939668228483813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20181679330505781942623501 7568129748939668228483813)
                  ·
                    refine ⟨1419024327926187792840715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7568129748939668228483813 1419024327926187792840715)
                    ·
                      rfl

theorem cell22_4145310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4145310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145310 prefixEnd_4145310 := by exact prefixLift 4145310
  have htrace : WordTrace (prefixWord ++ tailWord_4145310) baseStart_4145310 baseEnd_4145310 := by
    simpa [prefixWord, tailWord_4145310, baseEnd_4145310] using wordTrace_append hprefix tailTrace_4145310
  have hstable : (prefixWord ++ tailWord_4145310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145310).length < 2 ^ (prefixWord ++ tailWord_4145310).sum := by decide
  have hdescent : baseEnd_4145310 < baseStart_4145310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145368 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 5, 3]
def baseStart_4145368 : Nat := 118140960795 + 4145368 * 2 ^ 59
def prefixEnd_4145368 : Nat := 4983230072969 + 3 ^ 40 * 4145368 * 2
def baseEnd_4145368 : Nat := 1419044182511494974890537

theorem tailTrace_4145368 : CollatzResearch.WordTrace tailWord_4145368 prefixEnd_4145368 1419044182511494974890537 := by
  unfold tailWord_4145368
  simp only [CollatzResearch.WordTrace]
  refine ⟨75596996023023591667470379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100795994697364788889960505 75596996023023591667470379)
  ·
    refine ⟨113395494034535387501205569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75596996023023591667470379 113395494034535387501205569)
    ·
      refine ⟨85046620525901540625904177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113395494034535387501205569 85046620525901540625904177)
      ·
        refine ⟨63784965394426155469428133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85046620525901540625904177 63784965394426155469428133)
        ·
          refine ⟨11959681011454904150517775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63784965394426155469428133 11959681011454904150517775)
          ·
            refine ⟨17939521517182356225776663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11959681011454904150517775 17939521517182356225776663)
            ·
              refine ⟨26909282275773534338664995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17939521517182356225776663 26909282275773534338664995)
              ·
                refine ⟨40363923413660301507997493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26909282275773534338664995 40363923413660301507997493)
                ·
                  refine ⟨3784117820030653266374765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40363923413660301507997493 3784117820030653266374765)
                  ·
                    refine ⟨1419044182511494974890537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3784117820030653266374765 1419044182511494974890537)
                    ·
                      rfl

theorem cell22_4145368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_4145368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145368 prefixEnd_4145368 := by exact prefixLift 4145368
  have htrace : WordTrace (prefixWord ++ tailWord_4145368) baseStart_4145368 baseEnd_4145368 := by
    simpa [prefixWord, tailWord_4145368, baseEnd_4145368] using wordTrace_append hprefix tailTrace_4145368
  have hstable : (prefixWord ++ tailWord_4145368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145368).length < 2 ^ (prefixWord ++ tailWord_4145368).sum := by decide
  have hdescent : baseEnd_4145368 < baseStart_4145368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145378 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4145378 : Nat := 118140960795 + 4145378 * 2 ^ 59
def prefixEnd_4145378 : Nat := 4983230072969 + 3 ^ 40 * 4145378 * 2
def baseEnd_4145378 : Nat := 1419047605715858282140507

theorem tailTrace_4145378 : CollatzResearch.WordTrace tailWord_4145378 prefixEnd_4145378 1419047605715858282140507 := by
  unfold tailWord_4145378
  simp only [CollatzResearch.WordTrace]
  refine ⟨37798589194002738760701197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100796237850673970028536525 37798589194002738760701197)
  ·
    refine ⟨14174470947751027035262949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37798589194002738760701197 14174470947751027035262949)
    ·
      refine ⟨2657713302703317569111803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14174470947751027035262949 2657713302703317569111803)
      ·
        refine ⟨3986569954054976353667705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657713302703317569111803 3986569954054976353667705)
        ·
          refine ⟨2989927465541232265250779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3986569954054976353667705 2989927465541232265250779)
          ·
            refine ⟨4484891198311848397876169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2989927465541232265250779 4484891198311848397876169)
            ·
              refine ⟨3363668398733886298407127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4484891198311848397876169 3363668398733886298407127)
              ·
                refine ⟨5045502598100829447610691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363668398733886298407127 5045502598100829447610691)
                ·
                  refine ⟨7568253897151244171416037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5045502598100829447610691 7568253897151244171416037)
                  ·
                    refine ⟨1419047605715858282140507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7568253897151244171416037 1419047605715858282140507)
                    ·
                      rfl

theorem cell22_4145378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4145378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145378 prefixEnd_4145378 := by exact prefixLift 4145378
  have htrace : WordTrace (prefixWord ++ tailWord_4145378) baseStart_4145378 baseEnd_4145378 := by
    simpa [prefixWord, tailWord_4145378, baseEnd_4145378] using wordTrace_append hprefix tailTrace_4145378
  have hstable : (prefixWord ++ tailWord_4145378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145378).length < 2 ^ (prefixWord ++ tailWord_4145378).sum := by decide
  have hdescent : baseEnd_4145378 < baseStart_4145378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145456 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_4145456 : Nat := 118140960795 + 4145456 * 2 ^ 59
def prefixEnd_4145456 : Nat := 4983230072969 + 3 ^ 40 * 4145456 * 2
def baseEnd_4145456 : Nat := 1419074306709892078690267

theorem tailTrace_4145456 : CollatzResearch.WordTrace tailWord_4145456 prefixEnd_4145456 1419074306709892078690267 := by
  unfold tailWord_4145456
  simp only [CollatzResearch.WordTrace]
  refine ⟨75598600834864187182072111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100798134446485582909429481 75598600834864187182072111)
  ·
    refine ⟨113397901252296280773108167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75598600834864187182072111 113397901252296280773108167)
    ·
      refine ⟨170096851878444421159662251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113397901252296280773108167 170096851878444421159662251)
      ·
        refine ⟨255145277817666631739493377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170096851878444421159662251 255145277817666631739493377)
        ·
          refine ⟨191358958363249973804620033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255145277817666631739493377 191358958363249973804620033)
          ·
            refine ⟨143519218772437480353465025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191358958363249973804620033 143519218772437480353465025)
            ·
              refine ⟨107639414079328110265098769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143519218772437480353465025 107639414079328110265098769)
              ·
                refine ⟨80729560559496082698824077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107639414079328110265098769 80729560559496082698824077)
                ·
                  refine ⟨30273585209811031012059029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80729560559496082698824077 30273585209811031012059029)
                  ·
                    refine ⟨1419074306709892078690267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30273585209811031012059029 1419074306709892078690267)
                    ·
                      rfl

theorem cell22_4145456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_4145456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145456 prefixEnd_4145456 := by exact prefixLift 4145456
  have htrace : WordTrace (prefixWord ++ tailWord_4145456) baseStart_4145456 baseEnd_4145456 := by
    simpa [prefixWord, tailWord_4145456, baseEnd_4145456] using wordTrace_append hprefix tailTrace_4145456
  have hstable : (prefixWord ++ tailWord_4145456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145456).length < 2 ^ (prefixWord ++ tailWord_4145456).sum := by decide
  have hdescent : baseEnd_4145456 < baseStart_4145456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145460 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 6]
def baseStart_4145460 : Nat := 118140960795 + 4145460 * 2 ^ 59
def prefixEnd_4145460 : Nat := 4983230072969 + 3 ^ 40 * 4145460 * 2
def baseEnd_4145460 : Nat := 473025225330545800530085

theorem tailTrace_4145460 : CollatzResearch.WordTrace tailWord_4145460 prefixEnd_4145460 473025225330545800530085 := by
  unfold tailWord_4145460
  simp only [CollatzResearch.WordTrace]
  refine ⟨75598673780856941523644917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100798231707809255364859889 75598673780856941523644917)
  ·
    refine ⟨7087375666955338267841711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75598673780856941523644917 7087375666955338267841711)
    ·
      refine ⟨10631063500433007401762567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7087375666955338267841711 10631063500433007401762567)
      ·
        refine ⟨15946595250649511102643851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10631063500433007401762567 15946595250649511102643851)
        ·
          refine ⟨23919892875974266653965777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15946595250649511102643851 23919892875974266653965777)
          ·
            refine ⟨17939919656980699990474333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23919892875974266653965777 17939919656980699990474333)
            ·
              refine ⟨6727469871367762496427875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17939919656980699990474333 6727469871367762496427875)
              ·
                refine ⟨10091204807051643744641813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6727469871367762496427875 10091204807051643744641813)
                ·
                  refine ⟨473025225330545800530085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10091204807051643744641813 473025225330545800530085)
                  ·
                    rfl

theorem cell22_4145460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_4145460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145460 prefixEnd_4145460 := by exact prefixLift 4145460
  have htrace : WordTrace (prefixWord ++ tailWord_4145460) baseStart_4145460 baseEnd_4145460 := by
    simpa [prefixWord, tailWord_4145460, baseEnd_4145460] using wordTrace_append hprefix tailTrace_4145460
  have hstable : (prefixWord ++ tailWord_4145460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145460).length < 2 ^ (prefixWord ++ tailWord_4145460).sum := by decide
  have hdescent : baseEnd_4145460 < baseStart_4145460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145537 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 3, 3]
def baseStart_4145537 : Nat := 118140960795 + 4145537 * 2 ^ 59
def prefixEnd_4145537 : Nat := 4983230072969 + 3 ^ 40 * 4145537 * 2
def baseEnd_4145537 : Nat := 1419102034665234867415019

theorem tailTrace_4145537 : CollatzResearch.WordTrace tailWord_4145537 prefixEnd_4145537 1419102034665234867415019 := by
  unfold tailWord_4145537
  simp only [CollatzResearch.WordTrace]
  refine ⟨151200155982434925197842865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100800103988289950131895243 151200155982434925197842865)
  ·
    refine ⟨113400116986826193898382149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151200155982434925197842865 113400116986826193898382149)
    ·
      refine ⟨21262521935029911355946653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113400116986826193898382149 21262521935029911355946653)
      ·
        refine ⟨7973445725636216758479995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21262521935029911355946653 7973445725636216758479995)
        ·
          refine ⟨11960168588454325137719993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7973445725636216758479995 11960168588454325137719993)
          ·
            refine ⟨8970126441340743853289995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11960168588454325137719993 8970126441340743853289995)
            ·
              refine ⟨13455189662011115779934993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8970126441340743853289995 13455189662011115779934993)
              ·
                refine ⟨10091392246508336834951245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13455189662011115779934993 10091392246508336834951245)
                ·
                  refine ⟨3784272092440626313106717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10091392246508336834951245 3784272092440626313106717)
                  ·
                    refine ⟨1419102034665234867415019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3784272092440626313106717 1419102034665234867415019)
                    ·
                      rfl

theorem cell22_4145537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_4145537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145537 prefixEnd_4145537 := by exact prefixLift 4145537
  have htrace : WordTrace (prefixWord ++ tailWord_4145537) baseStart_4145537 baseEnd_4145537 := by
    simpa [prefixWord, tailWord_4145537, baseEnd_4145537] using wordTrace_append hprefix tailTrace_4145537
  have hstable : (prefixWord ++ tailWord_4145537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145537).length < 2 ^ (prefixWord ++ tailWord_4145537).sum := by decide
  have hdescent : baseEnd_4145537 < baseStart_4145537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145597 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_4145597 : Nat := 118140960795 + 4145597 * 2 ^ 59
def prefixEnd_4145597 : Nat := 4983230072969 + 3 ^ 40 * 4145597 * 2
def baseEnd_4145597 : Nat := 1419122573891414710914835

theorem tailTrace_4145597 : CollatzResearch.WordTrace tailWord_4145597 prefixEnd_4145597 1419122573891414710914835 := by
  unfold tailWord_4145597
  simp only [CollatzResearch.WordTrace]
  refine ⟨151202344362217555445027045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100801562908145036963351363 151202344362217555445027045)
  ·
    refine ⟨28350439567915791645942571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151202344362217555445027045 28350439567915791645942571)
    ·
      refine ⟨42525659351873687468913857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28350439567915791645942571 42525659351873687468913857)
      ·
        refine ⟨31894244513905265601685393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42525659351873687468913857 31894244513905265601685393)
        ·
          refine ⟨23920683385428949201264045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31894244513905265601685393 23920683385428949201264045)
          ·
            refine ⟨8970256269535855950474017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23920683385428949201264045 8970256269535855950474017)
            ·
              refine ⟨6727692202151891962855513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8970256269535855950474017 6727692202151891962855513)
              ·
                refine ⟨5045769151613918972141635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727692202151891962855513 5045769151613918972141635)
                ·
                  refine ⟨7568653727420878458212453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5045769151613918972141635 7568653727420878458212453)
                  ·
                    refine ⟨1419122573891414710914835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7568653727420878458212453 1419122573891414710914835)
                    ·
                      rfl

theorem cell22_4145597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_4145597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145597 prefixEnd_4145597 := by exact prefixLift 4145597
  have htrace : WordTrace (prefixWord ++ tailWord_4145597) baseStart_4145597 baseEnd_4145597 := by
    simpa [prefixWord, tailWord_4145597, baseEnd_4145597] using wordTrace_append hprefix tailTrace_4145597
  have hstable : (prefixWord ++ tailWord_4145597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145597).length < 2 ^ (prefixWord ++ tailWord_4145597).sum := by decide
  have hdescent : baseEnd_4145597 < baseStart_4145597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145610 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 6, 3]
def baseStart_4145610 : Nat := 118140960795 + 4145610 * 2 ^ 59
def prefixEnd_4145610 : Nat := 4983230072969 + 3 ^ 40 * 4145610 * 2
def baseEnd_4145610 : Nat := 1419127024057087010339795

theorem tailTrace_4145610 : CollatzResearch.WordTrace tailWord_4145610 prefixEnd_4145610 1419127024057087010339795 := by
  unfold tailWord_4145610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37800704627792614666312571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100801879007446972443500189 37800704627792614666312571)
  ·
    refine ⟨56701056941688921999468857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37800704627792614666312571 56701056941688921999468857)
    ·
      refine ⟨42525792706266691499601643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56701056941688921999468857 42525792706266691499601643)
      ·
        refine ⟨63788689059400037249402465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42525792706266691499601643 63788689059400037249402465)
        ·
          refine ⟨47841516794550027937051849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63788689059400037249402465 47841516794550027937051849)
          ·
            refine ⟨35881137595912520952788887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47841516794550027937051849 35881137595912520952788887)
            ·
              refine ⟨53821706393868781429183331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35881137595912520952788887 53821706393868781429183331)
              ·
                refine ⟨80732559590803172143774997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53821706393868781429183331 80732559590803172143774997)
                ·
                  refine ⟨3784338730818898694239453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80732559590803172143774997 3784338730818898694239453)
                  ·
                    refine ⟨1419127024057087010339795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3784338730818898694239453 1419127024057087010339795)
                    ·
                      rfl

theorem cell22_4145610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_4145610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145610 prefixEnd_4145610 := by exact prefixLift 4145610
  have htrace : WordTrace (prefixWord ++ tailWord_4145610) baseStart_4145610 baseEnd_4145610 := by
    simpa [prefixWord, tailWord_4145610, baseEnd_4145610] using wordTrace_append hprefix tailTrace_4145610
  have hstable : (prefixWord ++ tailWord_4145610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145610).length < 2 ^ (prefixWord ++ tailWord_4145610).sum := by decide
  have hdescent : baseEnd_4145610 < baseStart_4145610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145625 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_4145625 : Nat := 118140960795 + 4145625 * 2 ^ 59
def prefixEnd_4145625 : Nat := 4983230072969 + 3 ^ 40 * 4145625 * 2
def baseEnd_4145625 : Nat := 1419132158863631971214749

theorem tailTrace_4145625 : CollatzResearch.WordTrace tailWord_4145625 prefixEnd_4145625 1419132158863631971214749 := by
  unfold tailWord_4145625
  simp only [CollatzResearch.WordTrace]
  refine ⟨151203365606116116227046329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100802243737410744151364219 151203365606116116227046329)
  ·
    refine ⟨113402524204587087170284747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151203365606116116227046329 113402524204587087170284747)
    ·
      refine ⟨170103786306880630755427121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113402524204587087170284747 170103786306880630755427121)
      ·
        refine ⟨127577839730160473066570341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170103786306880630755427121 127577839730160473066570341)
        ·
          refine ⟨23920844949405088699981939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127577839730160473066570341 23920844949405088699981939)
          ·
            refine ⟨35881267424107633049972909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23920844949405088699981939 35881267424107633049972909)
            ·
              refine ⟨13455475284040362393739841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35881267424107633049972909 13455475284040362393739841)
              ·
                refine ⟨10091606463030271795304881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13455475284040362393739841 10091606463030271795304881)
                ·
                  refine ⟨7568704847272703846478661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10091606463030271795304881 7568704847272703846478661)
                  ·
                    refine ⟨1419132158863631971214749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7568704847272703846478661 1419132158863631971214749)
                    ·
                      rfl

theorem cell22_4145625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_4145625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145625 prefixEnd_4145625 := by exact prefixLift 4145625
  have htrace : WordTrace (prefixWord ++ tailWord_4145625) baseStart_4145625 baseEnd_4145625 := by
    simpa [prefixWord, tailWord_4145625, baseEnd_4145625] using wordTrace_append hprefix tailTrace_4145625
  have hstable : (prefixWord ++ tailWord_4145625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145625).length < 2 ^ (prefixWord ++ tailWord_4145625).sum := by decide
  have hdescent : baseEnd_4145625 < baseStart_4145625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145629 : List Nat := [1, 4, 3, 1, 1, 1, 5, 2, 4]
def baseStart_4145629 : Nat := 118140960795 + 4145629 * 2 ^ 59
def prefixEnd_4145629 : Nat := 4983230072969 + 3 ^ 40 * 4145629 * 2
def baseEnd_4145629 : Nat := 473044509381792431371579

theorem tailTrace_4145629 : CollatzResearch.WordTrace tailWord_4145629 prefixEnd_4145629 473044509381792431371579 := by
  unfold tailWord_4145629
  simp only [CollatzResearch.WordTrace]
  refine ⟨151203511498101624910191941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100802340998734416606794627 151203511498101624910191941)
  ·
    refine ⟨28350658405894054670660989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151203511498101624910191941 28350658405894054670660989)
    ·
      refine ⟨10631496902210270501497871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28350658405894054670660989 10631496902210270501497871)
      ·
        refine ⟨15947245353315405752246807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10631496902210270501497871 15947245353315405752246807)
        ·
          refine ⟨23920868029973108628370211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15947245353315405752246807 23920868029973108628370211)
          ·
            refine ⟨35881302044959662942555317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23920868029973108628370211 35881302044959662942555317)
            ·
              refine ⟨3363872066714968400864561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35881302044959662942555317 3363872066714968400864561)
              ·
                refine ⟨2522904050036226300648421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363872066714968400864561 2522904050036226300648421)
                ·
                  refine ⟨473044509381792431371579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522904050036226300648421 473044509381792431371579)
                  ·
                    rfl

theorem cell22_4145629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_4145629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145629 prefixEnd_4145629 := by exact prefixLift 4145629
  have htrace : WordTrace (prefixWord ++ tailWord_4145629) baseStart_4145629 baseEnd_4145629 := by
    simpa [prefixWord, tailWord_4145629, baseEnd_4145629] using wordTrace_append hprefix tailTrace_4145629
  have hstable : (prefixWord ++ tailWord_4145629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145629).length < 2 ^ (prefixWord ++ tailWord_4145629).sum := by decide
  have hdescent : baseEnd_4145629 < baseStart_4145629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145640 : List Nat := [2, 1, 4, 1, 1, 4, 2, 7]
def baseStart_4145640 : Nat := 118140960795 + 4145640 * 2 ^ 59
def prefixEnd_4145640 : Nat := 4983230072969 + 3 ^ 40 * 4145640 * 2
def baseEnd_4145640 : Nat := 157681921518908548009967

theorem tailTrace_4145640 : CollatzResearch.WordTrace tailWord_4145640 prefixEnd_4145640 157681921518908548009967 := by
  unfold tailWord_4145640
  simp only [CollatzResearch.WordTrace]
  refine ⟨75601956350530886894421187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100802608467374515859228249 75601956350530886894421187)
  ·
    refine ⟨113402934525796330341631781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75601956350530886894421187 113402934525796330341631781)
    ·
      refine ⟨21263050223586811939055959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113402934525796330341631781 21263050223586811939055959)
      ·
        refine ⟨31894575335380217908583939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21263050223586811939055959 31894575335380217908583939)
        ·
          refine ⟨47841863003070326862875909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31894575335380217908583939 47841863003070326862875909)
          ·
            refine ⟨8970349313075686286789233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47841863003070326862875909 8970349313075686286789233)
            ·
              refine ⟨6727761984806764715091925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8970349313075686286789233 6727761984806764715091925)
              ·
                refine ⟨157681921518908548009967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6727761984806764715091925 157681921518908548009967)
                ·
                  rfl

theorem cell22_4145640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 7].length) (baseStart_4145640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145640 prefixEnd_4145640 := by exact prefixLift 4145640
  have htrace : WordTrace (prefixWord ++ tailWord_4145640) baseStart_4145640 baseEnd_4145640 := by
    simpa [prefixWord, tailWord_4145640, baseEnd_4145640] using wordTrace_append hprefix tailTrace_4145640
  have hstable : (prefixWord ++ tailWord_4145640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145640).length < 2 ^ (prefixWord ++ tailWord_4145640).sum := by decide
  have hdescent : baseEnd_4145640 < baseStart_4145640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145715 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 3, 4]
def baseStart_4145715 : Nat := 118140960795 + 4145715 * 2 ^ 59
def prefixEnd_4145715 : Nat := 4983230072969 + 3 ^ 40 * 4145715 * 2
def baseEnd_4145715 : Nat := 1419162967702901736464473

theorem tailTrace_4145715 : CollatzResearch.WordTrace tailWord_4145715 prefixEnd_4145715 1419162967702901736464473 := by
  unfold tailWord_4145715
  simp only [CollatzResearch.WordTrace]
  refine ⟨151206648175790061597822599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100804432117193374398548399 151206648175790061597822599)
  ·
    refine ⟨226809972263685092396733899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151206648175790061597822599 226809972263685092396733899)
    ·
      refine ⟨340214958395527638595100849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226809972263685092396733899 340214958395527638595100849)
      ·
        refine ⟨255161218796645728946325637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340214958395527638595100849 255161218796645728946325637)
        ·
          refine ⟨47842728524371074177436057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255161218796645728946325637 47842728524371074177436057)
          ·
            refine ⟨35882046393278305633077043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47842728524371074177436057 35882046393278305633077043)
            ·
              refine ⟨53823069589917458449615565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35882046393278305633077043 53823069589917458449615565)
              ·
                refine ⟨20183651096219046918605837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53823069589917458449615565 20183651096219046918605837)
                ·
                  refine ⟨7568869161082142594477189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20183651096219046918605837 7568869161082142594477189)
                  ·
                    refine ⟨1419162967702901736464473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7568869161082142594477189 1419162967702901736464473)
                    ·
                      rfl

theorem cell22_4145715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 4].length) (baseStart_4145715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145715 prefixEnd_4145715 := by exact prefixLift 4145715
  have htrace : WordTrace (prefixWord ++ tailWord_4145715) baseStart_4145715 baseEnd_4145715 := by
    simpa [prefixWord, tailWord_4145715, baseEnd_4145715] using wordTrace_append hprefix tailTrace_4145715
  have hstable : (prefixWord ++ tailWord_4145715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145715).length < 2 ^ (prefixWord ++ tailWord_4145715).sum := by decide
  have hdescent : baseEnd_4145715 < baseStart_4145715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145734 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_4145734 : Nat := 118140960795 + 4145734 * 2 ^ 59
def prefixEnd_4145734 : Nat := 4983230072969 + 3 ^ 40 * 4145734 * 2
def baseEnd_4145734 : Nat := 1419169471791192020239415

theorem tailTrace_4145734 : CollatzResearch.WordTrace tailWord_4145734 prefixEnd_4145734 1419169471791192020239415 := by
  unfold tailWord_4145734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725229411335038370086383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100804894108480818561842837 4725229411335038370086383)
  ·
    refine ⟨7087844117002557555129575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4725229411335038370086383 7087844117002557555129575)
    ·
      refine ⟨10631766175503836332694363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7087844117002557555129575 10631766175503836332694363)
      ·
        refine ⟨15947649263255754499041545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10631766175503836332694363 15947649263255754499041545)
        ·
          refine ⟨11960736947441815874281159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15947649263255754499041545 11960736947441815874281159)
          ·
            refine ⟨17941105421162723811421739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11960736947441815874281159 17941105421162723811421739)
            ·
              refine ⟨26911658131744085717132609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17941105421162723811421739 26911658131744085717132609)
              ·
                refine ⟨20183743598808064287849457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26911658131744085717132609 20183743598808064287849457)
                ·
                  refine ⟨15137807699106048215887093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20183743598808064287849457 15137807699106048215887093)
                  ·
                    refine ⟨1419169471791192020239415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15137807699106048215887093 1419169471791192020239415)
                    ·
                      rfl

theorem cell22_4145734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_4145734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145734 prefixEnd_4145734 := by exact prefixLift 4145734
  have htrace : WordTrace (prefixWord ++ tailWord_4145734) baseStart_4145734 baseEnd_4145734 := by
    simpa [prefixWord, tailWord_4145734, baseEnd_4145734] using wordTrace_append hprefix tailTrace_4145734
  have hstable : (prefixWord ++ tailWord_4145734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145734).length < 2 ^ (prefixWord ++ tailWord_4145734).sum := by decide
  have hdescent : baseEnd_4145734 < baseStart_4145734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145760 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_4145760 : Nat := 118140960795 + 4145760 * 2 ^ 59
def prefixEnd_4145760 : Nat := 4983230072969 + 3 ^ 40 * 4145760 * 2
def baseEnd_4145760 : Nat := 1419178372122536619089335

theorem tailTrace_4145760 : CollatzResearch.WordTrace tailWord_4145760 prefixEnd_4145760 1419178372122536619089335 := by
  unfold tailWord_4145760
  simp only [CollatzResearch.WordTrace]
  refine ⟨75604144730313517141605367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100805526307084689522140489 75604144730313517141605367)
  ·
    refine ⟨113406217095470275712408051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75604144730313517141605367 113406217095470275712408051)
    ·
      refine ⟨170109325643205413568612077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113406217095470275712408051 170109325643205413568612077)
      ·
        refine ⟨63790997116202030088229529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170109325643205413568612077 63790997116202030088229529)
        ·
          refine ⟨47843247837151522566172147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63790997116202030088229529 47843247837151522566172147)
          ·
            refine ⟨71764871755727283849258221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47843247837151522566172147 71764871755727283849258221)
            ·
              refine ⟨26911826908397731443471833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71764871755727283849258221 26911826908397731443471833)
              ·
                refine ⟨20183870181298298582603875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26911826908397731443471833 20183870181298298582603875)
                ·
                  refine ⟨30275805271947447873905813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20183870181298298582603875 30275805271947447873905813)
                  ·
                    refine ⟨1419178372122536619089335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30275805271947447873905813 1419178372122536619089335)
                    ·
                      rfl

theorem cell22_4145760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_4145760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145760 prefixEnd_4145760 := by exact prefixLift 4145760
  have htrace : WordTrace (prefixWord ++ tailWord_4145760) baseStart_4145760 baseEnd_4145760 := by
    simpa [prefixWord, tailWord_4145760, baseEnd_4145760] using wordTrace_append hprefix tailTrace_4145760
  have hstable : (prefixWord ++ tailWord_4145760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145760).length < 2 ^ (prefixWord ++ tailWord_4145760).sum := by decide
  have hdescent : baseEnd_4145760 < baseStart_4145760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145852 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_4145852 : Nat := 118140960795 + 4145852 * 2 ^ 59
def prefixEnd_4145852 : Nat := 4983230072969 + 3 ^ 40 * 4145852 * 2
def baseEnd_4145852 : Nat := 1419209865602679045789053

theorem tailTrace_4145852 : CollatzResearch.WordTrace tailWord_4145852 prefixEnd_4145852 1419209865602679045789053 := by
  unfold tailWord_4145852
  simp only [CollatzResearch.WordTrace]
  refine ⟨75605822488146866997779905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100807763317529155997039873 75605822488146866997779905)
  ·
    refine ⟨56704366866110150248334929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75605822488146866997779905 56704366866110150248334929)
    ·
      refine ⟨42528275149582612686251197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56704366866110150248334929 42528275149582612686251197)
      ·
        refine ⟨15948103181093479757344199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42528275149582612686251197 15948103181093479757344199)
        ·
          refine ⟨23922154771640219636016299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15948103181093479757344199 23922154771640219636016299)
          ·
            refine ⟨35883232157460329454024449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23922154771640219636016299 35883232157460329454024449)
            ·
              refine ⟨26912424118095247090518337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35883232157460329454024449 26912424118095247090518337)
              ·
                refine ⟨20184318088571435317888753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26912424118095247090518337 20184318088571435317888753)
                ·
                  refine ⟨15138238566428576488416565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20184318088571435317888753 15138238566428576488416565)
                  ·
                    refine ⟨1419209865602679045789053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15138238566428576488416565 1419209865602679045789053)
                    ·
                      rfl

theorem cell22_4145852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_4145852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145852 prefixEnd_4145852 := by exact prefixLift 4145852
  have htrace : WordTrace (prefixWord ++ tailWord_4145852) baseStart_4145852 baseEnd_4145852 := by
    simpa [prefixWord, tailWord_4145852, baseEnd_4145852] using wordTrace_append hprefix tailTrace_4145852
  have hstable : (prefixWord ++ tailWord_4145852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145852).length < 2 ^ (prefixWord ++ tailWord_4145852).sum := by decide
  have hdescent : baseEnd_4145852 < baseStart_4145852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145854 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_4145854 : Nat := 118140960795 + 4145854 * 2 ^ 59
def prefixEnd_4145854 : Nat := 4983230072969 + 3 ^ 40 * 4145854 * 2
def baseEnd_4145854 : Nat := 473070183414517235746349

theorem tailTrace_4145854 : CollatzResearch.WordTrace tailWord_4145854 prefixEnd_4145854 473070183414517235746349 := by
  unfold tailWord_4145854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18901464740285811042141577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100807811948190992224755077 18901464740285811042141577)
  ·
    refine ⟨14176098555214358281606183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18901464740285811042141577 14176098555214358281606183)
    ·
      refine ⟨21264147832821537422409275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14176098555214358281606183 21264147832821537422409275)
      ·
        refine ⟨31896221749232306133613913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21264147832821537422409275 31896221749232306133613913)
        ·
          refine ⟨23922166311924229600210435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31896221749232306133613913 23922166311924229600210435)
          ·
            refine ⟨35883249467886344400315653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23922166311924229600210435 35883249467886344400315653)
            ·
              refine ⟨6728109275228689575059185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35883249467886344400315653 6728109275228689575059185)
              ·
                refine ⟨5046081956421517181294389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6728109275228689575059185 5046081956421517181294389)
                ·
                  refine ⟨473070183414517235746349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5046081956421517181294389 473070183414517235746349)
                  ·
                    rfl

theorem cell22_4145854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_4145854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145854 prefixEnd_4145854 := by exact prefixLift 4145854
  have htrace : WordTrace (prefixWord ++ tailWord_4145854) baseStart_4145854 baseEnd_4145854 := by
    simpa [prefixWord, tailWord_4145854, baseEnd_4145854] using wordTrace_append hprefix tailTrace_4145854
  have hstable : (prefixWord ++ tailWord_4145854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145854).length < 2 ^ (prefixWord ++ tailWord_4145854).sum := by decide
  have hdescent : baseEnd_4145854 < baseStart_4145854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145865 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 12]
def baseStart_4145865 : Nat := 118140960795 + 4145865 * 2 ^ 59
def prefixEnd_4145865 : Nat := 4983230072969 + 3 ^ 40 * 4145865 * 2
def baseEnd_4145865 : Nat := 473071438589450448404671

theorem tailTrace_4145865 : CollatzResearch.WordTrace tailWord_4145865 prefixEnd_4145865 473071438589450448404671 := by
  unfold tailWord_4145865
  simp only [CollatzResearch.WordTrace]
  refine ⟨151212119125246637215783049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100808079416831091477188699 151212119125246637215783049)
  ·
    refine ⟨113409089343934977911837287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151212119125246637215783049 113409089343934977911837287)
    ·
      refine ⟨170113634015902466867755931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113409089343934977911837287 170113634015902466867755931)
      ·
        refine ⟨255170451023853700301633897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170113634015902466867755931 255170451023853700301633897)
        ·
          refine ⟨191377838267890275226225423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255170451023853700301633897 191377838267890275226225423)
          ·
            refine ⟨287066757401835412839338135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191377838267890275226225423 287066757401835412839338135)
            ·
              refine ⟨430600136102753119259007203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287066757401835412839338135 430600136102753119259007203)
              ·
                refine ⟨645900204154129678888510805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430600136102753119259007203 645900204154129678888510805)
                ·
                  refine ⟨473071438589450448404671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 645900204154129678888510805 473071438589450448404671)
                  ·
                    rfl

theorem cell22_4145865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_4145865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145865 prefixEnd_4145865 := by exact prefixLift 4145865
  have htrace : WordTrace (prefixWord ++ tailWord_4145865) baseStart_4145865 baseEnd_4145865 := by
    simpa [prefixWord, tailWord_4145865, baseEnd_4145865] using wordTrace_append hprefix tailTrace_4145865
  have hstable : (prefixWord ++ tailWord_4145865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145865).length < 2 ^ (prefixWord ++ tailWord_4145865).sum := by decide
  have hdescent : baseEnd_4145865 < baseStart_4145865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145882 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_4145882 : Nat := 118140960795 + 4145882 * 2 ^ 59
def prefixEnd_4145882 : Nat := 4983230072969 + 3 ^ 40 * 4145882 * 2
def baseEnd_4145882 : Nat := 473073378405256322512987

theorem tailTrace_4145882 : CollatzResearch.WordTrace tailWord_4145882 prefixEnd_4145882 473073378405256322512987 := by
  unfold tailWord_4145882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37803184791546262279787975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100808492777456699412767933 37803184791546262279787975)
  ·
    refine ⟨56704777187319393419681963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37803184791546262279787975 56704777187319393419681963)
    ·
      refine ⟨85057165780979090129522945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56704777187319393419681963 85057165780979090129522945)
      ·
        refine ⟨63792874335734317597142209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85057165780979090129522945 63792874335734317597142209)
        ·
          refine ⟨47844655751800738197856657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63792874335734317597142209 47844655751800738197856657)
          ·
            refine ⟨35883491813850553648392493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47844655751800738197856657 35883491813850553648392493)
            ·
              refine ⟨13456309430193957618147185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35883491813850553648392493 13456309430193957618147185)
              ·
                refine ⟨10092232072645468213610389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13456309430193957618147185 10092232072645468213610389)
                ·
                  refine ⟨473073378405256322512987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10092232072645468213610389 473073378405256322512987)
                  ·
                    rfl

theorem cell22_4145882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_4145882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145882 prefixEnd_4145882 := by exact prefixLift 4145882
  have htrace : WordTrace (prefixWord ++ tailWord_4145882) baseStart_4145882 baseEnd_4145882 := by
    simpa [prefixWord, tailWord_4145882, baseEnd_4145882] using wordTrace_append hprefix tailTrace_4145882
  have hstable : (prefixWord ++ tailWord_4145882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145882).length < 2 ^ (prefixWord ++ tailWord_4145882).sum := by decide
  have hdescent : baseEnd_4145882 < baseStart_4145882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145897 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_4145897 : Nat := 118140960795 + 4145897 * 2 ^ 59
def prefixEnd_4145897 : Nat := 4983230072969 + 3 ^ 40 * 4145897 * 2
def baseEnd_4145897 : Nat := 1419225270022313928413915

theorem tailTrace_4145897 : CollatzResearch.WordTrace tailWord_4145897 prefixEnd_4145897 1419225270022313928413915 := by
  unfold tailWord_4145897
  simp only [CollatzResearch.WordTrace]
  refine ⟨151213286261130706680947945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100808857507420471120631963 151213286261130706680947945)
  ·
    refine ⟨113409964695848030010710959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151213286261130706680947945 113409964695848030010710959)
    ·
      refine ⟨170114947043772045016066439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113409964695848030010710959 170114947043772045016066439)
      ·
        refine ⟨255172420565658067524099659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170114947043772045016066439 255172420565658067524099659)
        ·
          refine ⟨382758630848487101286149489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255172420565658067524099659 382758630848487101286149489)
          ·
            refine ⟨287068973136365325964612117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382758630848487101286149489 287068973136365325964612117)
            ·
              refine ⟨13456358115767124654591193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 287068973136365325964612117 13456358115767124654591193)
              ·
                refine ⟨10092268586825343490943395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13456358115767124654591193 10092268586825343490943395)
                ·
                  refine ⟨15138402880238015236415093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10092268586825343490943395 15138402880238015236415093)
                  ·
                    refine ⟨1419225270022313928413915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15138402880238015236415093 1419225270022313928413915)
                    ·
                      rfl

theorem cell22_4145897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_4145897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145897 prefixEnd_4145897 := by exact prefixLift 4145897
  have htrace : WordTrace (prefixWord ++ tailWord_4145897) baseStart_4145897 baseEnd_4145897 := by
    simpa [prefixWord, tailWord_4145897, baseEnd_4145897] using wordTrace_append hprefix tailTrace_4145897
  have hstable : (prefixWord ++ tailWord_4145897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145897).length < 2 ^ (prefixWord ++ tailWord_4145897).sum := by decide
  have hdescent : baseEnd_4145897 < baseStart_4145897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145912 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_4145912 : Nat := 118140960795 + 4145912 * 2 ^ 59
def prefixEnd_4145912 : Nat := 4983230072969 + 3 ^ 40 * 4145912 * 2
def baseEnd_4145912 : Nat := 1419230404828858889288869

theorem tailTrace_4145912 : CollatzResearch.WordTrace tailWord_4145912 prefixEnd_4145912 1419230404828858889288869 := by
  unfold tailWord_4145912
  simp only [CollatzResearch.WordTrace]
  refine ⟨75606916678038182121371995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100809222237384242828495993 75606916678038182121371995)
  ·
    refine ⟨113410375017057273182057993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75606916678038182121371995 113410375017057273182057993)
    ·
      refine ⟨85057781262792954886543495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113410375017057273182057993 85057781262792954886543495)
      ·
        refine ⟨127586671894189432329815243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85057781262792954886543495 127586671894189432329815243)
        ·
          refine ⟨191380007841284148494722865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127586671894189432329815243 191380007841284148494722865)
          ·
            refine ⟨143535005880963111371042149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191380007841284148494722865 143535005880963111371042149)
            ·
              refine ⟨26912813602680583382070403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143535005880963111371042149 26912813602680583382070403)
              ·
                refine ⟨40369220404020875073105605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26912813602680583382070403 40369220404020875073105605)
                ·
                  refine ⟨7569228825753914076207301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40369220404020875073105605 7569228825753914076207301)
                  ·
                    refine ⟨1419230404828858889288869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7569228825753914076207301 1419230404828858889288869)
                    ·
                      rfl

theorem cell22_4145912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_4145912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145912 prefixEnd_4145912 := by exact prefixLift 4145912
  have htrace : WordTrace (prefixWord ++ tailWord_4145912) baseStart_4145912 baseEnd_4145912 := by
    simpa [prefixWord, tailWord_4145912, baseEnd_4145912] using wordTrace_append hprefix tailTrace_4145912
  have hstable : (prefixWord ++ tailWord_4145912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145912).length < 2 ^ (prefixWord ++ tailWord_4145912).sum := by decide
  have hdescent : baseEnd_4145912 < baseStart_4145912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145982 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_4145982 : Nat := 118140960795 + 4145982 * 2 ^ 59
def prefixEnd_4145982 : Nat := 4983230072969 + 3 ^ 40 * 4145982 * 2
def baseEnd_4145982 : Nat := 1419254367259402040038655

theorem tailTrace_4145982 : CollatzResearch.WordTrace tailWord_4145982 prefixEnd_4145982 1419254367259402040038655 := by
  unfold tailWord_4145982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18902048308227845774724025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100810924310548510798528133 18902048308227845774724025)
  ·
    refine ⟨14176536231170884331043019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18902048308227845774724025 14176536231170884331043019)
    ·
      refine ⟨21264804346756326496564529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14176536231170884331043019 21264804346756326496564529)
      ·
        refine ⟨15948603260067244872423397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21264804346756326496564529 15948603260067244872423397)
        ·
          refine ⟨2990363111262608413579387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15948603260067244872423397 2990363111262608413579387)
          ·
            refine ⟨4485544666893912620369081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990363111262608413579387 4485544666893912620369081)
            ·
              refine ⟨3364158500170434465276811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4485544666893912620369081 3364158500170434465276811)
              ·
                refine ⟨5046237750255651697915217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364158500170434465276811 5046237750255651697915217)
                ·
                  refine ⟨3784678312691738773436413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5046237750255651697915217 3784678312691738773436413)
                  ·
                    refine ⟨1419254367259402040038655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3784678312691738773436413 1419254367259402040038655)
                    ·
                      rfl

theorem cell22_4145982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_4145982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145982 prefixEnd_4145982 := by exact prefixLift 4145982
  have htrace : WordTrace (prefixWord ++ tailWord_4145982) baseStart_4145982 baseEnd_4145982 := by
    simpa [prefixWord, tailWord_4145982, baseEnd_4145982] using wordTrace_append hprefix tailTrace_4145982
  have hstable : (prefixWord ++ tailWord_4145982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145982).length < 2 ^ (prefixWord ++ tailWord_4145982).sum := by decide
  have hdescent : baseEnd_4145982 < baseStart_4145982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145987 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 1, 7]
def baseStart_4145987 : Nat := 118140960795 + 4145987 * 2 ^ 59
def prefixEnd_4145987 : Nat := 4983230072969 + 3 ^ 40 * 4145987 * 2
def baseEnd_4145987 : Nat := 1419256078861583693663639

theorem tailTrace_4145987 : CollatzResearch.WordTrace tailWord_4145987 prefixEnd_4145987 1419256078861583693663639 := by
  unfold tailWord_4145987
  simp only [CollatzResearch.WordTrace]
  refine ⟨151216568830804652051724215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100811045887203101367816143 151216568830804652051724215)
  ·
    refine ⟨226824853246206978077586323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151216568830804652051724215 226824853246206978077586323)
    ·
      refine ⟨340237279869310467116379485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226824853246206978077586323 340237279869310467116379485)
      ·
        refine ⟨127588979950991425168642307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340237279869310467116379485 127588979950991425168642307)
        ·
          refine ⟨191383469926487137752963461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127588979950991425168642307 191383469926487137752963461)
          ·
            refine ⟨35884400611216338328680649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191383469926487137752963461 35884400611216338328680649)
            ·
              refine ⟨26913300458412253746510487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35884400611216338328680649 26913300458412253746510487)
              ·
                refine ⟨40369950687618380619765731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26913300458412253746510487 40369950687618380619765731)
                ·
                  refine ⟨60554926031427570929648597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40369950687618380619765731 60554926031427570929648597)
                  ·
                    refine ⟨1419256078861583693663639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60554926031427570929648597 1419256078861583693663639)
                    ·
                      rfl

theorem cell22_4145987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_4145987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145987 prefixEnd_4145987 := by exact prefixLift 4145987
  have htrace : WordTrace (prefixWord ++ tailWord_4145987) baseStart_4145987 baseEnd_4145987 := by
    simpa [prefixWord, tailWord_4145987, baseEnd_4145987] using wordTrace_append hprefix tailTrace_4145987
  have hstable : (prefixWord ++ tailWord_4145987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145987).length < 2 ^ (prefixWord ++ tailWord_4145987).sum := by decide
  have hdescent : baseEnd_4145987 < baseStart_4145987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146017 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 10]
def baseStart_4146017 : Nat := 118140960795 + 4146017 * 2 ^ 59
def prefixEnd_4146017 : Nat := 4983230072969 + 3 ^ 40 * 4146017 * 2
def baseEnd_4146017 : Nat := 473088782824891205137849

theorem tailTrace_4146017 : CollatzResearch.WordTrace tailWord_4146017 prefixEnd_4146017 473088782824891205137849 := by
  unfold tailWord_4146017
  simp only [CollatzResearch.WordTrace]
  refine ⟨151217663020695967175316305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100811775347130644783544203 151217663020695967175316305)
  ·
    refine ⟨113413247265521975381487229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151217663020695967175316305 113413247265521975381487229)
    ·
      refine ⟨42529967724570740768057711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113413247265521975381487229 42529967724570740768057711)
      ·
        refine ⟨63794951586856111152086567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42529967724570740768057711 63794951586856111152086567)
        ·
          refine ⟨95692427380284166728129851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63794951586856111152086567 95692427380284166728129851)
          ·
            refine ⟨143538641070426250092194777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95692427380284166728129851 143538641070426250092194777)
            ·
              refine ⟨107653980802819687569146083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143538641070426250092194777 107653980802819687569146083)
              ·
                refine ⟨161480971204229531353719125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107653980802819687569146083 161480971204229531353719125)
                ·
                  refine ⟨473088782824891205137849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 161480971204229531353719125 473088782824891205137849)
                  ·
                    rfl

theorem cell22_4146017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_4146017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146017 prefixEnd_4146017 := by exact prefixLift 4146017
  have htrace : WordTrace (prefixWord ++ tailWord_4146017) baseStart_4146017 baseEnd_4146017 := by
    simpa [prefixWord, tailWord_4146017, baseEnd_4146017] using wordTrace_append hprefix tailTrace_4146017
  have hstable : (prefixWord ++ tailWord_4146017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146017).length < 2 ^ (prefixWord ++ tailWord_4146017).sum := by decide
  have hdescent : baseEnd_4146017 < baseStart_4146017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146068 : List Nat := [2, 4, 2, 1, 1, 1, 4, 3, 4]
def baseStart_4146068 : Nat := 118140960795 + 4146068 * 2 ^ 59
def prefixEnd_4146068 : Nat := 4983230072969 + 3 ^ 40 * 4146068 * 2
def baseEnd_4146068 : Nat := 473094602272308827462797

theorem tailTrace_4146068 : CollatzResearch.WordTrace tailWord_4146068 prefixEnd_4146068 473094602272308827462797 := by
  unfold tailWord_4146068
  simp only [CollatzResearch.WordTrace]
  refine ⟨75609761571755601442711429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100813015429007468590281905 75609761571755601442711429)
  ·
    refine ⟨14176830294704175270508393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75609761571755601442711429 14176830294704175270508393)
    ·
      refine ⟨10632622721028131452881295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14176830294704175270508393 10632622721028131452881295)
      ·
        refine ⟨15948934081542197179321943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10632622721028131452881295 15948934081542197179321943)
        ·
          refine ⟨23923401122313295768982915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15948934081542197179321943 23923401122313295768982915)
          ·
            refine ⟨35885101683469943653474373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23923401122313295768982915 35885101683469943653474373)
            ·
              refine ⟨6728456565650614435026445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35885101683469943653474373 6728456565650614435026445)
              ·
                refine ⟨2523171212118980413134917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6728456565650614435026445 2523171212118980413134917)
                ·
                  refine ⟨473094602272308827462797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523171212118980413134917 473094602272308827462797)
                  ·
                    rfl

theorem cell22_4146068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_4146068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146068 prefixEnd_4146068 := by exact prefixLift 4146068
  have htrace : WordTrace (prefixWord ++ tailWord_4146068) baseStart_4146068 baseEnd_4146068 := by
    simpa [prefixWord, tailWord_4146068, baseEnd_4146068] using wordTrace_append hprefix tailTrace_4146068
  have hstable : (prefixWord ++ tailWord_4146068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146068).length < 2 ^ (prefixWord ++ tailWord_4146068).sum := by decide
  have hdescent : baseEnd_4146068 < baseStart_4146068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146079 : List Nat := [1, 1, 2, 5, 2, 2, 9]
def baseStart_4146079 : Nat := 118140960795 + 4146079 * 2 ^ 59
def prefixEnd_4146079 : Nat := 4983230072969 + 3 ^ 40 * 4146079 * 2
def baseEnd_4146079 : Nat := 52566206383026893346791

theorem tailTrace_4146079 : CollatzResearch.WordTrace tailWord_4146079 prefixEnd_4146079 52566206383026893346791 := by
  unfold tailWord_4146079
  simp only [CollatzResearch.WordTrace]
  refine ⟨151219924346471351764073291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100813282897647567842715527 151219924346471351764073291)
  ·
    refine ⟨226829886519707027646109937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151219924346471351764073291 226829886519707027646109937)
    ·
      refine ⟨170122414889780270734582453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226829886519707027646109937 170122414889780270734582453)
      ·
        refine ⟨15948976395916900381367105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170122414889780270734582453 15948976395916900381367105)
        ·
          refine ⟨11961732296937675286025329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15948976395916900381367105 11961732296937675286025329)
          ·
            refine ⟨8971299222703256464518997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11961732296937675286025329 8971299222703256464518997)
            ·
              refine ⟨52566206383026893346791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8971299222703256464518997 52566206383026893346791)
              ·
                rfl

theorem cell22_4146079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 9].length) (baseStart_4146079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146079 prefixEnd_4146079 := by exact prefixLift 4146079
  have htrace : WordTrace (prefixWord ++ tailWord_4146079) baseStart_4146079 baseEnd_4146079 := by
    simpa [prefixWord, tailWord_4146079, baseEnd_4146079] using wordTrace_append hprefix tailTrace_4146079
  have hstable : (prefixWord ++ tailWord_4146079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146079).length < 2 ^ (prefixWord ++ tailWord_4146079).sum := by decide
  have hdescent : baseEnd_4146079 < baseStart_4146079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146100 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4146100 : Nat := 118140960795 + 4146100 * 2 ^ 59
def prefixEnd_4146100 : Nat := 4983230072969 + 3 ^ 40 * 4146100 * 2
def baseEnd_4146100 : Nat := 1419294761070889065588293

theorem tailTrace_4146100 : CollatzResearch.WordTrace tailWord_4146100 prefixEnd_4146100 1419294761070889065588293 := by
  unfold tailWord_4146100
  simp only [CollatzResearch.WordTrace]
  refine ⟨75610345139697636175293877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100813793519596848233725169 75610345139697636175293877)
  ·
    refine ⟨7088469856846653391433801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75610345139697636175293877 7088469856846653391433801)
    ·
      refine ⟨5316352392634990043575351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7088469856846653391433801 5316352392634990043575351)
      ·
        refine ⟨7974528588952485065363027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316352392634990043575351 7974528588952485065363027)
        ·
          refine ⟨11961792883428727598044541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974528588952485065363027 11961792883428727598044541)
          ·
            refine ⟨4485672331285772849266703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11961792883428727598044541 4485672331285772849266703)
            ·
              refine ⟨6728508496928659273900055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4485672331285772849266703 6728508496928659273900055)
              ·
                refine ⟨10092762745392988910850083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728508496928659273900055 10092762745392988910850083)
                ·
                  refine ⟨15139144118089483366275125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10092762745392988910850083 15139144118089483366275125)
                  ·
                    refine ⟨1419294761070889065588293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15139144118089483366275125 1419294761070889065588293)
                    ·
                      rfl

theorem cell22_4146100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4146100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146100 prefixEnd_4146100 := by exact prefixLift 4146100
  have htrace : WordTrace (prefixWord ++ tailWord_4146100) baseStart_4146100 baseEnd_4146100 := by
    simpa [prefixWord, tailWord_4146100, baseEnd_4146100] using wordTrace_append hprefix tailTrace_4146100
  have hstable : (prefixWord ++ tailWord_4146100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146100).length < 2 ^ (prefixWord ++ tailWord_4146100).sum := by decide
  have hdescent : baseEnd_4146100 < baseStart_4146100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146124 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 9]
def baseStart_4146124 : Nat := 118140960795 + 4146124 * 2 ^ 59
def prefixEnd_4146124 : Nat := 4983230072969 + 3 ^ 40 * 4146124 * 2
def baseEnd_4146124 : Nat := 473100992253787000996073

theorem tailTrace_4146124 : CollatzResearch.WordTrace tailWord_4146124 prefixEnd_4146124 473100992253787000996073 := by
  unfold tailWord_4146124
  simp only [CollatzResearch.WordTrace]
  refine ⟨75610782815654162224730713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100814377087538882966307617 75610782815654162224730713)
  ·
    refine ⟨56708087111740621668548035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75610782815654162224730713 56708087111740621668548035)
    ·
      refine ⟨85062130667610932502822053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56708087111740621668548035 85062130667610932502822053)
      ·
        refine ⟨15949149500177049844279135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85062130667610932502822053 15949149500177049844279135)
        ·
          refine ⟨23923724250265574766418703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15949149500177049844279135 23923724250265574766418703)
          ·
            refine ⟨35885586375398362149628055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23923724250265574766418703 35885586375398362149628055)
            ·
              refine ⟨53828379563097543224442083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35885586375398362149628055 53828379563097543224442083)
              ·
                refine ⟨80742569344646314836663125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53828379563097543224442083 80742569344646314836663125)
                ·
                  refine ⟨473100992253787000996073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80742569344646314836663125 473100992253787000996073)
                  ·
                    rfl

theorem cell22_4146124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_4146124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146124 prefixEnd_4146124 := by exact prefixLift 4146124
  have htrace : WordTrace (prefixWord ++ tailWord_4146124) baseStart_4146124 baseEnd_4146124 := by
    simpa [prefixWord, tailWord_4146124, baseEnd_4146124] using wordTrace_append hprefix tailTrace_4146124
  have hstable : (prefixWord ++ tailWord_4146124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146124).length < 2 ^ (prefixWord ++ tailWord_4146124).sum := by decide
  have hdescent : baseEnd_4146124 < baseStart_4146124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146141 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 7]
def baseStart_4146141 : Nat := 118140960795 + 4146141 * 2 ^ 59
def prefixEnd_4146141 : Nat := 4983230072969 + 3 ^ 40 * 4146141 * 2
def baseEnd_4146141 : Nat := 473102932069592875104389

theorem tailTrace_4146141 : CollatzResearch.WordTrace tailWord_4146141 prefixEnd_4146141 473102932069592875104389 := by
  unfold tailWord_4146141
  simp only [CollatzResearch.WordTrace]
  refine ⟨151222185672246736352830277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100814790448164490901886851 151222185672246736352830277)
  ·
    refine ⟨28354159813546263066155677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151222185672246736352830277 28354159813546263066155677)
    ·
      refine ⟨10632809930079848649808379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28354159813546263066155677 10632809930079848649808379)
      ·
        refine ⟨15949214895119772974712569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10632809930079848649808379 15949214895119772974712569)
        ·
          refine ⟨11961911171339829731034427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15949214895119772974712569 11961911171339829731034427)
          ·
            refine ⟨17942866757009744596551641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11961911171339829731034427 17942866757009744596551641)
            ·
              refine ⟨13457150067757308447413731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17942866757009744596551641 13457150067757308447413731)
              ·
                refine ⟨20185725101635962671120597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13457150067757308447413731 20185725101635962671120597)
                ·
                  refine ⟨473102932069592875104389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20185725101635962671120597 473102932069592875104389)
                  ·
                    rfl

theorem cell22_4146141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_4146141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146141 prefixEnd_4146141 := by exact prefixLift 4146141
  have htrace : WordTrace (prefixWord ++ tailWord_4146141) baseStart_4146141 baseEnd_4146141 := by
    simpa [prefixWord, tailWord_4146141, baseEnd_4146141] using wordTrace_append hprefix tailTrace_4146141
  have hstable : (prefixWord ++ tailWord_4146141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146141).length < 2 ^ (prefixWord ++ tailWord_4146141).sum := by decide
  have hdescent : baseEnd_4146141 < baseStart_4146141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146158 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_4146158 : Nat := 118140960795 + 4146158 * 2 ^ 59
def prefixEnd_4146158 : Nat := 4983230072969 + 3 ^ 40 * 4146158 * 2
def baseEnd_4146158 : Nat := 473104871885398749212705

theorem tailTrace_4146158 : CollatzResearch.WordTrace tailWord_4146158 prefixEnd_4146158 473104871885398749212705 := by
  unfold tailWord_4146158
  simp only [CollatzResearch.WordTrace]
  refine ⟨18902850714148143532024891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100815203808790098837466085 18902850714148143532024891)
  ·
    refine ⟨28354276071222215298037337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18902850714148143532024891 28354276071222215298037337)
    ·
      refine ⟨21265707053416661473528003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28354276071222215298037337 21265707053416661473528003)
      ·
        refine ⟨31898560580124992210292005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21265707053416661473528003 31898560580124992210292005)
        ·
          refine ⟨5980980108773436039429751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31898560580124992210292005 5980980108773436039429751)
          ·
            refine ⟨8971470163160154059144627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5980980108773436039429751 8971470163160154059144627)
            ·
              refine ⟨13457205244740231088716941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8971470163160154059144627 13457205244740231088716941)
              ·
                refine ⟨5046451966777586658268853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13457205244740231088716941 5046451966777586658268853)
                ·
                  refine ⟨473104871885398749212705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5046451966777586658268853 473104871885398749212705)
                  ·
                    rfl

theorem cell22_4146158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_4146158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146158 prefixEnd_4146158 := by exact prefixLift 4146158
  have htrace : WordTrace (prefixWord ++ tailWord_4146158) baseStart_4146158 baseEnd_4146158 := by
    simpa [prefixWord, tailWord_4146158, baseEnd_4146158] using wordTrace_append hprefix tailTrace_4146158
  have hstable : (prefixWord ++ tailWord_4146158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146158).length < 2 ^ (prefixWord ++ tailWord_4146158).sum := by decide
  have hdescent : baseEnd_4146158 < baseStart_4146158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146169 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 8]
def baseStart_4146169 : Nat := 118140960795 + 4146169 * 2 ^ 59
def prefixEnd_4146169 : Nat := 4983230072969 + 3 ^ 40 * 4146169 * 2
def baseEnd_4146169 : Nat := 473106127060331961871027

theorem tailTrace_4146169 : CollatzResearch.WordTrace tailWord_4146169 prefixEnd_4146169 473106127060331961871027 := by
  unfold tailWord_4146169
  simp only [CollatzResearch.WordTrace]
  refine ⟨151223206916145297134849561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100815471277430198089899707 151223206916145297134849561)
  ·
    refine ⟨113417405187108972851137171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151223206916145297134849561 113417405187108972851137171)
    ·
      refine ⟨170126107780663459276705757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113417405187108972851137171 170126107780663459276705757)
      ·
        refine ⟨63797290417748797228764659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170126107780663459276705757 63797290417748797228764659)
        ·
          refine ⟨95695935626623195843146989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63797290417748797228764659 95695935626623195843146989)
          ·
            refine ⟨35885975859983698441180121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95695935626623195843146989 35885975859983698441180121)
            ·
              refine ⟨26914481894987773830885091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35885975859983698441180121 26914481894987773830885091)
              ·
                refine ⟨40371722842481660746327637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26914481894987773830885091 40371722842481660746327637)
                ·
                  refine ⟨473106127060331961871027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40371722842481660746327637 473106127060331961871027)
                  ·
                    rfl

theorem cell22_4146169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_4146169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146169 prefixEnd_4146169 := by exact prefixLift 4146169
  have htrace : WordTrace (prefixWord ++ tailWord_4146169) baseStart_4146169 baseEnd_4146169 := by
    simpa [prefixWord, tailWord_4146169, baseEnd_4146169] using wordTrace_append hprefix tailTrace_4146169
  have hstable : (prefixWord ++ tailWord_4146169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146169).length < 2 ^ (prefixWord ++ tailWord_4146169).sum := by decide
  have hdescent : baseEnd_4146169 < baseStart_4146169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146201 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 4, 3]
def baseStart_4146201 : Nat := 118140960795 + 4146201 * 2 ^ 59
def prefixEnd_4146201 : Nat := 4983230072969 + 3 ^ 40 * 4146201 * 2
def baseEnd_4146201 : Nat := 1419329335434958468812983

theorem tailTrace_4146201 : CollatzResearch.WordTrace tailWord_4146201 prefixEnd_4146201 1419329335434958468812983 := by
  unfold tailWord_4146201
  simp only [CollatzResearch.WordTrace]
  refine ⟨151224374052029366600014457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100816249368019577733342971 151224374052029366600014457)
  ·
    refine ⟨113418280539022024950010843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151224374052029366600014457 113418280539022024950010843)
    ·
      refine ⟨170127420808533037425016265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113418280539022024950010843 170127420808533037425016265)
      ·
        refine ⟨127595565606399778068762199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170127420808533037425016265 127595565606399778068762199)
        ·
          refine ⟨191393348409599667103143299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127595565606399778068762199 191393348409599667103143299)
          ·
            refine ⟨287090022614399500654714949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191393348409599667103143299 287090022614399500654714949)
            ·
              refine ⟨53829379240199906372759053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287090022614399500654714949 53829379240199906372759053)
              ·
                refine ⟨20186017215074964889784645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53829379240199906372759053 20186017215074964889784645)
                ·
                  refine ⟨3784878227826555916834621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20186017215074964889784645 3784878227826555916834621)
                  ·
                    refine ⟨1419329335434958468812983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3784878227826555916834621 1419329335434958468812983)
                    ·
                      rfl

theorem cell22_4146201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 3].length) (baseStart_4146201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146201 prefixEnd_4146201 := by exact prefixLift 4146201
  have htrace : WordTrace (prefixWord ++ tailWord_4146201) baseStart_4146201 baseEnd_4146201 := by
    simpa [prefixWord, tailWord_4146201, baseEnd_4146201] using wordTrace_append hprefix tailTrace_4146201
  have hstable : (prefixWord ++ tailWord_4146201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146201).length < 2 ^ (prefixWord ++ tailWord_4146201).sum := by decide
  have hdescent : baseEnd_4146201 < baseStart_4146201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146233 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 2, 4]
def baseStart_4146233 : Nat := 118140960795 + 4146233 * 2 ^ 59
def prefixEnd_4146233 : Nat := 4983230072969 + 3 ^ 40 * 4146233 * 2
def baseEnd_4146233 : Nat := 1419340289688921052012885

theorem tailTrace_4146233 : CollatzResearch.WordTrace tailWord_4146233 prefixEnd_4146233 1419340289688921052012885 := by
  unfold tailWord_4146233
  simp only [CollatzResearch.WordTrace]
  refine ⟨151225541187913436065179353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100817027458608957376786235 151225541187913436065179353)
  ·
    refine ⟨113419155890935077048884515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151225541187913436065179353 113419155890935077048884515)
    ·
      refine ⟨170128733836402615573326773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113419155890935077048884515 170128733836402615573326773)
      ·
        refine ⟨15949568797162745209999385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170128733836402615573326773 15949568797162745209999385)
        ·
          refine ⟨11962176597872058907499539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15949568797162745209999385 11962176597872058907499539)
          ·
            refine ⟨17943264896808088361249309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11962176597872058907499539 17943264896808088361249309)
            ·
              refine ⟨6728724336303033135468491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17943264896808088361249309 6728724336303033135468491)
              ·
                refine ⟨10093086504454549703202737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728724336303033135468491 10093086504454549703202737)
                ·
                  refine ⟨7569814878340912277402053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10093086504454549703202737 7569814878340912277402053)
                  ·
                    refine ⟨1419340289688921052012885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7569814878340912277402053 1419340289688921052012885)
                    ·
                      rfl

theorem cell22_4146233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_4146233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146233 prefixEnd_4146233 := by exact prefixLift 4146233
  have htrace : WordTrace (prefixWord ++ tailWord_4146233) baseStart_4146233 baseEnd_4146233 := by
    simpa [prefixWord, tailWord_4146233, baseEnd_4146233] using wordTrace_append hprefix tailTrace_4146233
  have hstable : (prefixWord ++ tailWord_4146233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146233).length < 2 ^ (prefixWord ++ tailWord_4146233).sum := by decide
  have hdescent : baseEnd_4146233 < baseStart_4146233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146269 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_4146269 : Nat := 118140960795 + 4146269 * 2 ^ 59
def prefixEnd_4146269 : Nat := 4983230072969 + 3 ^ 40 * 4146269 * 2
def baseEnd_4146269 : Nat := 1419352613224628958112775

theorem tailTrace_4146269 : CollatzResearch.WordTrace tailWord_4146269 prefixEnd_4146269 1419352613224628958112775 := by
  unfold tailWord_4146269
  simp only [CollatzResearch.WordTrace]
  refine ⟨151226854215783014213489861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100817902810522009475659907 151226854215783014213489861)
  ·
    refine ⟨28355035165459315165029349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151226854215783014213489861 28355035165459315165029349)
    ·
      refine ⟨5316569093523621593443003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28355035165459315165029349 5316569093523621593443003)
      ·
        refine ⟨7974853640285432390164505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316569093523621593443003 7974853640285432390164505)
        ·
          refine ⟨5981140230214074292623379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7974853640285432390164505 5981140230214074292623379)
          ·
            refine ⟨8971710345321111438935069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981140230214074292623379 8971710345321111438935069)
            ·
              refine ⟨3364391379495416789600651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8971710345321111438935069 3364391379495416789600651)
              ·
                refine ⟨5046587069243125184400977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364391379495416789600651 5046587069243125184400977)
                ·
                  refine ⟨3784940301932343888300733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5046587069243125184400977 3784940301932343888300733)
                  ·
                    refine ⟨1419352613224628958112775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3784940301932343888300733 1419352613224628958112775)
                    ·
                      rfl

theorem cell22_4146269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_4146269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146269 prefixEnd_4146269 := by exact prefixLift 4146269
  have htrace : WordTrace (prefixWord ++ tailWord_4146269) baseStart_4146269 baseEnd_4146269 := by
    simpa [prefixWord, tailWord_4146269, baseEnd_4146269] using wordTrace_append hprefix tailTrace_4146269
  have hstable : (prefixWord ++ tailWord_4146269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146269).length < 2 ^ (prefixWord ++ tailWord_4146269).sum := by decide
  have hdescent : baseEnd_4146269 < baseStart_4146269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146340 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_4146340 : Nat := 118140960795 + 4146340 * 2 ^ 59
def prefixEnd_4146340 : Nat := 4983230072969 + 3 ^ 40 * 4146340 * 2
def baseEnd_4146340 : Nat := 1419376917975608439587557

theorem tailTrace_4146340 : CollatzResearch.WordTrace tailWord_4146340 prefixEnd_4146340 1419376917975608439587557 := by
  unfold tailWord_4146340
  simp only [CollatzResearch.WordTrace]
  refine ⟨75614721899262896669662237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100819629199017195559549649 75614721899262896669662237)
  ·
    refine ⟨28355520712223586251123339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75614721899262896669662237 28355520712223586251123339)
    ·
      refine ⟨42533281068335379376685009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28355520712223586251123339 42533281068335379376685009)
      ·
        refine ⟨31899960801251534532513757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42533281068335379376685009 31899960801251534532513757)
        ·
          refine ⟨11962485300469325449692659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31899960801251534532513757 11962485300469325449692659)
          ·
            refine ⟨17943727950703988174538989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11962485300469325449692659 17943727950703988174538989)
            ·
              refine ⟨6728897981513995565452121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17943727950703988174538989 6728897981513995565452121)
              ·
                refine ⟨5046673486135496674089091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6728897981513995565452121 5046673486135496674089091)
                ·
                  refine ⟨7570010229203245011133637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046673486135496674089091 7570010229203245011133637)
                  ·
                    refine ⟨1419376917975608439587557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7570010229203245011133637 1419376917975608439587557)
                    ·
                      rfl

theorem cell22_4146340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_4146340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146340 prefixEnd_4146340 := by exact prefixLift 4146340
  have htrace : WordTrace (prefixWord ++ tailWord_4146340) baseStart_4146340 baseEnd_4146340 := by
    simpa [prefixWord, tailWord_4146340, baseEnd_4146340] using wordTrace_append hprefix tailTrace_4146340
  have hstable : (prefixWord ++ tailWord_4146340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146340).length < 2 ^ (prefixWord ++ tailWord_4146340).sum := by decide
  have hdescent : baseEnd_4146340 < baseStart_4146340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146351 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 1, 6]
def baseStart_4146351 : Nat := 118140960795 + 4146351 * 2 ^ 59
def prefixEnd_4146351 : Nat := 4983230072969 + 3 ^ 40 * 4146351 * 2
def baseEnd_4146351 : Nat := 1419380683500408077562523

theorem tailTrace_4146351 : CollatzResearch.WordTrace tailWord_4146351 prefixEnd_4146351 1419380683500408077562523 := by
  unfold tailWord_4146351
  simp only [CollatzResearch.WordTrace]
  refine ⟨151229845001485942217974907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100819896667657294811983271 151229845001485942217974907)
  ·
    refine ⟨226844767502228913326962361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151229845001485942217974907 226844767502228913326962361)
    ·
      refine ⟨170133575626671684995221771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226844767502228913326962361 170133575626671684995221771)
      ·
        refine ⟨255200363440007527492832657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170133575626671684995221771 255200363440007527492832657)
        ·
          refine ⟨191400272580005645619624493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255200363440007527492832657 191400272580005645619624493)
          ·
            refine ⟨71775102217502117107359185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191400272580005645619624493 71775102217502117107359185)
            ·
              refine ⟨53831326663126587830519389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71775102217502117107359185 53831326663126587830519389)
              ·
                refine ⟨20186747498672470436444771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53831326663126587830519389 20186747498672470436444771)
                ·
                  refine ⟨30280121248008705654667157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20186747498672470436444771 30280121248008705654667157)
                  ·
                    refine ⟨1419380683500408077562523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30280121248008705654667157 1419380683500408077562523)
                    ·
                      rfl

theorem cell22_4146351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_4146351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146351 prefixEnd_4146351 := by exact prefixLift 4146351
  have htrace : WordTrace (prefixWord ++ tailWord_4146351) baseStart_4146351 baseEnd_4146351 := by
    simpa [prefixWord, tailWord_4146351, baseEnd_4146351] using wordTrace_append hprefix tailTrace_4146351
  have hstable : (prefixWord ++ tailWord_4146351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146351).length < 2 ^ (prefixWord ++ tailWord_4146351).sum := by decide
  have hdescent : baseEnd_4146351 < baseStart_4146351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146353 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_4146353 : Nat := 118140960795 + 4146353 * 2 ^ 59
def prefixEnd_4146353 : Nat := 4983230072969 + 3 ^ 40 * 4146353 * 2
def baseEnd_4146353 : Nat := 1419381368141280739012517

theorem tailTrace_4146353 : CollatzResearch.WordTrace tailWord_4146353 prefixEnd_4146353 1419381368141280739012517 := by
  unfold tailWord_4146353
  simp only [CollatzResearch.WordTrace]
  refine ⟨151229917947478696559547713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100819945298319131039698475 151229917947478696559547713)
  ·
    refine ⟨113422438460609022419660785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151229917947478696559547713 113422438460609022419660785)
    ·
      refine ⟨85066828845456766814745589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113422438460609022419660785 85066828845456766814745589)
      ·
        refine ⟨7975015204261571888882399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85066828845456766814745589 7975015204261571888882399)
        ·
          refine ⟨11962522806392357833323599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7975015204261571888882399 11962522806392357833323599)
          ·
            refine ⟨17943784209588536749985399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11962522806392357833323599 17943784209588536749985399)
            ·
              refine ⟨26915676314382805124978099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17943784209588536749985399 26915676314382805124978099)
              ·
                refine ⟨40373514471574207687467149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26915676314382805124978099 40373514471574207687467149)
                ·
                  refine ⟨15140067926840327882800181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40373514471574207687467149 15140067926840327882800181)
                  ·
                    refine ⟨1419381368141280739012517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15140067926840327882800181 1419381368141280739012517)
                    ·
                      rfl

theorem cell22_4146353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_4146353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146353 prefixEnd_4146353 := by exact prefixLift 4146353
  have htrace : WordTrace (prefixWord ++ tailWord_4146353) baseStart_4146353 baseEnd_4146353 := by
    simpa [prefixWord, tailWord_4146353, baseEnd_4146353] using wordTrace_append hprefix tailTrace_4146353
  have hstable : (prefixWord ++ tailWord_4146353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146353).length < 2 ^ (prefixWord ++ tailWord_4146353).sum := by decide
  have hdescent : baseEnd_4146353 < baseStart_4146353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146372 : List Nat := [2, 3, 3, 1, 3, 1, 1, 4, 4]
def baseStart_4146372 : Nat := 118140960795 + 4146372 * 2 ^ 59
def prefixEnd_4146372 : Nat := 4983230072969 + 3 ^ 40 * 4146372 * 2
def baseEnd_4146372 : Nat := 473129290743190340929153

theorem tailTrace_4146372 : CollatzResearch.WordTrace tailWord_4146372 prefixEnd_4146372 473129290743190340929153 := by
  unfold tailWord_4146372
  simp only [CollatzResearch.WordTrace]
  refine ⟨75615305467204931402244685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100820407289606575202992913 75615305467204931402244685)
  ·
    refine ⟨28355739550201849275841757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75615305467204931402244685 28355739550201849275841757)
    ·
      refine ⟨10633402331325693478440659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28355739550201849275841757 10633402331325693478440659)
      ·
        refine ⟨15950103496988540217660989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10633402331325693478440659 15950103496988540217660989)
        ·
          refine ⟨5981288811370702581622871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15950103496988540217660989 5981288811370702581622871)
          ·
            refine ⟨8971933217056053872434307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981288811370702581622871 8971933217056053872434307)
            ·
              refine ⟨13457899825584080808651461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8971933217056053872434307 13457899825584080808651461)
              ·
                refine ⟨2523356217297015151622149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13457899825584080808651461 2523356217297015151622149)
                ·
                  refine ⟨473129290743190340929153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523356217297015151622149 473129290743190340929153)
                  ·
                    rfl

theorem cell22_4146372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_4146372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146372 prefixEnd_4146372 := by exact prefixLift 4146372
  have htrace : WordTrace (prefixWord ++ tailWord_4146372) baseStart_4146372 baseEnd_4146372 := by
    simpa [prefixWord, tailWord_4146372, baseEnd_4146372] using wordTrace_append hprefix tailTrace_4146372
  have hstable : (prefixWord ++ tailWord_4146372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146372).length < 2 ^ (prefixWord ++ tailWord_4146372).sum := by decide
  have hdescent : baseEnd_4146372 < baseStart_4146372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146443 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 2, 5]
def baseStart_4146443 : Nat := 118140960795 + 4146443 * 2 ^ 59
def prefixEnd_4146443 : Nat := 4983230072969 + 3 ^ 40 * 4146443 * 2
def baseEnd_4146443 : Nat := 1419412176980550504262241

theorem tailTrace_4146443 : CollatzResearch.WordTrace tailWord_4146443 prefixEnd_4146443 1419412176980550504262241 := by
  unfold tailWord_4146443
  simp only [CollatzResearch.WordTrace]
  refine ⟨151233200517152641930323983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100822133678101761286882655 151233200517152641930323983)
  ·
    refine ⟨226849800775728962895485975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151233200517152641930323983 226849800775728962895485975)
    ·
      refine ⟨340274701163593444343228963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226849800775728962895485975 340274701163593444343228963)
      ·
        refine ⟨510412051745390166514843445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340274701163593444343228963 510412051745390166514843445)
        ·
          refine ⟨47851129851130328110766573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 510412051745390166514843445 47851129851130328110766573)
          ·
            refine ⟨17944173694173873041537465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47851129851130328110766573 17944173694173873041537465)
            ·
              refine ⟨13458130270630404781153099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17944173694173873041537465 13458130270630404781153099)
              ·
                refine ⟨20187195405945607171729649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13458130270630404781153099 20187195405945607171729649)
                ·
                  refine ⟨15140396554459205378797237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20187195405945607171729649 15140396554459205378797237)
                  ·
                    refine ⟨1419412176980550504262241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15140396554459205378797237 1419412176980550504262241)
                    ·
                      rfl

theorem cell22_4146443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 5].length) (baseStart_4146443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146443 prefixEnd_4146443 := by exact prefixLift 4146443
  have htrace : WordTrace (prefixWord ++ tailWord_4146443) baseStart_4146443 baseEnd_4146443 := by
    simpa [prefixWord, tailWord_4146443, baseEnd_4146443] using wordTrace_append hprefix tailTrace_4146443
  have hstable : (prefixWord ++ tailWord_4146443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146443).length < 2 ^ (prefixWord ++ tailWord_4146443).sum := by decide
  have hdescent : baseEnd_4146443 < baseStart_4146443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146466 : List Nat := [3, 3, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_4146466 : Nat := 118140960795 + 4146466 * 2 ^ 59
def prefixEnd_4146466 : Nat := 4983230072969 + 3 ^ 40 * 4146466 * 2
def baseEnd_4146466 : Nat := 1419420050350586110937171

theorem tailTrace_4146466 : CollatzResearch.WordTrace tailWord_4146466 prefixEnd_4146466 1419420050350586110937171 := by
  unfold tailWord_4146466
  simp only [CollatzResearch.WordTrace]
  refine ⟨37808509849017329214602813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100822692930712877905607501 37808509849017329214602813)
  ·
    refine ⟨14178191193381498455476055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37808509849017329214602813 14178191193381498455476055)
    ·
      refine ⟨21267286790072247683214083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14178191193381498455476055 21267286790072247683214083)
      ·
        refine ⟨31900930185108371524821125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21267286790072247683214083 31900930185108371524821125)
        ·
          refine ⟨5981424409707819660903961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31900930185108371524821125 5981424409707819660903961)
          ·
            refine ⟨4486068307280864745677971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5981424409707819660903961 4486068307280864745677971)
            ·
              refine ⟨6729102460921297118516957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4486068307280864745677971 6729102460921297118516957)
              ·
                refine ⟨2523413422845486419443859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6729102460921297118516957 2523413422845486419443859)
                ·
                  refine ⟨3785120134268229629165789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523413422845486419443859 3785120134268229629165789)
                  ·
                    refine ⟨1419420050350586110937171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3785120134268229629165789 1419420050350586110937171)
                    ·
                      rfl

theorem cell22_4146466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_4146466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146466 prefixEnd_4146466 := by exact prefixLift 4146466
  have htrace : WordTrace (prefixWord ++ tailWord_4146466) baseStart_4146466 baseEnd_4146466 := by
    simpa [prefixWord, tailWord_4146466, baseEnd_4146466] using wordTrace_append hprefix tailTrace_4146466
  have hstable : (prefixWord ++ tailWord_4146466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146466).length < 2 ^ (prefixWord ++ tailWord_4146466).sum := by decide
  have hdescent : baseEnd_4146466 < baseStart_4146466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146509 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_4146509 : Nat := 118140960795 + 4146509 * 2 ^ 59
def prefixEnd_4146509 : Nat := 4983230072969 + 3 ^ 40 * 4146509 * 2
def baseEnd_4146509 : Nat := 1419434770129348332112039

theorem tailTrace_4146509 : CollatzResearch.WordTrace tailWord_4146509 prefixEnd_4146509 1419434770129348332112039 := by
  unfold tailWord_4146509
  simp only [CollatzResearch.WordTrace]
  refine ⟨151235607734913535202226581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100823738489942356801484387 151235607734913535202226581)
  ·
    refine ⟨7089169112574071962604371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151235607734913535202226581 7089169112574071962604371)
    ·
      refine ⟨10633753668861107943906557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7089169112574071962604371 10633753668861107943906557)
      ·
        refine ⟨3987657625822915478964959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10633753668861107943906557 3987657625822915478964959)
        ·
          refine ⟨5981486438734373218447439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3987657625822915478964959 5981486438734373218447439)
          ·
            refine ⟨8972229658101559827671159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981486438734373218447439 8972229658101559827671159)
            ·
              refine ⟨13458344487152339741506739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972229658101559827671159 13458344487152339741506739)
              ·
                refine ⟨20187516730728509612260109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13458344487152339741506739 20187516730728509612260109)
                ·
                  refine ⟨7570318774023191104597541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20187516730728509612260109 7570318774023191104597541)
                  ·
                    refine ⟨1419434770129348332112039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7570318774023191104597541 1419434770129348332112039)
                    ·
                      rfl

theorem cell22_4146509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_4146509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146509 prefixEnd_4146509 := by exact prefixLift 4146509
  have htrace : WordTrace (prefixWord ++ tailWord_4146509) baseStart_4146509 baseEnd_4146509 := by
    simpa [prefixWord, tailWord_4146509, baseEnd_4146509] using wordTrace_append hprefix tailTrace_4146509
  have hstable : (prefixWord ++ tailWord_4146509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146509).length < 2 ^ (prefixWord ++ tailWord_4146509).sum := by decide
  have hdescent : baseEnd_4146509 < baseStart_4146509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146520 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 2, 4]
def baseStart_4146520 : Nat := 118140960795 + 4146520 * 2 ^ 59
def prefixEnd_4146520 : Nat := 4983230072969 + 3 ^ 40 * 4146520 * 2
def baseEnd_4146520 : Nat := 1419438535654147970087005

theorem tailTrace_4146520 : CollatzResearch.WordTrace tailWord_4146520 prefixEnd_4146520 1419438535654147970087005 := by
  unfold tailWord_4146520
  simp only [CollatzResearch.WordTrace]
  refine ⟨75618004468936842040438507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100824005958582456053918009 75618004468936842040438507)
  ·
    refine ⟨113427006703405263060657761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75618004468936842040438507 113427006703405263060657761)
    ·
      refine ⟨85070255027553947295493321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113427006703405263060657761 85070255027553947295493321)
      ·
        refine ⟨63802691270665460471619991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85070255027553947295493321 63802691270665460471619991)
        ·
          refine ⟨95704036905998190707429987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63802691270665460471619991 95704036905998190707429987)
          ·
            refine ⟨143556055358997286061144981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95704036905998190707429987 143556055358997286061144981)
            ·
              refine ⟨6729190094952997784116171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143556055358997286061144981 6729190094952997784116171)
              ·
                refine ⟨10093785142429496676174257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729190094952997784116171 10093785142429496676174257)
                ·
                  refine ⟨7570338856822122507130693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10093785142429496676174257 7570338856822122507130693)
                  ·
                    refine ⟨1419438535654147970087005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7570338856822122507130693 1419438535654147970087005)
                    ·
                      rfl

theorem cell22_4146520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_4146520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146520 prefixEnd_4146520 := by exact prefixLift 4146520
  have htrace : WordTrace (prefixWord ++ tailWord_4146520) baseStart_4146520 baseEnd_4146520 := by
    simpa [prefixWord, tailWord_4146520, baseEnd_4146520] using wordTrace_append hprefix tailTrace_4146520
  have hstable : (prefixWord ++ tailWord_4146520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146520).length < 2 ^ (prefixWord ++ tailWord_4146520).sum := by decide
  have hdescent : baseEnd_4146520 < baseStart_4146520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146535 : List Nat := [1, 1, 5, 1, 5, 9]
def baseStart_4146535 : Nat := 118140960795 + 4146535 * 2 ^ 59
def prefixEnd_4146535 : Nat := 4983230072969 + 3 ^ 40 * 4146535 * 2
def baseEnd_4146535 : Nat := 17523995931613492974839

theorem tailTrace_4146535 : CollatzResearch.WordTrace tailWord_4146535 prefixEnd_4146535 17523995931613492974839 := by
  unfold tailWord_4146535
  simp only [CollatzResearch.WordTrace]
  refine ⟨151236556032819341642673059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100824370688546227761782039 151236556032819341642673059)
  ·
    refine ⟨226854834049229012464009589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151236556032819341642673059 226854834049229012464009589)
    ·
      refine ⟨21267640692115219918500899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226854834049229012464009589 21267640692115219918500899)
      ·
        refine ⟨31901461038172829877751349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21267640692115219918500899 31901461038172829877751349)
        ·
          refine ⟨2990761972328702801039189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31901461038172829877751349 2990761972328702801039189)
          ·
            refine ⟨17523995931613492974839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2990761972328702801039189 17523995931613492974839)
            ·
              rfl

theorem cell22_4146535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 9].length) (baseStart_4146535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146535 prefixEnd_4146535 := by exact prefixLift 4146535
  have htrace : WordTrace (prefixWord ++ tailWord_4146535) baseStart_4146535 baseEnd_4146535 := by
    simpa [prefixWord, tailWord_4146535, baseEnd_4146535] using wordTrace_append hprefix tailTrace_4146535
  have hstable : (prefixWord ++ tailWord_4146535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146535).length < 2 ^ (prefixWord ++ tailWord_4146535).sum := by decide
  have hdescent : baseEnd_4146535 < baseStart_4146535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146567 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 3, 3]
def baseStart_4146567 : Nat := 118140960795 + 4146567 * 2 ^ 59
def prefixEnd_4146567 : Nat := 4983230072969 + 3 ^ 40 * 4146567 * 2
def baseEnd_4146567 : Nat := 1419454624714655514161861

theorem tailTrace_4146567 : CollatzResearch.WordTrace tailWord_4146567 prefixEnd_4146567 1419454624714655514161861 := by
  unfold tailWord_4146567
  simp only [CollatzResearch.WordTrace]
  refine ⟨151237723168703411107837955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100825148779135607405225303 151237723168703411107837955)
  ·
    refine ⟨226856584753055116661756933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151237723168703411107837955 226856584753055116661756933)
    ·
      refine ⟨42535609641197834374079425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226856584753055116661756933 42535609641197834374079425)
      ·
        refine ⟨31901707230898375780559569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42535609641197834374079425 31901707230898375780559569)
        ·
          refine ⟨23926280423173781835419677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31901707230898375780559569 23926280423173781835419677)
          ·
            refine ⟨8972355158690168188282379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23926280423173781835419677 8972355158690168188282379)
            ·
              refine ⟨13458532738035252282423569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972355158690168188282379 13458532738035252282423569)
              ·
                refine ⟨10093899553526439211817677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13458532738035252282423569 10093899553526439211817677)
                ·
                  refine ⟨3785212332572414704431629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10093899553526439211817677 3785212332572414704431629)
                  ·
                    refine ⟨1419454624714655514161861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3785212332572414704431629 1419454624714655514161861)
                    ·
                      rfl

theorem cell22_4146567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_4146567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146567 prefixEnd_4146567 := by exact prefixLift 4146567
  have htrace : WordTrace (prefixWord ++ tailWord_4146567) baseStart_4146567 baseEnd_4146567 := by
    simpa [prefixWord, tailWord_4146567, baseEnd_4146567] using wordTrace_append hprefix tailTrace_4146567
  have hstable : (prefixWord ++ tailWord_4146567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146567).length < 2 ^ (prefixWord ++ tailWord_4146567).sum := by decide
  have hdescent : baseEnd_4146567 < baseStart_4146567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146610 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_4146610 : Nat := 118140960795 + 4146610 * 2 ^ 59
def prefixEnd_4146610 : Nat := 4983230072969 + 3 ^ 40 * 4146610 * 2
def baseEnd_4146610 : Nat := 1419469344493417735336729

theorem tailTrace_4146610 : CollatzResearch.WordTrace tailWord_4146610 prefixEnd_4146610 1419469344493417735336729 := by
  unfold tailWord_4146610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37809822876886907362913321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100826194338365086301102189 37809822876886907362913321)
  ·
    refine ⟨28357367157665180522184991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37809822876886907362913321 28357367157665180522184991)
    ·
      refine ⟨42536050736497770783277487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28357367157665180522184991 42536050736497770783277487)
      ·
        refine ⟨63804076104746656174916231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42536050736497770783277487 63804076104746656174916231)
        ·
          refine ⟨95706114157119984262374347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63804076104746656174916231 95706114157119984262374347)
          ·
            refine ⟨143559171235679976393561521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95706114157119984262374347 143559171235679976393561521)
            ·
              refine ⟨107669378426759982295171141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143559171235679976393561521 107669378426759982295171141)
              ·
                refine ⟨20188008455017496680344589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107669378426759982295171141 20188008455017496680344589)
                ·
                  refine ⟨7570503170631561255129221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20188008455017496680344589 7570503170631561255129221)
                  ·
                    refine ⟨1419469344493417735336729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7570503170631561255129221 1419469344493417735336729)
                    ·
                      rfl

theorem cell22_4146610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_4146610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146610 prefixEnd_4146610 := by exact prefixLift 4146610
  have htrace : WordTrace (prefixWord ++ tailWord_4146610) baseStart_4146610 baseEnd_4146610 := by
    simpa [prefixWord, tailWord_4146610, baseEnd_4146610] using wordTrace_append hprefix tailTrace_4146610
  have hstable : (prefixWord ++ tailWord_4146610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146610).length < 2 ^ (prefixWord ++ tailWord_4146610).sum := by decide
  have hdescent : baseEnd_4146610 < baseStart_4146610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146657 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 4, 3]
def baseStart_4146657 : Nat := 118140960795 + 4146657 * 2 ^ 59
def prefixEnd_4146657 : Nat := 4983230072969 + 3 ^ 40 * 4146657 * 2
def baseEnd_4146657 : Nat := 1419485433553925279411585

theorem tailTrace_4146657 : CollatzResearch.WordTrace tailWord_4146657 prefixEnd_4146657 1419485433553925279411585 := by
  unfold tailWord_4146657
  simp only [CollatzResearch.WordTrace]
  refine ⟨151241005738377356478614225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100827337158918237652409483 151241005738377356478614225)
  ·
    refine ⟨113430754303783017358960669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151241005738377356478614225 113430754303783017358960669)
    ·
      refine ⟨42536532863918631509610251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113430754303783017358960669 42536532863918631509610251)
      ·
        refine ⟨63804799295877947264415377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42536532863918631509610251 63804799295877947264415377)
        ·
          refine ⟨47853599471908460448311533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63804799295877947264415377 47853599471908460448311533)
          ·
            refine ⟨17945099801965672668116825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47853599471908460448311533 17945099801965672668116825)
            ·
              refine ⟨13458824851474254501087619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17945099801965672668116825 13458824851474254501087619)
              ·
                refine ⟨20188237277211381751631429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13458824851474254501087619 20188237277211381751631429)
                ·
                  refine ⟨3785294489477134078430893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20188237277211381751631429 3785294489477134078430893)
                  ·
                    refine ⟨1419485433553925279411585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3785294489477134078430893 1419485433553925279411585)
                    ·
                      rfl

theorem cell22_4146657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_4146657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146657 prefixEnd_4146657 := by exact prefixLift 4146657
  have htrace : WordTrace (prefixWord ++ tailWord_4146657) baseStart_4146657 baseEnd_4146657 := by
    simpa [prefixWord, tailWord_4146657, baseEnd_4146657] using wordTrace_append hprefix tailTrace_4146657
  have hstable : (prefixWord ++ tailWord_4146657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146657).length < 2 ^ (prefixWord ++ tailWord_4146657).sum := by decide
  have hdescent : baseEnd_4146657 < baseStart_4146657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146689 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 2, 4]
def baseStart_4146689 : Nat := 118140960795 + 4146689 * 2 ^ 59
def prefixEnd_4146689 : Nat := 4983230072969 + 3 ^ 40 * 4146689 * 2
def baseEnd_4146689 : Nat := 1419496387807887862611487

theorem tailTrace_4146689 : CollatzResearch.WordTrace tailWord_4146689 prefixEnd_4146689 1419496387807887862611487 := by
  unfold tailWord_4146689
  simp only [CollatzResearch.WordTrace]
  refine ⟨151242172874261425943779121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100828115249507617295852747 151242172874261425943779121)
  ·
    refine ⟨113431629655696069457834341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151242172874261425943779121 113431629655696069457834341)
    ·
      refine ⟨21268430560443013023343939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113431629655696069457834341 21268430560443013023343939)
      ·
        refine ⟨31902645840664519535015909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21268430560443013023343939 31902645840664519535015909)
        ·
          refine ⟨5981746095124597412815483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31902645840664519535015909 5981746095124597412815483)
          ·
            refine ⟨8972619142686896119223225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981746095124597412815483 8972619142686896119223225)
            ·
              refine ⟨6729464357015172089417419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8972619142686896119223225 6729464357015172089417419)
              ·
                refine ⟨10094196535522758134126129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729464357015172089417419 10094196535522758134126129)
                ·
                  refine ⟨7570647401642068600594597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10094196535522758134126129 7570647401642068600594597)
                  ·
                    refine ⟨1419496387807887862611487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7570647401642068600594597 1419496387807887862611487)
                    ·
                      rfl

theorem cell22_4146689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_4146689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146689 prefixEnd_4146689 := by exact prefixLift 4146689
  have htrace : WordTrace (prefixWord ++ tailWord_4146689) baseStart_4146689 baseEnd_4146689 := by
    simpa [prefixWord, tailWord_4146689, baseEnd_4146689] using wordTrace_append hprefix tailTrace_4146689
  have hstable : (prefixWord ++ tailWord_4146689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146689).length < 2 ^ (prefixWord ++ tailWord_4146689).sum := by decide
  have hdescent : baseEnd_4146689 < baseStart_4146689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146708 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_4146708 : Nat := 118140960795 + 4146708 * 2 ^ 59
def prefixEnd_4146708 : Nat := 4983230072969 + 3 ^ 40 * 4146708 * 2
def baseEnd_4146708 : Nat := 1419502891896178146386429

theorem tailTrace_4146708 : CollatzResearch.WordTrace tailWord_4146708 prefixEnd_4146708 1419502891896178146386429 := by
  unfold tailWord_4146708
  simp only [CollatzResearch.WordTrace]
  refine ⟨75621432930596296094360389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100828577240795061459147185 75621432930596296094360389)
  ·
    refine ⟨14179018674486805517692573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75621432930596296094360389 14179018674486805517692573)
    ·
      refine ⟨5317132002932552069134715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14179018674486805517692573 5317132002932552069134715)
      ·
        refine ⟨7975698004398828103702073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5317132002932552069134715 7975698004398828103702073)
        ·
          refine ⟨5981773503299121077776555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7975698004398828103702073 5981773503299121077776555)
          ·
            refine ⟨8972660254948681616664833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981773503299121077776555 8972660254948681616664833)
            ·
              refine ⟨6729495191211511212498625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8972660254948681616664833 6729495191211511212498625)
              ·
                refine ⟨5047121393408633409373969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6729495191211511212498625 5047121393408633409373969)
                ·
                  refine ⟨3785341045056475057030477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5047121393408633409373969 3785341045056475057030477)
                  ·
                    refine ⟨1419502891896178146386429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3785341045056475057030477 1419502891896178146386429)
                    ·
                      rfl

theorem cell22_4146708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_4146708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146708 prefixEnd_4146708 := by exact prefixLift 4146708
  have htrace : WordTrace (prefixWord ++ tailWord_4146708) baseStart_4146708 baseEnd_4146708 := by
    simpa [prefixWord, tailWord_4146708, baseEnd_4146708] using wordTrace_append hprefix tailTrace_4146708
  have hstable : (prefixWord ++ tailWord_4146708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146708).length < 2 ^ (prefixWord ++ tailWord_4146708).sum := by decide
  have hdescent : baseEnd_4146708 < baseStart_4146708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146807 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 2, 4]
def baseStart_4146807 : Nat := 118140960795 + 4146807 * 2 ^ 59
def prefixEnd_4146807 : Nat := 4983230072969 + 3 ^ 40 * 4146807 * 2
def baseEnd_4146807 : Nat := 1419536781619374888161125

theorem tailTrace_4146807 : CollatzResearch.WordTrace tailWord_4146807 prefixEnd_4146807 1419536781619374888161125 := by
  unfold tailWord_4146807
  simp only [CollatzResearch.WordTrace]
  refine ⟨151246476687833932096574675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100830984458555954731049783 151246476687833932096574675)
  ·
    refine ⟨226869715031750898144862013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151246476687833932096574675 226869715031750898144862013)
    ·
      refine ⟨85076143136906586804323255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226869715031750898144862013 85076143136906586804323255)
      ·
        refine ⟨127614214705359880206484883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85076143136906586804323255 127614214705359880206484883)
        ·
          refine ⟨191421322058039820309727325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127614214705359880206484883 191421322058039820309727325)
          ·
            refine ⟨71782995771764932616147747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191421322058039820309727325 71782995771764932616147747)
            ·
              refine ⟨107674493657647398924221621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71782995771764932616147747 107674493657647398924221621)
              ·
                refine ⟨10094483780404443649145777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107674493657647398924221621 10094483780404443649145777)
                ·
                  refine ⟨7570862835303332736859333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10094483780404443649145777 7570862835303332736859333)
                  ·
                    refine ⟨1419536781619374888161125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7570862835303332736859333 1419536781619374888161125)
                    ·
                      rfl

theorem cell22_4146807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_4146807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146807 prefixEnd_4146807 := by exact prefixLift 4146807
  have htrace : WordTrace (prefixWord ++ tailWord_4146807) baseStart_4146807 baseEnd_4146807 := by
    simpa [prefixWord, tailWord_4146807, baseEnd_4146807] using wordTrace_append hprefix tailTrace_4146807
  have hstable : (prefixWord ++ tailWord_4146807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146807).length < 2 ^ (prefixWord ++ tailWord_4146807).sum := by decide
  have hdescent : baseEnd_4146807 < baseStart_4146807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146912 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 8]
def baseStart_4146912 : Nat := 118140960795 + 4146912 * 2 ^ 59
def prefixEnd_4146912 : Nat := 4983230072969 + 3 ^ 40 * 4146912 * 2
def baseEnd_4146912 : Nat := 473190908421729871428601

theorem tailTrace_4146912 : CollatzResearch.WordTrace tailWord_4146912 prefixEnd_4146912 473190908421729871428601 := by
  unfold tailWord_4146912
  simp only [CollatzResearch.WordTrace]
  refine ⟨75625153176226767514573495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100833537568302356686097993 75625153176226767514573495)
  ·
    refine ⟨113437729764340151271860243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75625153176226767514573495 113437729764340151271860243)
    ·
      refine ⟨170156594646510226907790365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113437729764340151271860243 170156594646510226907790365)
      ·
        refine ⟨63808722992441335090421387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170156594646510226907790365 63808722992441335090421387)
        ·
          refine ⟨95713084488662002635632081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63808722992441335090421387 95713084488662002635632081)
          ·
            refine ⟨71784813366496501976724061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95713084488662002635632081 71784813366496501976724061)
            ·
              refine ⟨26919305012436188241271523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71784813366496501976724061 26919305012436188241271523)
              ·
                refine ⟨40378957518654282361907285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26919305012436188241271523 40378957518654282361907285)
                ·
                  refine ⟨473190908421729871428601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40378957518654282361907285 473190908421729871428601)
                  ·
                    rfl

theorem cell22_4146912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_4146912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146912 prefixEnd_4146912 := by exact prefixLift 4146912
  have htrace : WordTrace (prefixWord ++ tailWord_4146912) baseStart_4146912 baseEnd_4146912 := by
    simpa [prefixWord, tailWord_4146912, baseEnd_4146912] using wordTrace_append hprefix tailTrace_4146912
  have hstable : (prefixWord ++ tailWord_4146912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146912).length < 2 ^ (prefixWord ++ tailWord_4146912).sum := by decide
  have hdescent : baseEnd_4146912 < baseStart_4146912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146931 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 1, 4]
def baseStart_4146931 : Nat := 118140960795 + 4146931 * 2 ^ 59
def prefixEnd_4146931 : Nat := 4983230072969 + 3 ^ 40 * 4146931 * 2
def baseEnd_4146931 : Nat := 1419579229353479898060745

theorem tailTrace_4146931 : CollatzResearch.WordTrace tailWord_4146931 prefixEnd_4146931 1419579229353479898060745 := by
  unfold tailWord_4146931
  simp only [CollatzResearch.WordTrace]
  refine ⟨151250999339384701274088647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100833999559589800849392431 151250999339384701274088647)
  ·
    refine ⟨226876499009077051911132971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151250999339384701274088647 226876499009077051911132971)
    ·
      refine ⟨340314748513615577866699457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226876499009077051911132971 340314748513615577866699457)
      ·
        refine ⟨255236061385211683400024593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340314748513615577866699457 255236061385211683400024593)
        ·
          refine ⟨191427046038908762550018445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255236061385211683400024593 191427046038908762550018445)
          ·
            refine ⟨71785142264590785956256917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191427046038908762550018445 71785142264590785956256917)
            ·
              refine ⟨3364928543652693091699543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71785142264590785956256917 3364928543652693091699543)
              ·
                refine ⟨5047392815479039637549315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364928543652693091699543 5047392815479039637549315)
                ·
                  refine ⟨7571089223218559456323973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047392815479039637549315 7571089223218559456323973)
                  ·
                    refine ⟨1419579229353479898060745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7571089223218559456323973 1419579229353479898060745)
                    ·
                      rfl

theorem cell22_4146931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 4].length) (baseStart_4146931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146931 prefixEnd_4146931 := by exact prefixLift 4146931
  have htrace : WordTrace (prefixWord ++ tailWord_4146931) baseStart_4146931 baseEnd_4146931 := by
    simpa [prefixWord, tailWord_4146931, baseEnd_4146931] using wordTrace_append hprefix tailTrace_4146931
  have hstable : (prefixWord ++ tailWord_4146931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146931).length < 2 ^ (prefixWord ++ tailWord_4146931).sum := by decide
  have hdescent : baseEnd_4146931 < baseStart_4146931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146944 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 4, 3]
def baseStart_4146944 : Nat := 118140960795 + 4146944 * 2 ^ 59
def prefixEnd_4146944 : Nat := 4983230072969 + 3 ^ 40 * 4146944 * 2
def baseEnd_4146944 : Nat := 1419583679519152197485705

theorem tailTrace_4146944 : CollatzResearch.WordTrace tailWord_4146944 prefixEnd_4146944 1419583679519152197485705 := by
  unfold tailWord_4146944
  simp only [CollatzResearch.WordTrace]
  refine ⟨75625736744168802247155943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100834315658891736329541257 75625736744168802247155943)
  ·
    refine ⟨113438605116253203370733915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75625736744168802247155943 113438605116253203370733915)
    ·
      refine ⟨170157907674379805056100873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113438605116253203370733915 170157907674379805056100873)
      ·
        refine ⟨127618430755784853792075655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170157907674379805056100873 127618430755784853792075655)
        ·
          refine ⟨191427646133677280688113483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127618430755784853792075655 191427646133677280688113483)
          ·
            refine ⟨287141469200515921032170225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191427646133677280688113483 287141469200515921032170225)
            ·
              refine ⟨215356101900386940774127669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287141469200515921032170225 215356101900386940774127669)
              ·
                refine ⟨20189634553161275697574469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215356101900386940774127669 20189634553161275697574469)
                ·
                  refine ⟨3785556478717739193295213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20189634553161275697574469 3785556478717739193295213)
                  ·
                    refine ⟨1419583679519152197485705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3785556478717739193295213 1419583679519152197485705)
                    ·
                      rfl

theorem cell22_4146944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4, 3].length) (baseStart_4146944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146944 prefixEnd_4146944 := by exact prefixLift 4146944
  have htrace : WordTrace (prefixWord ++ tailWord_4146944) baseStart_4146944 baseEnd_4146944 := by
    simpa [prefixWord, tailWord_4146944, baseEnd_4146944] using wordTrace_append hprefix tailTrace_4146944
  have hstable : (prefixWord ++ tailWord_4146944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146944).length < 2 ^ (prefixWord ++ tailWord_4146944).sum := by decide
  have hdescent : baseEnd_4146944 < baseStart_4146944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146946 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_4146946 : Nat := 118140960795 + 4146946 * 2 ^ 59
def prefixEnd_4146946 : Nat := 4983230072969 + 3 ^ 40 * 4146946 * 2
def baseEnd_4146946 : Nat := 473194788053341619645233

theorem tailTrace_4146946 : CollatzResearch.WordTrace tailWord_4146946 prefixEnd_4146946 473194788053341619645233 := by
  unfold tailWord_4146946
  simp only [CollatzResearch.WordTrace]
  refine ⟨37812886608582589708971173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100834364289553572557256461 37812886608582589708971173)
  ·
    refine ⟨7089916239109235570432095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37812886608582589708971173 7089916239109235570432095)
    ·
      refine ⟨10634874358663853355648143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7089916239109235570432095 10634874358663853355648143)
      ·
        refine ⟨15952311537995780033472215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10634874358663853355648143 15952311537995780033472215)
        ·
          refine ⟨23928467306993670050208323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15952311537995780033472215 23928467306993670050208323)
          ·
            refine ⟨35892700960490505075312485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23928467306993670050208323 35892700960490505075312485)
            ·
              refine ⟨6729881430091969701621091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35892700960490505075312485 6729881430091969701621091)
              ·
                refine ⟨10094822145137954552431637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729881430091969701621091 10094822145137954552431637)
                ·
                  refine ⟨473194788053341619645233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10094822145137954552431637 473194788053341619645233)
                  ·
                    rfl

theorem cell22_4146946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_4146946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4146946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4146946 prefixEnd_4146946 := by exact prefixLift 4146946
  have htrace : WordTrace (prefixWord ++ tailWord_4146946) baseStart_4146946 baseEnd_4146946 := by
    simpa [prefixWord, tailWord_4146946, baseEnd_4146946] using wordTrace_append hprefix tailTrace_4146946
  have hstable : (prefixWord ++ tailWord_4146946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146946).length < 2 ^ (prefixWord ++ tailWord_4146946).sum := by decide
  have hdescent : baseEnd_4146946 < baseStart_4146946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147098 : List Nat := [3, 1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_4147098 : Nat := 118140960795 + 4147098 * 2 ^ 59
def prefixEnd_4147098 : Nat := 4983230072969 + 3 ^ 40 * 4147098 * 2
def baseEnd_4147098 : Nat := 473212132288782376378411

theorem tailTrace_4147098 : CollatzResearch.WordTrace tailWord_4147098 prefixEnd_4147098 473212132288782376378411 := by
  unfold tailWord_4147098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37814272582444922198854487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100838060219853125863611965 37814272582444922198854487)
  ·
    refine ⟨56721408873667383298281731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37814272582444922198854487 56721408873667383298281731)
    ·
      refine ⟨85082113310501074947422597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56721408873667383298281731 85082113310501074947422597)
      ·
        refine ⟨15952896245718951552641737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85082113310501074947422597 15952896245718951552641737)
        ·
          refine ⟨11964672184289213664481303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15952896245718951552641737 11964672184289213664481303)
          ·
            refine ⟨17947008276433820496721955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11964672184289213664481303 17947008276433820496721955)
            ·
              refine ⟨26920512414650730745082933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17947008276433820496721955 26920512414650730745082933)
              ·
                refine ⟨2523798038873506007351525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26920512414650730745082933 2523798038873506007351525)
                ·
                  refine ⟨473212132288782376378411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523798038873506007351525 473212132288782376378411)
                  ·
                    rfl

theorem cell22_4147098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_4147098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147098 prefixEnd_4147098 := by exact prefixLift 4147098
  have htrace : WordTrace (prefixWord ++ tailWord_4147098) baseStart_4147098 baseEnd_4147098 := by
    simpa [prefixWord, tailWord_4147098, baseEnd_4147098] using wordTrace_append hprefix tailTrace_4147098
  have hstable : (prefixWord ++ tailWord_4147098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147098).length < 2 ^ (prefixWord ++ tailWord_4147098).sum := by decide
  have hdescent : baseEnd_4147098 < baseStart_4147098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147100 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 1, 4]
def baseStart_4147100 : Nat := 118140960795 + 4147100 * 2 ^ 59
def prefixEnd_4147100 : Nat := 4983230072969 + 3 ^ 40 * 4147100 * 2
def baseEnd_4147100 : Nat := 1419637081507219790585227

theorem tailTrace_4147100 : CollatzResearch.WordTrace tailWord_4147100 prefixEnd_4147100 1419637081507219790585227 := by
  unfold tailWord_4147100
  simp only [CollatzResearch.WordTrace]
  refine ⟨75628581637886221568495377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100838108850514962091327169 75628581637886221568495377)
  ·
    refine ⟨56721436228414666176371533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75628581637886221568495377 56721436228414666176371533)
    ·
      refine ⟨21270538585655499816139325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56721436228414666176371533 21270538585655499816139325)
      ·
        refine ⟨7976451969620812431052247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21270538585655499816139325 7976451969620812431052247)
        ·
          refine ⟨11964677954431218646578371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7976451969620812431052247 11964677954431218646578371)
          ·
            refine ⟨17947016931646827969867557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11964677954431218646578371 17947016931646827969867557)
            ·
              refine ⟨3365065674683780244350167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17947016931646827969867557 3365065674683780244350167)
              ·
                refine ⟨5047598512025670366525251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365065674683780244350167 5047598512025670366525251)
                ·
                  refine ⟨7571397768038505549787877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047598512025670366525251 7571397768038505549787877)
                  ·
                    refine ⟨1419637081507219790585227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7571397768038505549787877 1419637081507219790585227)
                    ·
                      rfl

theorem cell22_4147100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_4147100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147100 prefixEnd_4147100 := by exact prefixLift 4147100
  have htrace : WordTrace (prefixWord ++ tailWord_4147100) baseStart_4147100 baseEnd_4147100 := by
    simpa [prefixWord, tailWord_4147100, baseEnd_4147100] using wordTrace_append hprefix tailTrace_4147100
  have hstable : (prefixWord ++ tailWord_4147100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147100).length < 2 ^ (prefixWord ++ tailWord_4147100).sum := by decide
  have hdescent : baseEnd_4147100 < baseStart_4147100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147141 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 5, 3]
def baseStart_4147141 : Nat := 118140960795 + 4147141 * 2 ^ 59
def prefixEnd_4147141 : Nat := 4983230072969 + 3 ^ 40 * 4147141 * 2
def baseEnd_4147141 : Nat := 1419651116645109350310101

theorem tailTrace_4147141 : CollatzResearch.WordTrace tailWord_4147141 prefixEnd_4147141 1419651116645109350310101 := by
  unfold tailWord_4147141
  simp only [CollatzResearch.WordTrace]
  refine ⟨151258658668623907139233277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100839105779082604759488851 151258658668623907139233277)
  ·
    refine ⟨56721997000733965177212479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151258658668623907139233277 56721997000733965177212479)
    ·
      refine ⟨85082995501100947765818719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56721997000733965177212479 85082995501100947765818719)
      ·
        refine ⟨127624493251651421648728079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85082995501100947765818719 127624493251651421648728079)
        ·
          refine ⟨191436739877477132473092119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127624493251651421648728079 191436739877477132473092119)
          ·
            refine ⟨287155109816215698709638179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191436739877477132473092119 287155109816215698709638179)
            ·
              refine ⟨430732664724323548064457269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287155109816215698709638179 430732664724323548064457269)
              ·
                refine ⟨40381187317905332631042869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 430732664724323548064457269 40381187317905332631042869)
                ·
                  refine ⟨3785736311053624934160269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40381187317905332631042869 3785736311053624934160269)
                  ·
                    refine ⟨1419651116645109350310101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3785736311053624934160269 1419651116645109350310101)
                    ·
                      rfl

theorem cell22_4147141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_4147141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147141 prefixEnd_4147141 := by exact prefixLift 4147141
  have htrace : WordTrace (prefixWord ++ tailWord_4147141) baseStart_4147141 baseEnd_4147141 := by
    simpa [prefixWord, tailWord_4147141, baseEnd_4147141] using wordTrace_append hprefix tailTrace_4147141
  have hstable : (prefixWord ++ tailWord_4147141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147141).length < 2 ^ (prefixWord ++ tailWord_4147141).sum := by decide
  have hdescent : baseEnd_4147141 < baseStart_4147141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147171 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 7]
def baseStart_4147171 : Nat := 118140960795 + 4147171 * 2 ^ 59
def prefixEnd_4147171 : Nat := 4983230072969 + 3 ^ 40 * 4147171 * 2
def baseEnd_4147171 : Nat := 473220462086066424020003

theorem tailTrace_4147171 : CollatzResearch.WordTrace tailWord_4147171 prefixEnd_4147171 473220462086066424020003 := by
  unfold tailWord_4147171
  simp only [CollatzResearch.WordTrace]
  refine ⟨151259752858515222262825367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100839835239010148175216911 151259752858515222262825367)
  ·
    refine ⟨226889629287772833394238051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151259752858515222262825367 226889629287772833394238051)
    ·
      refine ⟨340334443931659250091357077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226889629287772833394238051 340334443931659250091357077)
      ·
        refine ⟨15953177059296527348032363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 340334443931659250091357077 15953177059296527348032363)
        ·
          refine ⟨23929765588944791022048545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15953177059296527348032363 23929765588944791022048545)
          ·
            refine ⟨17947324191708593266536409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23929765588944791022048545 17947324191708593266536409)
            ·
              refine ⟨13460493143781444949902307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17947324191708593266536409 13460493143781444949902307)
              ·
                refine ⟨20190739715672167424853461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13460493143781444949902307 20190739715672167424853461)
                ·
                  refine ⟨473220462086066424020003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20190739715672167424853461 473220462086066424020003)
                  ·
                    rfl

theorem cell22_4147171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 7].length) (baseStart_4147171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147171 prefixEnd_4147171 := by exact prefixLift 4147171
  have htrace : WordTrace (prefixWord ++ tailWord_4147171) baseStart_4147171 baseEnd_4147171 := by
    simpa [prefixWord, tailWord_4147171, baseEnd_4147171] using wordTrace_append hprefix tailTrace_4147171
  have hstable : (prefixWord ++ tailWord_4147171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147171).length < 2 ^ (prefixWord ++ tailWord_4147171).sum := by decide
  have hdescent : baseEnd_4147171 < baseStart_4147171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147181 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_4147181 : Nat := 118140960795 + 4147181 * 2 ^ 59
def prefixEnd_4147181 : Nat := 4983230072969 + 3 ^ 40 * 4147181 * 2
def baseEnd_4147181 : Nat := 1419664809462562579309979

theorem tailTrace_4147181 : CollatzResearch.WordTrace tailWord_4147181 prefixEnd_4147181 1419664809462562579309979 := by
  unfold tailWord_4147181
  simp only [CollatzResearch.WordTrace]
  refine ⟨151260117588478993970689397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100840078392319329313792931 151260117588478993970689397)
  ·
    refine ⟨14180636023919905684752131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151260117588478993970689397 14180636023919905684752131)
    ·
      refine ⟨21270954035879858527128197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14180636023919905684752131 21270954035879858527128197)
      ·
        refine ⟨3988303881727473473836537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21270954035879858527128197 3988303881727473473836537)
        ·
          refine ⟨2991227911295605105377403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3988303881727473473836537 2991227911295605105377403)
          ·
            refine ⟨4486841866943407658066105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991227911295605105377403 4486841866943407658066105)
            ·
              refine ⟨3365131400207555743549579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4486841866943407658066105 3365131400207555743549579)
              ·
                refine ⟨5047697100311333615324369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365131400207555743549579 5047697100311333615324369)
                ·
                  refine ⟨3785772825233500211493277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5047697100311333615324369 3785772825233500211493277)
                  ·
                    refine ⟨1419664809462562579309979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3785772825233500211493277 1419664809462562579309979)
                    ·
                      rfl

theorem cell22_4147181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_4147181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147181 prefixEnd_4147181 := by exact prefixLift 4147181
  have htrace : WordTrace (prefixWord ++ tailWord_4147181) baseStart_4147181 baseEnd_4147181 := by
    simpa [prefixWord, tailWord_4147181, baseEnd_4147181] using wordTrace_append hprefix tailTrace_4147181
  have hstable : (prefixWord ++ tailWord_4147181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147181).length < 2 ^ (prefixWord ++ tailWord_4147181).sum := by decide
  have hdescent : baseEnd_4147181 < baseStart_4147181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147231 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 3, 5]
def baseStart_4147231 : Nat := 118140960795 + 4147231 * 2 ^ 59
def prefixEnd_4147231 : Nat := 4983230072969 + 3 ^ 40 * 4147231 * 2
def baseEnd_4147231 : Nat := 1419681925484379115559825

theorem tailTrace_4147231 : CollatzResearch.WordTrace tailWord_4147231 prefixEnd_4147231 1419681925484379115559825 := by
  unfold tailWord_4147231
  simp only [CollatzResearch.WordTrace]
  refine ⟨151261941238297852510009547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100841294158865235006673031 151261941238297852510009547)
  ·
    refine ⟨226892911857446778765014321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151261941238297852510009547 226892911857446778765014321)
    ·
      refine ⟨170169683893085084073760741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226892911857446778765014321 170169683893085084073760741)
      ·
        refine ⟨31906815729953453263830139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170169683893085084073760741 31906815729953453263830139)
        ·
          refine ⟨47860223594930179895745209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31906815729953453263830139 47860223594930179895745209)
          ·
            refine ⟨35895167696197634921808907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47860223594930179895745209 35895167696197634921808907)
            ·
              refine ⟨53842751544296452382713361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35895167696197634921808907 53842751544296452382713361)
              ·
                refine ⟨40382063658222339287035021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53842751544296452382713361 40382063658222339287035021)
                ·
                  refine ⟨15143273871833377232638133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40382063658222339287035021 15143273871833377232638133)
                  ·
                    refine ⟨1419681925484379115559825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15143273871833377232638133 1419681925484379115559825)
                    ·
                      rfl

theorem cell22_4147231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_4147231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147231 prefixEnd_4147231 := by exact prefixLift 4147231
  have htrace : WordTrace (prefixWord ++ tailWord_4147231) baseStart_4147231 baseEnd_4147231 := by
    simpa [prefixWord, tailWord_4147231, baseEnd_4147231] using wordTrace_append hprefix tailTrace_4147231
  have hstable : (prefixWord ++ tailWord_4147231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147231).length < 2 ^ (prefixWord ++ tailWord_4147231).sum := by decide
  have hdescent : baseEnd_4147231 < baseStart_4147231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147248 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 1, 5]
def baseStart_4147248 : Nat := 118140960795 + 4147248 * 2 ^ 59
def prefixEnd_4147248 : Nat := 4983230072969 + 3 ^ 40 * 4147248 * 2
def baseEnd_4147248 : Nat := 1419687744931796737884773

theorem tailTrace_4147248 : CollatzResearch.WordTrace tailWord_4147248 prefixEnd_4147248 1419687744931796737884773 := by
  unfold tailWord_4147248
  simp only [CollatzResearch.WordTrace]
  refine ⟨75631280639618132206689199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100841707519490842942252265 75631280639618132206689199)
  ·
    refine ⟨113446920959427198310033799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75631280639618132206689199 113446920959427198310033799)
    ·
      refine ⟨170170381439140797465050699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113446920959427198310033799 170170381439140797465050699)
      ·
        refine ⟨255255572158711196197576049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170170381439140797465050699 255255572158711196197576049)
        ·
          refine ⟨191441679119033397148182037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255255572158711196197576049 191441679119033397148182037)
          ·
            refine ⟨8973828708704690491321033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191441679119033397148182037 8973828708704690491321033)
            ·
              refine ⟨6730371531528517868490775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973828708704690491321033 6730371531528517868490775)
              ·
                refine ⟨10095557297292776802736163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730371531528517868490775 10095557297292776802736163)
                ·
                  refine ⟨15143335945939165204104245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10095557297292776802736163 15143335945939165204104245)
                  ·
                    refine ⟨1419687744931796737884773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15143335945939165204104245 1419687744931796737884773)
                    ·
                      rfl

theorem cell22_4147248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_4147248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147248 prefixEnd_4147248 := by exact prefixLift 4147248
  have htrace : WordTrace (prefixWord ++ tailWord_4147248) baseStart_4147248 baseEnd_4147248 := by
    simpa [prefixWord, tailWord_4147248, baseEnd_4147248] using wordTrace_append hprefix tailTrace_4147248
  have hstable : (prefixWord ++ tailWord_4147248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147248).length < 2 ^ (prefixWord ++ tailWord_4147248).sum := by decide
  have hdescent : baseEnd_4147248 < baseStart_4147248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147263 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 2, 4]
def baseStart_4147263 : Nat := 118140960795 + 4147263 * 2 ^ 59
def prefixEnd_4147263 : Nat := 4983230072969 + 3 ^ 40 * 4147263 * 2
def baseEnd_4147263 : Nat := 1419692879738341698759727

theorem tailTrace_4147263 : CollatzResearch.WordTrace tailWord_4147263 prefixEnd_4147263 1419692879738341698759727 := by
  unfold tailWord_4147263
  simp only [CollatzResearch.WordTrace]
  refine ⟨151263108374181921975174443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100842072249454614650116295 151263108374181921975174443)
  ·
    refine ⟨226894662561272882962761665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151263108374181921975174443 226894662561272882962761665)
    ·
      refine ⟨170170996920954662222071249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226894662561272882962761665 170170996920954662222071249)
      ·
        refine ⟨127628247690715996666553437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170170996920954662222071249 127628247690715996666553437)
        ·
          refine ⟨47860592884018498749957539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127628247690715996666553437 47860592884018498749957539)
          ·
            refine ⟨71790889326027748124936309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47860592884018498749957539 71790889326027748124936309)
            ·
              refine ⟨6730395874315101386712779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71790889326027748124936309 6730395874315101386712779)
              ·
                refine ⟨10095593811472652080069169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730395874315101386712779 10095593811472652080069169)
                ·
                  refine ⟨7571695358604489060051877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10095593811472652080069169 7571695358604489060051877)
                  ·
                    refine ⟨1419692879738341698759727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7571695358604489060051877 1419692879738341698759727)
                    ·
                      rfl

theorem cell22_4147263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_4147263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147263 prefixEnd_4147263 := by exact prefixLift 4147263
  have htrace : WordTrace (prefixWord ++ tailWord_4147263) baseStart_4147263 baseEnd_4147263 := by
    simpa [prefixWord, tailWord_4147263, baseEnd_4147263] using wordTrace_append hprefix tailTrace_4147263
  have hstable : (prefixWord ++ tailWord_4147263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147263).length < 2 ^ (prefixWord ++ tailWord_4147263).sum := by decide
  have hdescent : baseEnd_4147263 < baseStart_4147263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147310 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_4147310 : Nat := 118140960795 + 4147310 * 2 ^ 59
def prefixEnd_4147310 : Nat := 4983230072969 + 3 ^ 40 * 4147310 * 2
def baseEnd_4147310 : Nat := 1419708968798849242834583

theorem tailTrace_4147310 : CollatzResearch.WordTrace tailWord_4147310 prefixEnd_4147310 1419708968798849242834583 := by
  unfold tailWord_4147310
  simp only [CollatzResearch.WordTrace]
  refine ⟨18908102825626456125266923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100843215070007766001423589 18908102825626456125266923)
  ·
    refine ⟨28362154238439684187900385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18908102825626456125266923 28362154238439684187900385)
    ·
      refine ⟨21271615678829763140925289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28362154238439684187900385 21271615678829763140925289)
      ·
        refine ⟨15953711759122322355693967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21271615678829763140925289 15953711759122322355693967)
        ·
          refine ⟨23930567638683483533540951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15953711759122322355693967 23930567638683483533540951)
          ·
            refine ⟨35895851458025225300311427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23930567638683483533540951 35895851458025225300311427)
            ·
              refine ⟨53843777187037837950467141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35895851458025225300311427 53843777187037837950467141)
              ·
                refine ⟨10095708222569594615712589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53843777187037837950467141 10095708222569594615712589)
                ·
                  refine ⟨3785890583463597980892221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10095708222569594615712589 3785890583463597980892221)
                  ·
                    refine ⟨1419708968798849242834583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3785890583463597980892221 1419708968798849242834583)
                    ·
                      rfl

theorem cell22_4147310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_4147310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147310 prefixEnd_4147310 := by exact prefixLift 4147310
  have htrace : WordTrace (prefixWord ++ tailWord_4147310) baseStart_4147310 baseEnd_4147310 := by
    simpa [prefixWord, tailWord_4147310, baseEnd_4147310] using wordTrace_append hprefix tailTrace_4147310
  have hstable : (prefixWord ++ tailWord_4147310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147310).length < 2 ^ (prefixWord ++ tailWord_4147310).sum := by decide
  have hdescent : baseEnd_4147310 < baseStart_4147310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147357 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 5]
def baseStart_4147357 : Nat := 118140960795 + 4147357 * 2 ^ 59
def prefixEnd_4147357 : Nat := 4983230072969 + 3 ^ 40 * 4147357 * 2
def baseEnd_4147357 : Nat := 473241685953118928969813

theorem tailTrace_4147357 : CollatzResearch.WordTrace tailWord_4147357 prefixEnd_4147357 473241685953118928969813 := by
  unfold tailWord_4147357
  simp only [CollatzResearch.WordTrace]
  refine ⟨151266536835841376029096325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100844357890560917352730883 151266536835841376029096325)
  ·
    refine ⟨28362475656720258005455561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151266536835841376029096325 28362475656720258005455561)
    ·
      refine ⟨21271856742540193504091671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28362475656720258005455561 21271856742540193504091671)
      ·
        refine ⟨31907785113810290256137507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21271856742540193504091671 31907785113810290256137507)
        ·
          refine ⟨47861677670715435384206261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31907785113810290256137507 47861677670715435384206261)
          ·
            refine ⟨4487032281629572067269337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47861677670715435384206261 4487032281629572067269337)
            ·
              refine ⟨3365274211222179050452003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4487032281629572067269337 3365274211222179050452003)
              ·
                refine ⟨5047911316833268575678005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365274211222179050452003 5047911316833268575678005)
                ·
                  refine ⟨473241685953118928969813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5047911316833268575678005 473241685953118928969813)
                  ·
                    rfl

theorem cell22_4147357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_4147357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147357 prefixEnd_4147357 := by exact prefixLift 4147357
  have htrace : WordTrace (prefixWord ++ tailWord_4147357) baseStart_4147357 baseEnd_4147357 := by
    simpa [prefixWord, tailWord_4147357, baseEnd_4147357] using wordTrace_append hprefix tailTrace_4147357
  have hstable : (prefixWord ++ tailWord_4147357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147357).length < 2 ^ (prefixWord ++ tailWord_4147357).sum := by decide
  have hdescent : baseEnd_4147357 < baseStart_4147357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147383 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 3, 5]
def baseStart_4147383 : Nat := 118140960795 + 4147383 * 2 ^ 59
def prefixEnd_4147383 : Nat := 4983230072969 + 3 ^ 40 * 4147383 * 2
def baseEnd_4147383 : Nat := 1419733958190701385759359

theorem tailTrace_4147383 : CollatzResearch.WordTrace tailWord_4147383 prefixEnd_4147383 1419733958190701385759359 := by
  unfold tailWord_4147383
  simp only [CollatzResearch.WordTrace]
  refine ⟨151267485133747182469542803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100844990089164788313028535 151267485133747182469542803)
  ·
    refine ⟨226901227700620773704314205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151267485133747182469542803 226901227700620773704314205)
    ·
      refine ⟨85087960387732790139117827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226901227700620773704314205 85087960387732790139117827)
      ·
        refine ⟨127631940581599185208676741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85087960387732790139117827 127631940581599185208676741)
        ·
          refine ⟨23930988859049847226626889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127631940581599185208676741 23930988859049847226626889)
          ·
            refine ⟨17948241644287385419970167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23930988859049847226626889 17948241644287385419970167)
            ·
              refine ⟨26922362466431078129955251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17948241644287385419970167 26922362466431078129955251)
              ·
                refine ⟨40383543699646617194932877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26922362466431078129955251 40383543699646617194932877)
                ·
                  refine ⟨15143828887367481448099829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40383543699646617194932877 15143828887367481448099829)
                  ·
                    refine ⟨1419733958190701385759359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15143828887367481448099829 1419733958190701385759359)
                    ·
                      rfl

theorem cell22_4147383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_4147383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147383 prefixEnd_4147383 := by exact prefixLift 4147383
  have htrace : WordTrace (prefixWord ++ tailWord_4147383) baseStart_4147383 baseEnd_4147383 := by
    simpa [prefixWord, tailWord_4147383, baseEnd_4147383] using wordTrace_append hprefix tailTrace_4147383
  have hstable : (prefixWord ++ tailWord_4147383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147383).length < 2 ^ (prefixWord ++ tailWord_4147383).sum := by decide
  have hdescent : baseEnd_4147383 < baseStart_4147383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147385 : List Nat := [1, 2, 1, 4, 1, 2, 2, 5, 4]
def baseStart_4147385 : Nat := 118140960795 + 4147385 * 2 ^ 59
def prefixEnd_4147385 : Nat := 4983230072969 + 3 ^ 40 * 4147385 * 2
def baseEnd_4147385 : Nat := 473244880943858015736451

theorem tailTrace_4147385 : CollatzResearch.WordTrace tailWord_4147385 prefixEnd_4147385 473244880943858015736451 := by
  unfold tailWord_4147385
  simp only [CollatzResearch.WordTrace]
  refine ⟨151267558079739936811115609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100845038719826624540743739 151267558079739936811115609)
  ·
    refine ⟨113450668559804952608336707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151267558079739936811115609 113450668559804952608336707)
    ·
      refine ⟨170176002839707428912505061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113450668559804952608336707 170176002839707428912505061)
      ·
        refine ⟨31908000532445142921094699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170176002839707428912505061 31908000532445142921094699)
        ·
          refine ⟨47862000798667714381642049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31908000532445142921094699 47862000798667714381642049)
          ·
            refine ⟨35896500599000785786231537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47862000798667714381642049 35896500599000785786231537)
            ·
              refine ⟨26922375449250589339673653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35896500599000785786231537 26922375449250589339673653)
              ·
                refine ⟨2523972698367242750594405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26922375449250589339673653 2523972698367242750594405)
                ·
                  refine ⟨473244880943858015736451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523972698367242750594405 473244880943858015736451)
                  ·
                    rfl

theorem cell22_4147385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 4].length) (baseStart_4147385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147385 prefixEnd_4147385 := by exact prefixLift 4147385
  have htrace : WordTrace (prefixWord ++ tailWord_4147385) baseStart_4147385 baseEnd_4147385 := by
    simpa [prefixWord, tailWord_4147385, baseEnd_4147385] using wordTrace_append hprefix tailTrace_4147385
  have hstable : (prefixWord ++ tailWord_4147385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147385).length < 2 ^ (prefixWord ++ tailWord_4147385).sum := by decide
  have hdescent : baseEnd_4147385 < baseStart_4147385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147432 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 2, 4]
def baseStart_4147432 : Nat := 118140960795 + 4147432 * 2 ^ 59
def prefixEnd_4147432 : Nat := 4983230072969 + 3 ^ 40 * 4147432 * 2
def baseEnd_4147432 : Nat := 1419750731892081591284209

theorem tailTrace_4147432 : CollatzResearch.WordTrace tailWord_4147432 prefixEnd_4147432 1419750731892081591284209 := by
  unfold tailWord_4147432
  simp only [CollatzResearch.WordTrace]
  refine ⟨75634636155284831919038275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100846181540379775892051033 75634636155284831919038275)
  ·
    refine ⟨113451954232927247878557413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75634636155284831919038275 113451954232927247878557413)
    ·
      refine ⟨21272241418673858977229515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113451954232927247878557413 21272241418673858977229515)
      ·
        refine ⟨31908362128010788465844273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21272241418673858977229515 31908362128010788465844273)
        ·
          refine ⟨23931271596008091349383205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31908362128010788465844273 23931271596008091349383205)
          ·
            refine ⟨4487113424251517128009351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23931271596008091349383205 4487113424251517128009351)
            ·
              refine ⟨6730670136377275692014027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4487113424251517128009351 6730670136377275692014027)
              ·
                refine ⟨10096005204565913538021041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730670136377275692014027 10096005204565913538021041)
                ·
                  refine ⟨7572003903424435153515781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10096005204565913538021041 7572003903424435153515781)
                  ·
                    refine ⟨1419750731892081591284209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7572003903424435153515781 1419750731892081591284209)
                    ·
                      rfl

theorem cell22_4147432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_4147432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147432 prefixEnd_4147432 := by exact prefixLift 4147432
  have htrace : WordTrace (prefixWord ++ tailWord_4147432) baseStart_4147432 baseEnd_4147432 := by
    simpa [prefixWord, tailWord_4147432, baseEnd_4147432] using wordTrace_append hprefix tailTrace_4147432
  have hstable : (prefixWord ++ tailWord_4147432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147432).length < 2 ^ (prefixWord ++ tailWord_4147432).sum := by decide
  have hdescent : baseEnd_4147432 < baseStart_4147432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147503 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 8]
def baseStart_4147503 : Nat := 118140960795 + 4147503 * 2 ^ 59
def prefixEnd_4147503 : Nat := 4983230072969 + 3 ^ 40 * 4147503 * 2
def baseEnd_4147503 : Nat := 473258345547687024252997

theorem tailTrace_4147503 : CollatzResearch.WordTrace tailWord_4147503 prefixEnd_4147503 473258345547687024252997 := by
  unfold tailWord_4147503
  simp only [CollatzResearch.WordTrace]
  refine ⟨151271861893312442963911163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100847907928874961975940775 151271861893312442963911163)
  ·
    refine ⟨226907792839968664445866745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151271861893312442963911163 226907792839968664445866745)
    ·
      refine ⟨170180844629976498334400059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226907792839968664445866745 170180844629976498334400059)
      ·
        refine ⟨255271266944964747501600089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170180844629976498334400059 255271266944964747501600089)
        ·
          refine ⟨191453450208723560626200067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255271266944964747501600089 191453450208723560626200067)
          ·
            refine ⟨287180175313085340939300101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191453450208723560626200067 287180175313085340939300101)
            ·
              refine ⟨53846282871203501426118769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287180175313085340939300101 53846282871203501426118769)
              ·
                refine ⟨40384712153402626069589077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53846282871203501426118769 40384712153402626069589077)
                ·
                  refine ⟨473258345547687024252997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40384712153402626069589077 473258345547687024252997)
                  ·
                    rfl

theorem cell22_4147503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 8].length) (baseStart_4147503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147503 prefixEnd_4147503 := by exact prefixLift 4147503
  have htrace : WordTrace (prefixWord ++ tailWord_4147503) baseStart_4147503 baseEnd_4147503 := by
    simpa [prefixWord, tailWord_4147503, baseEnd_4147503] using wordTrace_append hprefix tailTrace_4147503
  have hstable : (prefixWord ++ tailWord_4147503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147503).length < 2 ^ (prefixWord ++ tailWord_4147503).sum := by decide
  have hdescent : baseEnd_4147503 < baseStart_4147503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147535 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 6, 3]
def baseStart_4147535 : Nat := 118140960795 + 4147535 * 2 ^ 59
def prefixEnd_4147535 : Nat := 4983230072969 + 3 ^ 40 * 4147535 * 2
def baseEnd_4147535 : Nat := 1419785990897023655958893

theorem tailTrace_4147535 : CollatzResearch.WordTrace tailWord_4147535 prefixEnd_4147535 1419785990897023655958893 := by
  unfold tailWord_4147535
  simp only [CollatzResearch.WordTrace]
  refine ⟨151273029029196512429076059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100848686019464341619384039 151273029029196512429076059)
  ·
    refine ⟨226909543543794768643614089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151273029029196512429076059 226909543543794768643614089)
    ·
      refine ⟨170182157657846076482710567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226909543543794768643614089 170182157657846076482710567)
      ·
        refine ⟨255273236486769114724065851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170182157657846076482710567 255273236486769114724065851)
        ·
          refine ⟨382909854730153672086098777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255273236486769114724065851 382909854730153672086098777)
          ·
            refine ⟨287182391047615254064574083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382909854730153672086098777 287182391047615254064574083)
            ·
              refine ⟨430773586571422881096861125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287182391047615254064574083 430773586571422881096861125)
              ·
                refine ⟨80770047482141790205661461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430773586571422881096861125 80770047482141790205661461)
                ·
                  refine ⟨3786095975725396415890381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80770047482141790205661461 3786095975725396415890381)
                  ·
                    refine ⟨1419785990897023655958893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786095975725396415890381 1419785990897023655958893)
                    ·
                      rfl

theorem cell22_4147535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 3].length) (baseStart_4147535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147535 prefixEnd_4147535 := by exact prefixLift 4147535
  have htrace : WordTrace (prefixWord ++ tailWord_4147535) baseStart_4147535 baseEnd_4147535 := by
    simpa [prefixWord, tailWord_4147535, baseEnd_4147535] using wordTrace_append hprefix tailTrace_4147535
  have hstable : (prefixWord ++ tailWord_4147535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147535).length < 2 ^ (prefixWord ++ tailWord_4147535).sum := by decide
  have hdescent : baseEnd_4147535 < baseStart_4147535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147552 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 1, 5]
def baseStart_4147552 : Nat := 118140960795 + 4147552 * 2 ^ 59
def prefixEnd_4147552 : Nat := 4983230072969 + 3 ^ 40 * 4147552 * 2
def baseEnd_4147552 : Nat := 1419791810344441278283841

theorem tailTrace_4147552 : CollatzResearch.WordTrace tailWord_4147552 prefixEnd_4147552 1419791810344441278283841 := by
  unfold tailWord_4147552
  simp only [CollatzResearch.WordTrace]
  refine ⟨75636824535067462166222455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100849099380089949554963273 75636824535067462166222455)
  ·
    refine ⟨113455236802601193249333683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75636824535067462166222455 113455236802601193249333683)
    ·
      refine ⟨170182855203901789874000525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113455236802601193249333683 170182855203901789874000525)
      ·
        refine ⟨63818570701463171202750197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170182855203901789874000525 63818570701463171202750197)
        ·
          refine ⟨5982991003262172300257831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63818570701463171202750197 5982991003262172300257831)
          ·
            refine ⟨8974486504893258450386747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982991003262172300257831 8974486504893258450386747)
            ·
              refine ⟨13461729757339887675580121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8974486504893258450386747 13461729757339887675580121)
              ·
                refine ⟨10096297318004915756685091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13461729757339887675580121 10096297318004915756685091)
                ·
                  refine ⟨15144445977007373635027637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10096297318004915756685091 15144445977007373635027637)
                  ·
                    refine ⟨1419791810344441278283841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15144445977007373635027637 1419791810344441278283841)
                    ·
                      rfl

theorem cell22_4147552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_4147552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147552 prefixEnd_4147552 := by exact prefixLift 4147552
  have htrace : WordTrace (prefixWord ++ tailWord_4147552) baseStart_4147552 baseEnd_4147552 := by
    simpa [prefixWord, tailWord_4147552, baseEnd_4147552] using wordTrace_append hprefix tailTrace_4147552
  have hstable : (prefixWord ++ tailWord_4147552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147552).length < 2 ^ (prefixWord ++ tailWord_4147552).sum := by decide
  have hdescent : baseEnd_4147552 < baseStart_4147552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147586 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4147586 : Nat := 118140960795 + 4147586 * 2 ^ 59
def prefixEnd_4147586 : Nat := 4983230072969 + 3 ^ 40 * 4147586 * 2
def baseEnd_4147586 : Nat := 1419803449239276522933737

theorem tailTrace_4147586 : CollatzResearch.WordTrace tailWord_4147586 prefixEnd_4147586 1419803449239276522933737 := by
  unfold tailWord_4147586
  simp only [CollatzResearch.WordTrace]
  refine ⟨37818722288002937034795653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100849926101341165426121741 37818722288002937034795653)
  ·
    refine ⟨7091010429000550694024185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37818722288002937034795653 7091010429000550694024185)
    ·
      refine ⟨5318257821750413020518139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7091010429000550694024185 5318257821750413020518139)
      ·
        refine ⟨7977386732625619530777209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318257821750413020518139 7977386732625619530777209)
        ·
          refine ⟨5983040049469214648082907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7977386732625619530777209 5983040049469214648082907)
          ·
            refine ⟨8974560074203821972124361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983040049469214648082907 8974560074203821972124361)
            ·
              refine ⟨6730920055652866479093271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8974560074203821972124361 6730920055652866479093271)
              ·
                refine ⟨10096380083479299718639907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730920055652866479093271 10096380083479299718639907)
                ·
                  refine ⟨15144570125218949577959861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10096380083479299718639907 15144570125218949577959861)
                  ·
                    refine ⟨1419803449239276522933737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15144570125218949577959861 1419803449239276522933737)
                    ·
                      rfl

theorem cell22_4147586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4147586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147586 prefixEnd_4147586 := by exact prefixLift 4147586
  have htrace : WordTrace (prefixWord ++ tailWord_4147586) baseStart_4147586 baseEnd_4147586 := by
    simpa [prefixWord, tailWord_4147586, baseEnd_4147586] using wordTrace_append hprefix tailTrace_4147586
  have hstable : (prefixWord ++ tailWord_4147586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147586).length < 2 ^ (prefixWord ++ tailWord_4147586).sum := by decide
  have hdescent : baseEnd_4147586 < baseStart_4147586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147657 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 1, 4]
def baseStart_4147657 : Nat := 118140960795 + 4147657 * 2 ^ 59
def prefixEnd_4147657 : Nat := 4983230072969 + 3 ^ 40 * 4147657 * 2
def baseEnd_4147657 : Nat := 1419827753990256004408519

theorem tailTrace_4147657 : CollatzResearch.WordTrace tailWord_4147657 prefixEnd_4147657 1419827753990256004408519 := by
  unfold tailWord_4147657
  simp only [CollatzResearch.WordTrace]
  refine ⟨151277478734754527265017225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100851652489836351510011483 151277478734754527265017225)
  ·
    refine ⟨113458109051065895448762919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151277478734754527265017225 113458109051065895448762919)
    ·
      refine ⟨170187163576598843173144379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113458109051065895448762919 170187163576598843173144379)
      ·
        refine ⟨255280745364898264759716569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170187163576598843173144379 255280745364898264759716569)
        ·
          refine ⟨191460559023673698569787427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255280745364898264759716569 191460559023673698569787427)
          ·
            refine ⟨287190838535510547854681141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191460559023673698569787427 287190838535510547854681141)
            ·
              refine ⟨26924141112704113861376357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287190838535510547854681141 26924141112704113861376357)
              ·
                refine ⟨5048276458632021349008067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26924141112704113861376357 5048276458632021349008067)
                ·
                  refine ⟨7572414687948032023512101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048276458632021349008067 7572414687948032023512101)
                  ·
                    refine ⟨1419827753990256004408519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7572414687948032023512101 1419827753990256004408519)
                    ·
                      rfl

theorem cell22_4147657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_4147657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147657 prefixEnd_4147657 := by exact prefixLift 4147657
  have htrace : WordTrace (prefixWord ++ tailWord_4147657) baseStart_4147657 baseEnd_4147657 := by
    simpa [prefixWord, tailWord_4147657, baseEnd_4147657] using wordTrace_append hprefix tailTrace_4147657
  have hstable : (prefixWord ++ tailWord_4147657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147657).length < 2 ^ (prefixWord ++ tailWord_4147657).sum := by decide
  have hdescent : baseEnd_4147657 < baseStart_4147657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147682 : List Nat := [3, 3, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4147682 : Nat := 118140960795 + 4147682 * 2 ^ 59
def prefixEnd_4147682 : Nat := 4983230072969 + 3 ^ 40 * 4147682 * 2
def baseEnd_4147682 : Nat := 1419836312001164272533443

theorem tailTrace_4147682 : CollatzResearch.WordTrace tailWord_4147682 prefixEnd_4147682 1419836312001164272533443 := by
  unfold tailWord_4147682
  simp only [CollatzResearch.WordTrace]
  refine ⟨37819597639915989133669325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100852260373109304356451533 37819597639915989133669325)
  ·
    refine ⟨14182349114968495925125997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37819597639915989133669325 14182349114968495925125997)
    ·
      refine ⟨5318380918113185971922249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14182349114968495925125997 5318380918113185971922249)
      ·
        refine ⟨3988785688584889478941687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5318380918113185971922249 3988785688584889478941687)
        ·
          refine ⟨5983178532877334218412531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988785688584889478941687 5983178532877334218412531)
          ·
            refine ⟨8974767799316001327618797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983178532877334218412531 8974767799316001327618797)
            ·
              refine ⟨3365537924743500497857049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8974767799316001327618797 3365537924743500497857049)
              ·
                refine ⟨2524153443557625373392787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3365537924743500497857049 2524153443557625373392787)
                ·
                  refine ⟨3786230165336438060089181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524153443557625373392787 3786230165336438060089181)
                  ·
                    refine ⟨1419836312001164272533443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786230165336438060089181 1419836312001164272533443)
                    ·
                      rfl

theorem cell22_4147682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4147682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147682 prefixEnd_4147682 := by exact prefixLift 4147682
  have htrace : WordTrace (prefixWord ++ tailWord_4147682) baseStart_4147682 baseEnd_4147682 := by
    simpa [prefixWord, tailWord_4147682, baseEnd_4147682] using wordTrace_append hprefix tailTrace_4147682
  have hstable : (prefixWord ++ tailWord_4147682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147682).length < 2 ^ (prefixWord ++ tailWord_4147682).sum := by decide
  have hdescent : baseEnd_4147682 < baseStart_4147682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147704 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 2, 3]
def baseStart_4147704 : Nat := 118140960795 + 4147704 * 2 ^ 59
def prefixEnd_4147704 : Nat := 4983230072969 + 3 ^ 40 * 4147704 * 2
def baseEnd_4147704 : Nat := 1419843843050763548483375

theorem tailTrace_4147704 : CollatzResearch.WordTrace tailWord_4147704 prefixEnd_4147704 1419843843050763548483375 := by
  unfold tailWord_4147704
  simp only [CollatzResearch.WordTrace]
  refine ⟨75639596482792127145989083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100852795310389502861318777 75639596482792127145989083)
  ·
    refine ⟨113459394724188190718983625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75639596482792127145989083 113459394724188190718983625)
    ·
      refine ⟨85094546043141143039237719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113459394724188190718983625 85094546043141143039237719)
      ·
        refine ⟨127641819064711714558856579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85094546043141143039237719 127641819064711714558856579)
        ·
          refine ⟨191462728597067571838284869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127641819064711714558856579 191462728597067571838284869)
          ·
            refine ⟨35899261611950169719678413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191462728597067571838284869 35899261611950169719678413)
            ·
              refine ⟨13462223104481313644879405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35899261611950169719678413 13462223104481313644879405)
              ·
                refine ⟨5048333664180492616829777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13462223104481313644879405 5048333664180492616829777)
                ·
                  refine ⟨3786250248135369462622333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5048333664180492616829777 3786250248135369462622333)
                  ·
                    refine ⟨1419843843050763548483375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786250248135369462622333 1419843843050763548483375)
                    ·
                      rfl

theorem cell22_4147704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_4147704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147704 prefixEnd_4147704 := by exact prefixLift 4147704
  have htrace : WordTrace (prefixWord ++ tailWord_4147704) baseStart_4147704 baseEnd_4147704 := by
    simpa [prefixWord, tailWord_4147704, baseEnd_4147704] using wordTrace_append hprefix tailTrace_4147704
  have hstable : (prefixWord ++ tailWord_4147704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147704).length < 2 ^ (prefixWord ++ tailWord_4147704).sum := by decide
  have hdescent : baseEnd_4147704 < baseStart_4147704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147725 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4147725 : Nat := 118140960795 + 4147725 * 2 ^ 59
def prefixEnd_4147725 : Nat := 4983230072969 + 3 ^ 40 * 4147725 * 2
def baseEnd_4147725 : Nat := 1419851031779926493708311

theorem tailTrace_4147725 : CollatzResearch.WordTrace tailWord_4147725 prefixEnd_4147725 1419851031779926493708311 := by
  unfold tailWord_4147725
  simp only [CollatzResearch.WordTrace]
  refine ⟨151279958898508174878492629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100853305932338783252328419 151279958898508174878492629)
  ·
    refine ⟨3545624036683785348714671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 151279958898508174878492629 3545624036683785348714671)
    ·
      refine ⟨5318436055025678023072007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3545624036683785348714671 5318436055025678023072007)
      ·
        refine ⟨7977654082538517034608011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318436055025678023072007 7977654082538517034608011)
        ·
          refine ⟨11966481123807775551912017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7977654082538517034608011 11966481123807775551912017)
          ·
            refine ⟨8974860842855831663934013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11966481123807775551912017 8974860842855831663934013)
            ·
              refine ⟨3365572816070936873975255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8974860842855831663934013 3365572816070936873975255)
              ·
                refine ⟨5048359224106405310962883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365572816070936873975255 5048359224106405310962883)
                ·
                  refine ⟨7572538836159607966444325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048359224106405310962883 7572538836159607966444325)
                  ·
                    refine ⟨1419851031779926493708311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7572538836159607966444325 1419851031779926493708311)
                    ·
                      rfl

theorem cell22_4147725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4147725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147725 prefixEnd_4147725 := by exact prefixLift 4147725
  have htrace : WordTrace (prefixWord ++ tailWord_4147725) baseStart_4147725 baseEnd_4147725 := by
    simpa [prefixWord, tailWord_4147725, baseEnd_4147725] using wordTrace_append hprefix tailTrace_4147725
  have hstable : (prefixWord ++ tailWord_4147725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147725).length < 2 ^ (prefixWord ++ tailWord_4147725).sum := by decide
  have hdescent : baseEnd_4147725 < baseStart_4147725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147747 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 2, 6]
def baseStart_4147747 : Nat := 118140960795 + 4147747 * 2 ^ 59
def prefixEnd_4147747 : Nat := 4983230072969 + 3 ^ 40 * 4147747 * 2
def baseEnd_4147747 : Nat := 1419858562829525769658243

theorem tailTrace_4147747 : CollatzResearch.WordTrace tailWord_4147747 prefixEnd_4147747 1419858562829525769658243 := by
  unfold tailWord_4147747
  simp only [CollatzResearch.WordTrace]
  refine ⟨151280761304428472635793495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100853840869618981757195663 151280761304428472635793495)
  ·
    refine ⟨226921141956642708953690243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151280761304428472635793495 226921141956642708953690243)
    ·
      refine ⟨340381712934964063430535365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226921141956642708953690243 340381712934964063430535365)
      ·
        refine ⟨63821571175305761893225381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340381712934964063430535365 63821571175305761893225381)
        ·
          refine ⟨11966544595369830354979759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63821571175305761893225381 11966544595369830354979759)
          ·
            refine ⟨17949816893054745532469639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11966544595369830354979759 17949816893054745532469639)
            ·
              refine ⟨26924725339582118298704459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17949816893054745532469639 26924725339582118298704459)
              ·
                refine ⟨40387088009373177448056689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26924725339582118298704459 40387088009373177448056689)
                ·
                  refine ⟨30290316007029883086042517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40387088009373177448056689 30290316007029883086042517)
                  ·
                    refine ⟨1419858562829525769658243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30290316007029883086042517 1419858562829525769658243)
                    ·
                      rfl

theorem cell22_4147747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 6].length) (baseStart_4147747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147747 prefixEnd_4147747 := by exact prefixLift 4147747
  have htrace : WordTrace (prefixWord ++ tailWord_4147747) baseStart_4147747 baseEnd_4147747 := by
    simpa [prefixWord, tailWord_4147747, baseEnd_4147747] using wordTrace_append hprefix tailTrace_4147747
  have hstable : (prefixWord ++ tailWord_4147747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147747).length < 2 ^ (prefixWord ++ tailWord_4147747).sum := by decide
  have hdescent : baseEnd_4147747 < baseStart_4147747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147766 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_4147766 : Nat := 118140960795 + 4147766 * 2 ^ 59
def prefixEnd_4147766 : Nat := 4983230072969 + 3 ^ 40 * 4147766 * 2
def baseEnd_4147766 : Nat := 1419865066917816053433185

theorem tailTrace_4147766 : CollatzResearch.WordTrace tailWord_4147766 prefixEnd_4147766 1419865066917816053433185 := by
  unfold tailWord_4147766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9455090893209977430045947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100854302860906425920490101 9455090893209977430045947)
  ·
    refine ⟨14182636339814966145068921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9455090893209977430045947 14182636339814966145068921)
    ·
      refine ⟨10636977254861224608801691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14182636339814966145068921 10636977254861224608801691)
      ·
        refine ⟨15955465882291836913202537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10636977254861224608801691 15955465882291836913202537)
        ·
          refine ⟨11966599411718877684901903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15955465882291836913202537 11966599411718877684901903)
          ·
            refine ⟨17949899117578316527352855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11966599411718877684901903 17949899117578316527352855)
            ·
              refine ⟨26924848676367474791029283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17949899117578316527352855 26924848676367474791029283)
              ·
                refine ⟨40387273014551212186543925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26924848676367474791029283 40387273014551212186543925)
                ·
                  refine ⟨3786306845114176142488493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40387273014551212186543925 3786306845114176142488493)
                  ·
                    refine ⟨1419865066917816053433185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786306845114176142488493 1419865066917816053433185)
                    ·
                      rfl

theorem cell22_4147766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_4147766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147766 prefixEnd_4147766 := by exact prefixLift 4147766
  have htrace : WordTrace (prefixWord ++ tailWord_4147766) baseStart_4147766 baseEnd_4147766 := by
    simpa [prefixWord, tailWord_4147766, baseEnd_4147766] using wordTrace_append hprefix tailTrace_4147766
  have hstable : (prefixWord ++ tailWord_4147766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147766).length < 2 ^ (prefixWord ++ tailWord_4147766).sum := by decide
  have hdescent : baseEnd_4147766 < baseStart_4147766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147783 : List Nat := [1, 1, 4, 1, 4, 2, 2, 3, 1, 3]
def baseStart_4147783 : Nat := 118140960795 + 4147783 * 2 ^ 59
def prefixEnd_4147783 : Nat := 4983230072969 + 3 ^ 40 * 4147783 * 2
def baseEnd_4147783 : Nat := 1419870886365233675758133

theorem tailTrace_4147783 : CollatzResearch.WordTrace tailWord_4147783 prefixEnd_4147783 1419870886365233675758133 := by
  unfold tailWord_4147783
  simp only [CollatzResearch.WordTrace]
  refine ⟨151282074332298050784104003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100854716221532033856069335 151282074332298050784104003)
  ·
    refine ⟨226923111498447076176156005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151282074332298050784104003 226923111498447076176156005)
    ·
      refine ⟨42548083405958826783029251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226923111498447076176156005 42548083405958826783029251)
      ·
        refine ⟨63822125108938240174543877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42548083405958826783029251 63822125108938240174543877)
        ·
          refine ⟨11966648457925920032726977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63822125108938240174543877 11966648457925920032726977)
          ·
            refine ⟨8974986343444440024545233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11966648457925920032726977 8974986343444440024545233)
            ·
              refine ⟨6731239757583330018408925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8974986343444440024545233 6731239757583330018408925)
              ·
                refine ⟨2524214909093748756903347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6731239757583330018408925 2524214909093748756903347)
                ·
                  refine ⟨3786322363640623135355021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524214909093748756903347 3786322363640623135355021)
                  ·
                    refine ⟨1419870886365233675758133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786322363640623135355021 1419870886365233675758133)
                    ·
                      rfl

theorem cell22_4147783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_4147783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147783 prefixEnd_4147783 := by exact prefixLift 4147783
  have htrace : WordTrace (prefixWord ++ tailWord_4147783) baseStart_4147783 baseEnd_4147783 := by
    simpa [prefixWord, tailWord_4147783, baseEnd_4147783] using wordTrace_append hprefix tailTrace_4147783
  have hstable : (prefixWord ++ tailWord_4147783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147783).length < 2 ^ (prefixWord ++ tailWord_4147783).sum := by decide
  have hdescent : baseEnd_4147783 < baseStart_4147783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147792 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_4147792 : Nat := 118140960795 + 4147792 * 2 ^ 59
def prefixEnd_4147792 : Nat := 4983230072969 + 3 ^ 40 * 4147792 * 2
def baseEnd_4147792 : Nat := 1419873967249160652283105

theorem tailTrace_4147792 : CollatzResearch.WordTrace tailWord_4147792 prefixEnd_4147792 1419873967249160652283105 := by
  unfold tailWord_4147792
  simp only [CollatzResearch.WordTrace]
  refine ⟨75641201294632722660590815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100854935059510296880787753 75641201294632722660590815)
  ·
    refine ⟨113461801941949083990886223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75641201294632722660590815 113461801941949083990886223)
    ·
      refine ⟨170192702912923625986329335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113461801941949083990886223 170192702912923625986329335)
      ·
        refine ⟨255289054369385438979494003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170192702912923625986329335 255289054369385438979494003)
        ·
          refine ⟨382933581554078158469241005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255289054369385438979494003 382933581554078158469241005)
          ·
            refine ⟨143600093082779309425965377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382933581554078158469241005 143600093082779309425965377)
            ·
              refine ⟨107700069812084482069474033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143600093082779309425965377 107700069812084482069474033)
              ·
                refine ⟨80775052359063361552105525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107700069812084482069474033 80775052359063361552105525)
                ·
                  refine ⟨7572661158662190145509893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80775052359063361552105525 7572661158662190145509893)
                  ·
                    refine ⟨1419873967249160652283105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7572661158662190145509893 1419873967249160652283105)
                    ·
                      rfl

theorem cell22_4147792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_4147792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147792 prefixEnd_4147792 := by exact prefixLift 4147792
  have htrace : WordTrace (prefixWord ++ tailWord_4147792) baseStart_4147792 baseEnd_4147792 := by
    simpa [prefixWord, tailWord_4147792, baseEnd_4147792] using wordTrace_append hprefix tailTrace_4147792
  have hstable : (prefixWord ++ tailWord_4147792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147792).length < 2 ^ (prefixWord ++ tailWord_4147792).sum := by decide
  have hdescent : baseEnd_4147792 < baseStart_4147792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147796 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 5]
def baseStart_4147796 : Nat := 118140960795 + 4147796 * 2 ^ 59
def prefixEnd_4147796 : Nat := 4983230072969 + 3 ^ 40 * 4147796 * 2
def baseEnd_4147796 : Nat := 473291778843635325061031

theorem tailTrace_4147796 : CollatzResearch.WordTrace tailWord_4147796 prefixEnd_4147796 473291778843635325061031 := by
  unfold tailWord_4147796
  simp only [CollatzResearch.WordTrace]
  refine ⟨75641274240625477002163621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100855032320833969336218161 75641274240625477002163621)
  ·
    refine ⟨14182738920117276937905679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75641274240625477002163621 14182738920117276937905679)
    ·
      refine ⟨21274108380175915406858519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14182738920117276937905679 21274108380175915406858519)
      ·
        refine ⟨31911162570263873110287779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21274108380175915406858519 31911162570263873110287779)
        ·
          refine ⟨47866743855395809665431669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31911162570263873110287779 47866743855395809665431669)
          ·
            refine ⟨4487507236443357156134219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47866743855395809665431669 4487507236443357156134219)
            ·
              refine ⟨6731260854665035734201329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4487507236443357156134219 6731260854665035734201329)
              ·
                refine ⟨5048445640998776800650997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6731260854665035734201329 5048445640998776800650997)
                ·
                  refine ⟨473291778843635325061031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5048445640998776800650997 473291778843635325061031)
                  ·
                    rfl

theorem cell22_4147796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_4147796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147796 prefixEnd_4147796 := by exact prefixLift 4147796
  have htrace : WordTrace (prefixWord ++ tailWord_4147796) baseStart_4147796 baseEnd_4147796 := by
    simpa [prefixWord, tailWord_4147796, baseEnd_4147796] using wordTrace_append hprefix tailTrace_4147796
  have hstable : (prefixWord ++ tailWord_4147796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147796).length < 2 ^ (prefixWord ++ tailWord_4147796).sum := by decide
  have hdescent : baseEnd_4147796 < baseStart_4147796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147873 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 2, 3]
def baseStart_4147873 : Nat := 118140960795 + 4147873 * 2 ^ 59
def prefixEnd_4147873 : Nat := 4983230072969 + 3 ^ 40 * 4147873 * 2
def baseEnd_4147873 : Nat := 1419901695204503441007857

theorem tailTrace_4147873 : CollatzResearch.WordTrace tailWord_4147873 prefixEnd_4147873 1419901695204503441007857 := by
  unfold tailWord_4147873
  simp only [CollatzResearch.WordTrace]
  refine ⟨151285356901971996154880273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100856904601314664103253515 151285356901971996154880273)
  ·
    refine ⟨113464017676478997116160205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151285356901971996154880273 113464017676478997116160205)
    ·
      refine ⟨42549006628679623918560077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113464017676478997116160205 42549006628679623918560077)
      ·
        refine ⟨15955877485754858969460029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42549006628679623918560077 15955877485754858969460029)
        ·
          refine ⟨5983454057158072113547511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15955877485754858969460029 5983454057158072113547511)
          ·
            refine ⟨8975181085737108170321267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983454057158072113547511 8975181085737108170321267)
            ·
              refine ⟨13462771628605662255481901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8975181085737108170321267 13462771628605662255481901)
              ·
                refine ⟨5048539360727123345805713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13462771628605662255481901 5048539360727123345805713)
                ·
                  refine ⟨3786404520545342509354285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5048539360727123345805713 3786404520545342509354285)
                  ·
                    refine ⟨1419901695204503441007857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786404520545342509354285 1419901695204503441007857)
                    ·
                      rfl

theorem cell22_4147873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_4147873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147873 prefixEnd_4147873 := by exact prefixLift 4147873
  have htrace : WordTrace (prefixWord ++ tailWord_4147873) baseStart_4147873 baseEnd_4147873 := by
    simpa [prefixWord, tailWord_4147873, baseEnd_4147873] using wordTrace_append hprefix tailTrace_4147873
  have hstable : (prefixWord ++ tailWord_4147873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147873).length < 2 ^ (prefixWord ++ tailWord_4147873).sum := by decide
  have hdescent : baseEnd_4147873 < baseStart_4147873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147886 : List Nat := [4, 1, 4, 1, 1, 1, 2, 8]
def baseStart_4147886 : Nat := 118140960795 + 4147886 * 2 ^ 59
def prefixEnd_4147886 : Nat := 4983230072969 + 3 ^ 40 * 4147886 * 2
def baseEnd_4147886 : Nat := 157767349485575082270313

theorem tailTrace_4147886 : CollatzResearch.WordTrace tailWord_4147886 prefixEnd_4147886 157767349485575082270313 := by
  unfold tailWord_4147886
  simp only [CollatzResearch.WordTrace]
  refine ⟨18910728881365612421887939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100857220700616599583402341 18910728881365612421887939)
  ·
    refine ⟨28366093322048418632831909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18910728881365612421887939 28366093322048418632831909)
    ·
      refine ⟨5318642497884078493655983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28366093322048418632831909 5318642497884078493655983)
      ·
        refine ⟨7977963746826117740483975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318642497884078493655983 7977963746826117740483975)
        ·
          refine ⟨11966945620239176610725963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7977963746826117740483975 11966945620239176610725963)
          ·
            refine ⟨17950418430358764916088945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11966945620239176610725963 17950418430358764916088945)
            ·
              refine ⟨13462813822769073687066709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17950418430358764916088945 13462813822769073687066709)
              ·
                refine ⟨157767349485575082270313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13462813822769073687066709 157767349485575082270313)
                ·
                  rfl

theorem cell22_4147886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_4147886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147886 prefixEnd_4147886 := by exact prefixLift 4147886
  have htrace : WordTrace (prefixWord ++ tailWord_4147886) baseStart_4147886 baseEnd_4147886 := by
    simpa [prefixWord, tailWord_4147886, baseEnd_4147886] using wordTrace_append hprefix tailTrace_4147886
  have hstable : (prefixWord ++ tailWord_4147886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147886).length < 2 ^ (prefixWord ++ tailWord_4147886).sum := by decide
  have hdescent : baseEnd_4147886 < baseStart_4147886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147929 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_4147929 : Nat := 118140960795 + 4147929 * 2 ^ 59
def prefixEnd_4147929 : Nat := 4983230072969 + 3 ^ 40 * 4147929 * 2
def baseEnd_4147929 : Nat := 1419920865148937961607685

theorem tailTrace_4147929 : CollatzResearch.WordTrace tailWord_4147929 prefixEnd_4147929 1419920865148937961607685 := by
  unfold tailWord_4147929
  simp only [CollatzResearch.WordTrace]
  refine ⟨151287399389769117718918841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100858266259846078479279227 151287399389769117718918841)
  ·
    refine ⟨113465549542326838289189131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151287399389769117718918841 113465549542326838289189131)
    ·
      refine ⟨170198324313490257433783697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113465549542326838289189131 170198324313490257433783697)
      ·
        refine ⟨127648743235117693075337773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170198324313490257433783697 127648743235117693075337773)
        ·
          refine ⟨47868278713169134903251665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127648743235117693075337773 47868278713169134903251665)
          ·
            refine ⟨35901209034876851177438749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47868278713169134903251665 35901209034876851177438749)
            ·
              refine ⟨13462953388078819191539531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35901209034876851177438749 13462953388078819191539531)
              ·
                refine ⟨20194430082118228787309297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13462953388078819191539531 20194430082118228787309297)
                ·
                  refine ⟨15145822561588671590481973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20194430082118228787309297 15145822561588671590481973)
                  ·
                    refine ⟨1419920865148937961607685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15145822561588671590481973 1419920865148937961607685)
                    ·
                      rfl

theorem cell22_4147929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_4147929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147929 prefixEnd_4147929 := by exact prefixLift 4147929
  have htrace : WordTrace (prefixWord ++ tailWord_4147929) baseStart_4147929 baseEnd_4147929 := by
    simpa [prefixWord, tailWord_4147929, baseEnd_4147929] using wordTrace_append hprefix tailTrace_4147929
  have hstable : (prefixWord ++ tailWord_4147929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147929).length < 2 ^ (prefixWord ++ tailWord_4147929).sum := by decide
  have hdescent : baseEnd_4147929 < baseStart_4147929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147976 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 6]
def baseStart_4147976 : Nat := 118140960795 + 4147976 * 2 ^ 59
def prefixEnd_4147976 : Nat := 4983230072969 + 3 ^ 40 * 4147976 * 2
def baseEnd_4147976 : Nat := 473312318069815168560847

theorem tailTrace_4147976 : CollatzResearch.WordTrace tailWord_4147976 prefixEnd_4147976 473312318069815168560847 := by
  unfold tailWord_4147976
  simp only [CollatzResearch.WordTrace]
  refine ⟨75644556810299422372939891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100859409080399229830586521 75644556810299422372939891)
  ·
    refine ⟨113466835215449133559409837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75644556810299422372939891 113466835215449133559409837)
    ·
      refine ⟨42550063205793425084778689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113466835215449133559409837 42550063205793425084778689)
      ·
        refine ⟨31912547404345068813584017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42550063205793425084778689 31912547404345068813584017)
        ·
          refine ⟨23934410553258801610188013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31912547404345068813584017 23934410553258801610188013)
          ·
            refine ⟨8975403957472050603820505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23934410553258801610188013 8975403957472050603820505)
            ·
              refine ⟨6731552968104037952865379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8975403957472050603820505 6731552968104037952865379)
              ·
                refine ⟨10097329452156056929298069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731552968104037952865379 10097329452156056929298069)
                ·
                  refine ⟨473312318069815168560847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10097329452156056929298069 473312318069815168560847)
                  ·
                    rfl

theorem cell22_4147976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_4147976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147976 prefixEnd_4147976 := by exact prefixLift 4147976
  have htrace : WordTrace (prefixWord ++ tailWord_4147976) baseStart_4147976 baseEnd_4147976 := by
    simpa [prefixWord, tailWord_4147976, baseEnd_4147976] using wordTrace_append hprefix tailTrace_4147976
  have hstable : (prefixWord ++ tailWord_4147976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147976).length < 2 ^ (prefixWord ++ tailWord_4147976).sum := by decide
  have hdescent : baseEnd_4147976 < baseStart_4147976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147989 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_4147989 : Nat := 118140960795 + 4147989 * 2 ^ 59
def prefixEnd_4147989 : Nat := 4983230072969 + 3 ^ 40 * 4147989 * 2
def baseEnd_4147989 : Nat := 1419941404375117805107501

theorem tailTrace_4147989 : CollatzResearch.WordTrace tailWord_4147989 prefixEnd_4147989 1419941404375117805107501 := by
  unfold tailWord_4147989
  simp only [CollatzResearch.WordTrace]
  refine ⟨151289587769551747966103021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100859725179701165310735347 151289587769551747966103021)
  ·
    refine ⟨56733595413581905487288633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151289587769551747966103021 56733595413581905487288633)
    ·
      refine ⟨42550196560186429115466475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56733595413581905487288633 42550196560186429115466475)
      ·
        refine ⟨63825294840279643673199713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42550196560186429115466475 63825294840279643673199713)
        ·
          refine ⟨47868971130209732754899785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63825294840279643673199713 47868971130209732754899785)
          ·
            refine ⟨35901728347657299566174839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47868971130209732754899785 35901728347657299566174839)
            ·
              refine ⟨53852592521485949349262259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35901728347657299566174839 53852592521485949349262259)
              ·
                refine ⟨80778888782228924023893389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53852592521485949349262259 80778888782228924023893389)
                ·
                  refine ⟨30292083293335846508960021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80778888782228924023893389 30292083293335846508960021)
                  ·
                    refine ⟨1419941404375117805107501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30292083293335846508960021 1419941404375117805107501)
                    ·
                      rfl

theorem cell22_4147989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_4147989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4147989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4147989 prefixEnd_4147989 := by exact prefixLift 4147989
  have htrace : WordTrace (prefixWord ++ tailWord_4147989) baseStart_4147989 baseEnd_4147989 := by
    simpa [prefixWord, tailWord_4147989, baseEnd_4147989] using wordTrace_append hprefix tailTrace_4147989
  have hstable : (prefixWord ++ tailWord_4147989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147989).length < 2 ^ (prefixWord ++ tailWord_4147989).sum := by decide
  have hdescent : baseEnd_4147989 < baseStart_4147989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148021 : List Nat := [1, 3, 3, 1, 3, 3, 8]
def baseStart_4148021 : Nat := 118140960795 + 4148021 * 2 ^ 59
def prefixEnd_4148021 : Nat := 4983230072969 + 3 ^ 40 * 4148021 * 2
def baseEnd_4148021 : Nat := 52590828097373347715089

theorem tailTrace_4148021 : CollatzResearch.WordTrace tailWord_4148021 prefixEnd_4148021 52590828097373347715089 := by
  unfold tailWord_4148021
  simp only [CollatzResearch.WordTrace]
  refine ⟨151290754905435817431267917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100860503270290544954178611 151290754905435817431267917)
  ·
    refine ⟨56734033089538431536725469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151290754905435817431267917 56734033089538431536725469)
    ·
      refine ⟨21275262408576911826272051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56734033089538431536725469 21275262408576911826272051)
      ·
        refine ⟨31912893612865367739408077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21275262408576911826272051 31912893612865367739408077)
        ·
          refine ⟨11967335104824512902278029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31912893612865367739408077 11967335104824512902278029)
          ·
            refine ⟨4487750664309192338354261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11967335104824512902278029 4487750664309192338354261)
            ·
              refine ⟨52590828097373347715089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4487750664309192338354261 52590828097373347715089)
              ·
                rfl

theorem cell22_4148021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 8].length) (baseStart_4148021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148021 prefixEnd_4148021 := by exact prefixLift 4148021
  have htrace : WordTrace (prefixWord ++ tailWord_4148021) baseStart_4148021 baseEnd_4148021 := by
    simpa [prefixWord, tailWord_4148021, baseEnd_4148021] using wordTrace_append hprefix tailTrace_4148021
  have hstable : (prefixWord ++ tailWord_4148021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148021).length < 2 ^ (prefixWord ++ tailWord_4148021).sum := by decide
  have hdescent : baseEnd_4148021 < baseStart_4148021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148128 : List Nat := [2, 1, 1, 4, 1, 1, 3, 5, 4]
def baseStart_4148128 : Nat := 118140960795 + 4148128 * 2 ^ 59
def prefixEnd_4148128 : Nat := 4983230072969 + 3 ^ 40 * 4148128 * 2
def baseEnd_4148128 : Nat := 473329662305255925294025

theorem tailTrace_4148128 : CollatzResearch.WordTrace tailWord_4148128 prefixEnd_4148128 473329662305255925294025 := by
  unfold tailWord_4148128
  simp only [CollatzResearch.WordTrace]
  refine ⟨75647328758024087352706519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100863105010698783136942025 75647328758024087352706519)
  ·
    refine ⟨113470993137036131029059779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75647328758024087352706519 113470993137036131029059779)
    ·
      refine ⟨170206489705554196543589669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113470993137036131029059779 170206489705554196543589669)
      ·
        refine ⟨31913716819791411851923063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170206489705554196543589669 31913716819791411851923063)
        ·
          refine ⟨47870575229687117777884595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31913716819791411851923063 47870575229687117777884595)
          ·
            refine ⟨71805862844530676666826893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47870575229687117777884595 71805862844530676666826893)
            ·
              refine ⟨26927198566699003750060085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71805862844530676666826893 26927198566699003750060085)
              ·
                refine ⟨2524424865628031601568133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26927198566699003750060085 2524424865628031601568133)
                ·
                  refine ⟨473329662305255925294025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2524424865628031601568133 473329662305255925294025)
                  ·
                    rfl

theorem cell22_4148128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 4].length) (baseStart_4148128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148128 prefixEnd_4148128 := by exact prefixLift 4148128
  have htrace : WordTrace (prefixWord ++ tailWord_4148128) baseStart_4148128 baseEnd_4148128 := by
    simpa [prefixWord, tailWord_4148128, baseEnd_4148128] using wordTrace_append hprefix tailTrace_4148128
  have hstable : (prefixWord ++ tailWord_4148128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148128).length < 2 ^ (prefixWord ++ tailWord_4148128).sum := by decide
  have hdescent : baseEnd_4148128 < baseStart_4148128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148130 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_4148130 : Nat := 118140960795 + 4148130 * 2 ^ 59
def prefixEnd_4148130 : Nat := 4983230072969 + 3 ^ 40 * 4148130 * 2
def baseEnd_4148130 : Nat := 1419989671556640437332069

theorem tailTrace_4148130 : CollatzResearch.WordTrace tailWord_4148130 prefixEnd_4148130 1419989671556640437332069 := by
  unfold tailWord_4148130
  simp only [CollatzResearch.WordTrace]
  refine ⟨37823682615510232261746461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100863153641360619364657229 37823682615510232261746461)
  ·
    refine ⟨14183880980816337098154923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37823682615510232261746461 14183880980816337098154923)
    ·
      refine ⟨21275821471224505647232385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14183880980816337098154923 21275821471224505647232385)
      ·
        refine ⟨15956866103418379235424289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21275821471224505647232385 15956866103418379235424289)
        ·
          refine ⟨11967649577563784426568217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15956866103418379235424289 11967649577563784426568217)
          ·
            refine ⟨8975737183172838319926163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11967649577563784426568217 8975737183172838319926163)
            ·
              refine ⟨13463605774759257479889245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8975737183172838319926163 13463605774759257479889245)
              ·
                refine ⟨5048852165534721554958467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13463605774759257479889245 5048852165534721554958467)
                ·
                  refine ⟨7573278248302082332437701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048852165534721554958467 7573278248302082332437701)
                  ·
                    refine ⟨1419989671556640437332069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7573278248302082332437701 1419989671556640437332069)
                    ·
                      rfl

theorem cell22_4148130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_4148130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148130 prefixEnd_4148130 := by exact prefixLift 4148130
  have htrace : WordTrace (prefixWord ++ tailWord_4148130) baseStart_4148130 baseEnd_4148130 := by
    simpa [prefixWord, tailWord_4148130, baseEnd_4148130] using wordTrace_append hprefix tailTrace_4148130
  have hstable : (prefixWord ++ tailWord_4148130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148130).length < 2 ^ (prefixWord ++ tailWord_4148130).sum := by decide
  have hdescent : baseEnd_4148130 < baseStart_4148130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148143 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 2, 3]
def baseStart_4148143 : Nat := 118140960795 + 4148143 * 2 ^ 59
def prefixEnd_4148143 : Nat := 4983230072969 + 3 ^ 40 * 4148143 * 2
def baseEnd_4148143 : Nat := 1419994121722312736757029

theorem tailTrace_4148143 : CollatzResearch.WordTrace tailWord_4148143 prefixEnd_4148143 1419994121722312736757029 := by
  unfold tailWord_4148143
  simp only [CollatzResearch.WordTrace]
  refine ⟨151295204610993832267209083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100863469740662554844806055 151295204610993832267209083)
  ·
    refine ⟨226942806916490748400813625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151295204610993832267209083 226942806916490748400813625)
    ·
      refine ⟨170207105187368061300610219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226942806916490748400813625 170207105187368061300610219)
      ·
        refine ⟨255310657781052091950915329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170207105187368061300610219 255310657781052091950915329)
        ·
          refine ⟨191482993335789068963186497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255310657781052091950915329 191482993335789068963186497)
          ·
            refine ⟨143612245001841801722389873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191482993335789068963186497 143612245001841801722389873)
            ·
              refine ⟨107709183751381351291792405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143612245001841801722389873 107709183751381351291792405)
              ·
                refine ⟨5048867988346000841802769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107709183751381351291792405 5048867988346000841802769)
                ·
                  refine ⟨3786650991259500631352077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5048867988346000841802769 3786650991259500631352077)
                  ·
                    refine ⟨1419994121722312736757029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786650991259500631352077 1419994121722312736757029)
                    ·
                      rfl

theorem cell22_4148143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 3].length) (baseStart_4148143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148143 prefixEnd_4148143 := by exact prefixLift 4148143
  have htrace : WordTrace (prefixWord ++ tailWord_4148143) baseStart_4148143 baseEnd_4148143 := by
    simpa [prefixWord, tailWord_4148143, baseEnd_4148143] using wordTrace_append hprefix tailTrace_4148143
  have hstable : (prefixWord ++ tailWord_4148143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148143).length < 2 ^ (prefixWord ++ tailWord_4148143).sum := by decide
  have hdescent : baseEnd_4148143 < baseStart_4148143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148216 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_4148216 : Nat := 118140960795 + 4148216 * 2 ^ 59
def prefixEnd_4148216 : Nat := 4983230072969 + 3 ^ 40 * 4148216 * 2
def baseEnd_4148216 : Nat := 1420019111114164879681805

theorem tailTrace_4148216 : CollatzResearch.WordTrace tailWord_4148216 prefixEnd_4148216 1420019111114164879681805 := by
  unfold tailWord_4148216
  simp only [CollatzResearch.WordTrace]
  refine ⟨75648933569864682867308251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100865244759819577156411001 75648933569864682867308251)
  ·
    refine ⟨113473400354797024300962377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75648933569864682867308251 113473400354797024300962377)
    ·
      refine ⟨85105050266097768225721783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113473400354797024300962377 85105050266097768225721783)
      ·
        refine ⟨127657575399146652338582675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85105050266097768225721783 127657575399146652338582675)
        ·
          refine ⟨191486363098719978507874013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127657575399146652338582675 191486363098719978507874013)
          ·
            refine ⟨71807386162019991940452755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191486363098719978507874013 71807386162019991940452755)
            ·
              refine ⟨107711079243029987910679133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71807386162019991940452755 107711079243029987910679133)
              ·
                refine ⟨40391654716136245466504675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107711079243029987910679133 40391654716136245466504675)
                ·
                  refine ⟨60587482074204368199757013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40391654716136245466504675 60587482074204368199757013)
                  ·
                    refine ⟨1420019111114164879681805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60587482074204368199757013 1420019111114164879681805)
                    ·
                      rfl

theorem cell22_4148216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_4148216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148216 prefixEnd_4148216 := by exact prefixLift 4148216
  have htrace : WordTrace (prefixWord ++ tailWord_4148216) baseStart_4148216 baseEnd_4148216 := by
    simpa [prefixWord, tailWord_4148216, baseEnd_4148216] using wordTrace_append hprefix tailTrace_4148216
  have hstable : (prefixWord ++ tailWord_4148216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148216).length < 2 ^ (prefixWord ++ tailWord_4148216).sum := by decide
  have hdescent : baseEnd_4148216 < baseStart_4148216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148368 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_4148368 : Nat := 118140960795 + 4148368 * 2 ^ 59
def prefixEnd_4148368 : Nat := 4983230072969 + 3 ^ 40 * 4148368 * 2
def baseEnd_4148368 : Nat := 1420071143820487149881339

theorem tailTrace_4148368 : CollatzResearch.WordTrace tailWord_4148368 prefixEnd_4148368 1420071143820487149881339 := by
  unfold tailWord_4148368
  simp only [CollatzResearch.WordTrace]
  refine ⟨75651705517589347847074879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100868940690119130462766505 75651705517589347847074879)
  ·
    refine ⟨113477558276384021770612319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75651705517589347847074879 113477558276384021770612319)
    ·
      refine ⟨170216337414576032655918479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113477558276384021770612319 170216337414576032655918479)
      ·
        refine ⟨255324506121864048983877719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170216337414576032655918479 255324506121864048983877719)
        ·
          refine ⟨382986759182796073475816579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255324506121864048983877719 382986759182796073475816579)
          ·
            refine ⟨574480138774194110213724869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382986759182796073475816579 574480138774194110213724869)
            ·
              refine ⟨107715026020161395665073413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 574480138774194110213724869 107715026020161395665073413)
              ·
                refine ⟨20196567378780261687201265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107715026020161395665073413 20196567378780261687201265)
                ·
                  refine ⟨15147425534085196265400949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20196567378780261687201265 15147425534085196265400949)
                  ·
                    refine ⟨1420071143820487149881339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15147425534085196265400949 1420071143820487149881339)
                    ·
                      rfl

theorem cell22_4148368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_4148368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148368 prefixEnd_4148368 := by exact prefixLift 4148368
  have htrace : WordTrace (prefixWord ++ tailWord_4148368) baseStart_4148368 baseEnd_4148368 := by
    simpa [prefixWord, tailWord_4148368, baseEnd_4148368] using wordTrace_append hprefix tailTrace_4148368
  have hstable : (prefixWord ++ tailWord_4148368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148368).length < 2 ^ (prefixWord ++ tailWord_4148368).sum := by decide
  have hdescent : baseEnd_4148368 < baseStart_4148368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148370 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_4148370 : Nat := 118140960795 + 4148370 * 2 ^ 59
def prefixEnd_4148370 : Nat := 4983230072969 + 3 ^ 40 * 4148370 * 2
def baseEnd_4148370 : Nat := 473357276153786603777111

theorem tailTrace_4148370 : CollatzResearch.WordTrace tailWord_4148370 prefixEnd_4148370 473357276153786603777111 := by
  unfold tailWord_4148370
  simp only [CollatzResearch.WordTrace]
  refine ⟨37825870995292862508930641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100868989320780966690481709 37825870995292862508930641)
  ·
    refine ⟨28369403246469646881697981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37825870995292862508930641 28369403246469646881697981)
    ·
      refine ⟨10638526217426117580636743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28369403246469646881697981 10638526217426117580636743)
      ·
        refine ⟨15957789326139176370955115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10638526217426117580636743 15957789326139176370955115)
        ·
          refine ⟨23936683989208764556432673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15957789326139176370955115 23936683989208764556432673)
          ·
            refine ⟨17952512991906573417324505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23936683989208764556432673 17952512991906573417324505)
            ·
              refine ⟨13464384743929930062993379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17952512991906573417324505 13464384743929930062993379)
              ·
                refine ⟨20196577115894895094490069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13464384743929930062993379 20196577115894895094490069)
                ·
                  refine ⟨473357276153786603777111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20196577115894895094490069 473357276153786603777111)
                  ·
                    rfl

theorem cell22_4148370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_4148370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148370 prefixEnd_4148370 := by exact prefixLift 4148370
  have htrace : WordTrace (prefixWord ++ tailWord_4148370) baseStart_4148370 baseEnd_4148370 := by
    simpa [prefixWord, tailWord_4148370, baseEnd_4148370] using wordTrace_append hprefix tailTrace_4148370
  have hstable : (prefixWord ++ tailWord_4148370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148370).length < 2 ^ (prefixWord ++ tailWord_4148370).sum := by decide
  have hdescent : baseEnd_4148370 < baseStart_4148370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148447 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 2, 3]
def baseStart_4148447 : Nat := 118140960795 + 4148447 * 2 ^ 59
def prefixEnd_4148447 : Nat := 4983230072969 + 3 ^ 40 * 4148447 * 2
def baseEnd_4148447 : Nat := 1420098187134957277156097

theorem tailTrace_4148447 : CollatzResearch.WordTrace tailWord_4148447 prefixEnd_4148447 1420098187134957277156097 := by
  unfold tailWord_4148447
  simp only [CollatzResearch.WordTrace]
  refine ⟨151306292401892492186275595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100870861601261661457517063 151306292401892492186275595)
  ·
    refine ⟨226959438602838738279413393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151306292401892492186275595 226959438602838738279413393)
    ·
      refine ⟨170219578952129053709560045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226959438602838738279413393 170219578952129053709560045)
      ·
        refine ⟨63832342107048395141085017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170219578952129053709560045 63832342107048395141085017)
        ·
          refine ⟨47874256580286296355813763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63832342107048395141085017 47874256580286296355813763)
          ·
            refine ⟨71811384870429444533720645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47874256580286296355813763 71811384870429444533720645)
            ·
              refine ⟨13464634663205520850072621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71811384870429444533720645 13464634663205520850072621)
              ·
                refine ⟨5049237998702070318777233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13464634663205520850072621 5049237998702070318777233)
                ·
                  refine ⟨3786928499026552739082925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5049237998702070318777233 3786928499026552739082925)
                  ·
                    refine ⟨1420098187134957277156097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786928499026552739082925 1420098187134957277156097)
                    ·
                      rfl

theorem cell22_4148447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 3].length) (baseStart_4148447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148447 prefixEnd_4148447 := by exact prefixLift 4148447
  have htrace : WordTrace (prefixWord ++ tailWord_4148447) baseStart_4148447 baseEnd_4148447 := by
    simpa [prefixWord, tailWord_4148447, baseEnd_4148447] using wordTrace_append hprefix tailTrace_4148447
  have hstable : (prefixWord ++ tailWord_4148447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148447).length < 2 ^ (prefixWord ++ tailWord_4148447).sum := by decide
  have hdescent : baseEnd_4148447 < baseStart_4148447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148462 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_4148462 : Nat := 118140960795 + 4148462 * 2 ^ 59
def prefixEnd_4148462 : Nat := 4983230072969 + 3 ^ 40 * 4148462 * 2
def baseEnd_4148462 : Nat := 1420103321941502238031051

theorem tailTrace_4148462 : CollatzResearch.WordTrace tailWord_4148462 prefixEnd_4148462 1420103321941502238031051 := by
  unfold tailWord_4148462
  simp only [CollatzResearch.WordTrace]
  refine ⟨18913354937104768718508955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100871226331225433165381093 18913354937104768718508955)
  ·
    refine ⟨28370032405657153077763433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18913354937104768718508955 28370032405657153077763433)
    ·
      refine ⟨21277524304242864808322575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28370032405657153077763433 21277524304242864808322575)
      ·
        refine ⟨31916286456364297212483863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21277524304242864808322575 31916286456364297212483863)
        ·
          refine ⟨47874429684546445818725795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31916286456364297212483863 47874429684546445818725795)
          ·
            refine ⟨71811644526819668728088693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47874429684546445818725795 71811644526819668728088693)
            ·
              refine ⟨6732341674389343943258315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71811644526819668728088693 6732341674389343943258315)
              ·
                refine ⟨10098512511584015914887473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6732341674389343943258315 10098512511584015914887473)
                ·
                  refine ⟨7573884383688011936165605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10098512511584015914887473 7573884383688011936165605)
                  ·
                    refine ⟨1420103321941502238031051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7573884383688011936165605 1420103321941502238031051)
                    ·
                      rfl

theorem cell22_4148462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_4148462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148462 prefixEnd_4148462 := by exact prefixLift 4148462
  have htrace : WordTrace (prefixWord ++ tailWord_4148462) baseStart_4148462 baseEnd_4148462 := by
    simpa [prefixWord, tailWord_4148462, baseEnd_4148462] using wordTrace_append hprefix tailTrace_4148462
  have hstable : (prefixWord ++ tailWord_4148462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148462).length < 2 ^ (prefixWord ++ tailWord_4148462).sum := by decide
  have hdescent : baseEnd_4148462 < baseStart_4148462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148468 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4148468 : Nat := 118140960795 + 4148468 * 2 ^ 59
def prefixEnd_4148468 : Nat := 4983230072969 + 3 ^ 40 * 4148468 * 2
def baseEnd_4148468 : Nat := 1420105375864120222381033

theorem tailTrace_4148468 : CollatzResearch.WordTrace tailWord_4148468 prefixEnd_4148468 1420105375864120222381033 := by
  unfold tailWord_4148468
  simp only [CollatzResearch.WordTrace]
  refine ⟨75653529167408206386395029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100871372223210941848526705 75653529167408206386395029)
  ·
    refine ⟨3546259179722259674362267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75653529167408206386395029 3546259179722259674362267)
    ·
      refine ⟨5319388769583389511543401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546259179722259674362267 5319388769583389511543401)
      ·
        refine ⟨3989541577187542133657551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5319388769583389511543401 3989541577187542133657551)
        ·
          refine ⟨5984312365781313200486327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3989541577187542133657551 5984312365781313200486327)
          ·
            refine ⟨8976468548671969800729491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984312365781313200486327 8976468548671969800729491)
            ·
              refine ⟨13464702823007954701094237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976468548671969800729491 13464702823007954701094237)
              ·
                refine ⟨5049263558627983012910339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13464702823007954701094237 5049263558627983012910339)
                ·
                  refine ⟨7573895337941974519365509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5049263558627983012910339 7573895337941974519365509)
                  ·
                    refine ⟨1420105375864120222381033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7573895337941974519365509 1420105375864120222381033)
                    ·
                      rfl

theorem cell22_4148468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4148468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148468 prefixEnd_4148468 := by exact prefixLift 4148468
  have htrace : WordTrace (prefixWord ++ tailWord_4148468) baseStart_4148468 baseEnd_4148468 := by
    simpa [prefixWord, tailWord_4148468, baseEnd_4148468] using wordTrace_append hprefix tailTrace_4148468
  have hstable : (prefixWord ++ tailWord_4148468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148468).length < 2 ^ (prefixWord ++ tailWord_4148468).sum := by decide
  have hdescent : baseEnd_4148468 < baseStart_4148468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148492 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 3, 3]
def baseStart_4148492 : Nat := 118140960795 + 4148492 * 2 ^ 59
def prefixEnd_4148492 : Nat := 4983230072969 + 3 ^ 40 * 4148492 * 2
def baseEnd_4148492 : Nat := 1420113591554592159780959

theorem tailTrace_4148492 : CollatzResearch.WordTrace tailWord_4148492 prefixEnd_4148492 1420113591554592159780959 := by
  unfold tailWord_4148492
  simp only [CollatzResearch.WordTrace]
  refine ⟨75653966843364732435831865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100871955791152976581109153 75653966843364732435831865)
  ·
    refine ⟨56740475132523549326873899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75653966843364732435831865 56740475132523549326873899)
    ·
      refine ⟨85110712698785323990310849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56740475132523549326873899 85110712698785323990310849)
      ·
        refine ⟨63833034524088992992733137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85110712698785323990310849 63833034524088992992733137)
        ·
          refine ⟨47874775893066744744549853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63833034524088992992733137 47874775893066744744549853)
          ·
            refine ⟨17953040959900029279206195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47874775893066744744549853 17953040959900029279206195)
            ·
              refine ⟨26929561439850043918809293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17953040959900029279206195 26929561439850043918809293)
              ·
                refine ⟨10098585539943766469553485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26929561439850043918809293 10098585539943766469553485)
                ·
                  refine ⟨3786969577478912426082557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10098585539943766469553485 3786969577478912426082557)
                  ·
                    refine ⟨1420113591554592159780959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786969577478912426082557 1420113591554592159780959)
                    ·
                      rfl

theorem cell22_4148492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_4148492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148492 prefixEnd_4148492 := by exact prefixLift 4148492
  have htrace : WordTrace (prefixWord ++ tailWord_4148492) baseStart_4148492 baseEnd_4148492 := by
    simpa [prefixWord, tailWord_4148492, baseEnd_4148492] using wordTrace_append hprefix tailTrace_4148492
  have hstable : (prefixWord ++ tailWord_4148492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148492).length < 2 ^ (prefixWord ++ tailWord_4148492).sum := by decide
  have hdescent : baseEnd_4148492 < baseStart_4148492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148498 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4148498 : Nat := 118140960795 + 4148498 * 2 ^ 59
def prefixEnd_4148498 : Nat := 4983230072969 + 3 ^ 40 * 4148498 * 2
def baseEnd_4148498 : Nat := 1420115645477210144130941

theorem tailTrace_4148498 : CollatzResearch.WordTrace tailWord_4148498 prefixEnd_4148498 1420115645477210144130941 := by
  unfold tailWord_4148498
  simp only [CollatzResearch.WordTrace]
  refine ⟨37827038131176931974095537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100872101683138485264254765 37827038131176931974095537)
  ·
    refine ⟨28370278598382698980571653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37827038131176931974095537 28370278598382698980571653)
    ·
      refine ⟨5319427237196756058857185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28370278598382698980571653 5319427237196756058857185)
      ·
        refine ⟨3989570427897567044142889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5319427237196756058857185 3989570427897567044142889)
        ·
          refine ⟨2992177820923175283107167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3989570427897567044142889 2992177820923175283107167)
          ·
            refine ⟨4488266731384762924660751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992177820923175283107167 4488266731384762924660751)
            ·
              refine ⟨6732400097077144386991127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4488266731384762924660751 6732400097077144386991127)
              ·
                refine ⟨10098600145615716580486691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6732400097077144386991127 10098600145615716580486691)
                ·
                  refine ⟨15147900218423574870730037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10098600145615716580486691 15147900218423574870730037)
                  ·
                    refine ⟨1420115645477210144130941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15147900218423574870730037 1420115645477210144130941)
                    ·
                      rfl

theorem cell22_4148498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4148498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148498 prefixEnd_4148498 := by exact prefixLift 4148498
  have htrace : WordTrace (prefixWord ++ tailWord_4148498) baseStart_4148498 baseEnd_4148498 := by
    simpa [prefixWord, tailWord_4148498, baseEnd_4148498] using wordTrace_append hprefix tailTrace_4148498
  have hstable : (prefixWord ++ tailWord_4148498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148498).length < 2 ^ (prefixWord ++ tailWord_4148498).sum := by decide
  have hdescent : baseEnd_4148498 < baseStart_4148498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148509 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_4148509 : Nat := 118140960795 + 4148509 * 2 ^ 59
def prefixEnd_4148509 : Nat := 4983230072969 + 3 ^ 40 * 4148509 * 2
def baseEnd_4148509 : Nat := 1420119411002009782105907

theorem tailTrace_4148509 : CollatzResearch.WordTrace tailWord_4148509 prefixEnd_4148509 1420119411002009782105907 := by
  unfold tailWord_4148509
  simp only [CollatzResearch.WordTrace]
  refine ⟨151308553727667876775032581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100872369151778584516688387 151308553727667876775032581)
  ·
    refine ⟨28370353823937726895318609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151308553727667876775032581 28370353823937726895318609)
    ·
      refine ⟨21277765367953295171488957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28370353823937726895318609 21277765367953295171488957)
      ·
        refine ⟨7979162012982485689308359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21277765367953295171488957 7979162012982485689308359)
        ·
          refine ⟨11968743019473728533962539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7979162012982485689308359 11968743019473728533962539)
          ·
            refine ⟨17953114529210592800943809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11968743019473728533962539 17953114529210592800943809)
            ·
              refine ⟨13464835896907944600707857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17953114529210592800943809 13464835896907944600707857)
              ·
                refine ⟨10098626922680958450530893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13464835896907944600707857 10098626922680958450530893)
                ·
                  refine ⟨3786985096005359418949085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10098626922680958450530893 3786985096005359418949085)
                  ·
                    refine ⟨1420119411002009782105907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786985096005359418949085 1420119411002009782105907)
                    ·
                      rfl

theorem cell22_4148509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_4148509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148509 prefixEnd_4148509 := by exact prefixLift 4148509
  have htrace : WordTrace (prefixWord ++ tailWord_4148509) baseStart_4148509 baseEnd_4148509 := by
    simpa [prefixWord, tailWord_4148509, baseEnd_4148509] using wordTrace_append hprefix tailTrace_4148509
  have hstable : (prefixWord ++ tailWord_4148509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148509).length < 2 ^ (prefixWord ++ tailWord_4148509).sum := by decide
  have hdescent : baseEnd_4148509 < baseStart_4148509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148522 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_4148522 : Nat := 118140960795 + 4148522 * 2 ^ 59
def prefixEnd_4148522 : Nat := 4983230072969 + 3 ^ 40 * 4148522 * 2
def baseEnd_4148522 : Nat := 473374620389227360510289

theorem tailTrace_4148522 : CollatzResearch.WordTrace tailWord_4148522 prefixEnd_4148522 473374620389227360510289 := by
  unfold tailWord_4148522
  simp only [CollatzResearch.WordTrace]
  refine ⟨37827256969155194998813955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100872685251080519996837213 37827256969155194998813955)
  ·
    refine ⟨56740885453732792498220933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37827256969155194998813955 56740885453732792498220933)
    ·
      refine ⟨10638916022574898593416425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56740885453732792498220933 10638916022574898593416425)
      ·
        refine ⟨7979187016931173945062319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10638916022574898593416425 7979187016931173945062319)
        ·
          refine ⟨11968780525396760917593479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7979187016931173945062319 11968780525396760917593479)
          ·
            refine ⟨17953170788095141376390219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11968780525396760917593479 17953170788095141376390219)
            ·
              refine ⟨26929756182142712064585329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17953170788095141376390219 26929756182142712064585329)
              ·
                refine ⟨20197317136607034048438997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26929756182142712064585329 20197317136607034048438997)
                ·
                  refine ⟨473374620389227360510289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20197317136607034048438997 473374620389227360510289)
                  ·
                    rfl

theorem cell22_4148522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_4148522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148522 prefixEnd_4148522 := by exact prefixLift 4148522
  have htrace : WordTrace (prefixWord ++ tailWord_4148522) baseStart_4148522 baseEnd_4148522 := by
    simpa [prefixWord, tailWord_4148522, baseEnd_4148522] using wordTrace_append hprefix tailTrace_4148522
  have hstable : (prefixWord ++ tailWord_4148522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148522).length < 2 ^ (prefixWord ++ tailWord_4148522).sum := by decide
  have hdescent : baseEnd_4148522 < baseStart_4148522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148535 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 7, 4]
def baseStart_4148535 : Nat := 118140960795 + 4148535 * 2 ^ 59
def prefixEnd_4148535 : Nat := 4983230072969 + 3 ^ 40 * 4148535 * 2
def baseEnd_4148535 : Nat := 1420128311333354380955827

theorem tailTrace_4148535 : CollatzResearch.WordTrace tailWord_4148535 prefixEnd_4148535 1420128311333354380955827 := by
  unfold tailWord_4148535
  simp only [CollatzResearch.WordTrace]
  refine ⟨151309502025573683215479059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100873001350382455476986039 151309502025573683215479059)
  ·
    refine ⟨226964253038360524823218589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151309502025573683215479059 226964253038360524823218589)
    ·
      refine ⟨85111594889385196808706971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226964253038360524823218589 85111594889385196808706971)
      ·
        refine ⟨127667392334077795213060457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85111594889385196808706971 127667392334077795213060457)
        ·
          refine ⟨95750544250558346409795343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127667392334077795213060457 95750544250558346409795343)
          ·
            refine ⟨143625816375837519614693015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95750544250558346409795343 143625816375837519614693015)
            ·
              refine ⟨215438724563756279422039523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143625816375837519614693015 215438724563756279422039523)
              ·
                refine ⟨323158086845634419133059285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215438724563756279422039523 323158086845634419133059285)
                ·
                  refine ⟨7574017660444556698431077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 323158086845634419133059285 7574017660444556698431077)
                  ·
                    refine ⟨1420128311333354380955827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7574017660444556698431077 1420128311333354380955827)
                    ·
                      rfl

theorem cell22_4148535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_4148535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148535 prefixEnd_4148535 := by exact prefixLift 4148535
  have htrace : WordTrace (prefixWord ++ tailWord_4148535) baseStart_4148535 baseEnd_4148535 := by
    simpa [prefixWord, tailWord_4148535, baseEnd_4148535] using wordTrace_append hprefix tailTrace_4148535
  have hstable : (prefixWord ++ tailWord_4148535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148535).length < 2 ^ (prefixWord ++ tailWord_4148535).sum := by decide
  have hdescent : baseEnd_4148535 < baseStart_4148535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148599 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 2, 3]
def baseStart_4148599 : Nat := 118140960795 + 4148599 * 2 ^ 59
def prefixEnd_4148599 : Nat := 4983230072969 + 3 ^ 40 * 4148599 * 2
def baseEnd_4148599 : Nat := 1420150219841279547355631

theorem tailTrace_4148599 : CollatzResearch.WordTrace tailWord_4148599 prefixEnd_4148599 1420150219841279547355631 := by
  unfold tailWord_4148599
  simp only [CollatzResearch.WordTrace]
  refine ⟨151311836297341822145808851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100874557531561214763872567 151311836297341822145808851)
  ·
    refine ⟨226967754446012733218713277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151311836297341822145808851 226967754446012733218713277)
    ·
      refine ⟨85112907917254774957017479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226967754446012733218713277 85112907917254774957017479)
      ·
        refine ⟨127669361875882162435526219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85112907917254774957017479 127669361875882162435526219)
        ·
          refine ⟨191504042813823243653289329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127669361875882162435526219 191504042813823243653289329)
          ·
            refine ⟨143628032110367432739966997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191504042813823243653289329 143628032110367432739966997)
            ·
              refine ⟨6732564005173473409685953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143628032110367432739966997 6732564005173473409685953)
              ·
                refine ⟨5049423003880105057264465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6732564005173473409685953 5049423003880105057264465)
                ·
                  refine ⟨3787067252910078792948349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5049423003880105057264465 3787067252910078792948349)
                  ·
                    refine ⟨1420150219841279547355631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3787067252910078792948349 1420150219841279547355631)
                    ·
                      rfl

theorem cell22_4148599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_4148599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148599 prefixEnd_4148599 := by exact prefixLift 4148599
  have htrace : WordTrace (prefixWord ++ tailWord_4148599) baseStart_4148599 baseEnd_4148599 := by
    simpa [prefixWord, tailWord_4148599, baseEnd_4148599] using wordTrace_append hprefix tailTrace_4148599
  have hstable : (prefixWord ++ tailWord_4148599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148599).length < 2 ^ (prefixWord ++ tailWord_4148599).sum := by decide
  have hdescent : baseEnd_4148599 < baseStart_4148599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148612 : List Nat := [2, 3, 2, 1, 1, 3, 3, 7]
def baseStart_4148612 : Nat := 118140960795 + 4148612 * 2 ^ 59
def prefixEnd_4148612 : Nat := 4983230072969 + 3 ^ 40 * 4148612 * 2
def baseEnd_4148612 : Nat := 157794963334105760753399

theorem tailTrace_4148612 : CollatzResearch.WordTrace tailWord_4148612 prefixEnd_4148612 157794963334105760753399 := by
  unfold tailWord_4148612
  simp only [CollatzResearch.WordTrace]
  refine ⟨75656155223147362683016045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100874873630863150244021393 75656155223147362683016045)
  ·
    refine ⟨28371058208680261006131017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75656155223147362683016045 28371058208680261006131017)
    ·
      refine ⟨21278293656510195754598263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28371058208680261006131017 21278293656510195754598263)
      ·
        refine ⟨31917440484765293631897395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21278293656510195754598263 31917440484765293631897395)
        ·
          refine ⟨47876160727147940447846093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31917440484765293631897395 47876160727147940447846093)
          ·
            refine ⟨17953560272680477667942285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47876160727147940447846093 17953560272680477667942285)
            ·
              refine ⟨6732585102255179125478357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17953560272680477667942285 6732585102255179125478357)
              ·
                refine ⟨157794963334105760753399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6732585102255179125478357 157794963334105760753399)
                ·
                  rfl

theorem cell22_4148612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 7].length) (baseStart_4148612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148612 prefixEnd_4148612 := by exact prefixLift 4148612
  have htrace : WordTrace (prefixWord ++ tailWord_4148612) baseStart_4148612 baseEnd_4148612 := by
    simpa [prefixWord, tailWord_4148612, baseEnd_4148612] using wordTrace_append hprefix tailTrace_4148612
  have hstable : (prefixWord ++ tailWord_4148612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148612).length < 2 ^ (prefixWord ++ tailWord_4148612).sum := by decide
  have hdescent : baseEnd_4148612 < baseStart_4148612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148657 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 7]
def baseStart_4148657 : Nat := 118140960795 + 4148657 * 2 ^ 59
def prefixEnd_4148657 : Nat := 4983230072969 + 3 ^ 40 * 4148657 * 2
def baseEnd_4148657 : Nat := 473390024808862243135151

theorem tailTrace_4148657 : CollatzResearch.WordTrace tailWord_4148657 prefixEnd_4148657 473390024808862243135151 := by
  unfold tailWord_4148657
  simp only [CollatzResearch.WordTrace]
  refine ⟨151313951731131698051420225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100875967820754465367613483 151313951731131698051420225)
  ·
    refine ⟨113485463798348773538565169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151313951731131698051420225 113485463798348773538565169)
    ·
      refine ⟨85114097848761580153923877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113485463798348773538565169 85114097848761580153923877)
      ·
        refine ⟨15958893346642796278860727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85114097848761580153923877 15958893346642796278860727)
        ·
          refine ⟨23938340019964194418291091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15958893346642796278860727 23938340019964194418291091)
          ·
            refine ⟨35907510029946291627436637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23938340019964194418291091 35907510029946291627436637)
            ·
              refine ⟨13465316261229859360288739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35907510029946291627436637 13465316261229859360288739)
              ·
                refine ⟨20197974391844789040433109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13465316261229859360288739 20197974391844789040433109)
                ·
                  refine ⟨473390024808862243135151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20197974391844789040433109 473390024808862243135151)
                  ·
                    rfl

theorem cell22_4148657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_4148657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148657 prefixEnd_4148657 := by exact prefixLift 4148657
  have htrace : WordTrace (prefixWord ++ tailWord_4148657) baseStart_4148657 baseEnd_4148657 := by
    simpa [prefixWord, tailWord_4148657, baseEnd_4148657] using wordTrace_append hprefix tailTrace_4148657
  have hstable : (prefixWord ++ tailWord_4148657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148657).length < 2 ^ (prefixWord ++ tailWord_4148657).sum := by decide
  have hdescent : baseEnd_4148657 < baseStart_4148657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148661 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 3, 3]
def baseStart_4148661 : Nat := 118140960795 + 4148661 * 2 ^ 59
def prefixEnd_4148661 : Nat := 4983230072969 + 3 ^ 40 * 4148661 * 2
def baseEnd_4148661 : Nat := 1420171443708332052305441

theorem tailTrace_4148661 : CollatzResearch.WordTrace tailWord_4148661 prefixEnd_4148661 1420171443708332052305441 := by
  unfold tailWord_4148661
  simp only [CollatzResearch.WordTrace]
  refine ⟨151314097623117206734565837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100876065082078137823043891 151314097623117206734565837)
  ·
    refine ⟨56742786608668952525462189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151314097623117206734565837 56742786608668952525462189)
    ·
      refine ⟨21278544978250857197048321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56742786608668952525462189 21278544978250857197048321)
      ·
        refine ⟨15958908733688142897786241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21278544978250857197048321 15958908733688142897786241)
        ·
          refine ⟨11969181550266107173339681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15958908733688142897786241 11969181550266107173339681)
          ·
            refine ⟨8976886162699580380004761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11969181550266107173339681 8976886162699580380004761)
            ·
              refine ⟨6732664622024685285003571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8976886162699580380004761 6732664622024685285003571)
              ·
                refine ⟨10098996933037027927505357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6732664622024685285003571 10098996933037027927505357)
                ·
                  refine ⟨3787123849888885472814509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10098996933037027927505357 3787123849888885472814509)
                  ·
                    refine ⟨1420171443708332052305441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3787123849888885472814509 1420171443708332052305441)
                    ·
                      rfl

theorem cell22_4148661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_4148661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148661 prefixEnd_4148661 := by exact prefixLift 4148661
  have htrace : WordTrace (prefixWord ++ tailWord_4148661) baseStart_4148661 baseEnd_4148661 := by
    simpa [prefixWord, tailWord_4148661, baseEnd_4148661] using wordTrace_append hprefix tailTrace_4148661
  have hstable : (prefixWord ++ tailWord_4148661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148661).length < 2 ^ (prefixWord ++ tailWord_4148661).sum := by decide
  have hdescent : baseEnd_4148661 < baseStart_4148661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148672 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_4148672 : Nat := 118140960795 + 4148672 * 2 ^ 59
def prefixEnd_4148672 : Nat := 4983230072969 + 3 ^ 40 * 4148672 * 2
def baseEnd_4148672 : Nat := 1420175209233131690280407

theorem tailTrace_4148672 : CollatzResearch.WordTrace tailWord_4148672 prefixEnd_4148672 1420175209233131690280407 := by
  unfold tailWord_4148672
  simp only [CollatzResearch.WordTrace]
  refine ⟨75657249413038677806608135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100876332550718237075477513 75657249413038677806608135)
  ·
    refine ⟨113485874119558016709912203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75657249413038677806608135 113485874119558016709912203)
    ·
      refine ⟨170228811179337025064868305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113485874119558016709912203 170228811179337025064868305)
      ·
        refine ⟨127671608384502768798651229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170228811179337025064868305 127671608384502768798651229)
        ·
          refine ⟨47876853144188538299494211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127671608384502768798651229 47876853144188538299494211)
          ·
            refine ⟨71815279716282807449241317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47876853144188538299494211 71815279716282807449241317)
            ·
              refine ⟨13465364946803026396732747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71815279716282807449241317 13465364946803026396732747)
              ·
                refine ⟨20198047420204539595099121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13465364946803026396732747 20198047420204539595099121)
                ·
                  refine ⟨15148535565153404696324341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20198047420204539595099121 15148535565153404696324341)
                  ·
                    refine ⟨1420175209233131690280407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15148535565153404696324341 1420175209233131690280407)
                    ·
                      rfl

theorem cell22_4148672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_4148672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148672 prefixEnd_4148672 := by exact prefixLift 4148672
  have htrace : WordTrace (prefixWord ++ tailWord_4148672) baseStart_4148672 baseEnd_4148672 := by
    simpa [prefixWord, tailWord_4148672, baseEnd_4148672] using wordTrace_append hprefix tailTrace_4148672
  have hstable : (prefixWord ++ tailWord_4148672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148672).length < 2 ^ (prefixWord ++ tailWord_4148672).sum := by decide
  have hdescent : baseEnd_4148672 < baseStart_4148672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148687 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 3, 4]
def baseStart_4148687 : Nat := 118140960795 + 4148687 * 2 ^ 59
def prefixEnd_4148687 : Nat := 4983230072969 + 3 ^ 40 * 4148687 * 2
def baseEnd_4148687 : Nat := 1420180344039676651155361

theorem tailTrace_4148687 : CollatzResearch.WordTrace tailWord_4148687 prefixEnd_4148687 1420180344039676651155361 := by
  unfold tailWord_4148687
  simp only [CollatzResearch.WordTrace]
  refine ⟨151315045921023013175012315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100876697280682008783341543 151315045921023013175012315)
  ·
    refine ⟨226972568881534519762518473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151315045921023013175012315 226972568881534519762518473)
    ·
      refine ⟨170229426661150889821888855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226972568881534519762518473 170229426661150889821888855)
      ·
        refine ⟨255344139991726334732833283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170229426661150889821888855 255344139991726334732833283)
        ·
          refine ⟨383016209987589502099249925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255344139991726334732833283 383016209987589502099249925)
          ·
            refine ⟨71815539372673031643609361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383016209987589502099249925 71815539372673031643609361)
            ·
              refine ⟨53861654529504773732707021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71815539372673031643609361 53861654529504773732707021)
              ·
                refine ⟨20198120448564290149765133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53861654529504773732707021 20198120448564290149765133)
                ·
                  refine ⟨7574295168211608806161925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20198120448564290149765133 7574295168211608806161925)
                  ·
                    refine ⟨1420180344039676651155361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7574295168211608806161925 1420180344039676651155361)
                    ·
                      rfl

theorem cell22_4148687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_4148687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148687 prefixEnd_4148687 := by exact prefixLift 4148687
  have htrace : WordTrace (prefixWord ++ tailWord_4148687) baseStart_4148687 baseEnd_4148687 := by
    simpa [prefixWord, tailWord_4148687, baseEnd_4148687] using wordTrace_append hprefix tailTrace_4148687
  have hstable : (prefixWord ++ tailWord_4148687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148687).length < 2 ^ (prefixWord ++ tailWord_4148687).sum := by decide
  have hdescent : baseEnd_4148687 < baseStart_4148687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148719 : List Nat := [1, 1, 2, 1, 4, 1, 2, 6, 4]
def baseStart_4148719 : Nat := 118140960795 + 4148719 * 2 ^ 59
def prefixEnd_4148719 : Nat := 4983230072969 + 3 ^ 40 * 4148719 * 2
def baseEnd_4148719 : Nat := 473397099431213078118421

theorem tailTrace_4148719 : CollatzResearch.WordTrace tailWord_4148719 prefixEnd_4148719 473397099431213078118421 := by
  unfold tailWord_4148719
  simp only [CollatzResearch.WordTrace]
  refine ⟨151316213056907082640177211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100877475371271388426784807 151316213056907082640177211)
  ·
    refine ⟨226974319585360623960265817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151316213056907082640177211 226974319585360623960265817)
    ·
      refine ⟨170230739689020467970199363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226974319585360623960265817 170230739689020467970199363)
      ·
        refine ⟨255346109533530701955299045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170230739689020467970199363 255346109533530701955299045)
        ·
          refine ⟨47877395537537006616618571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255346109533530701955299045 47877395537537006616618571)
          ·
            refine ⟨71816093306305509924927857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47877395537537006616618571 71816093306305509924927857)
            ·
              refine ⟨53862069979729132443695893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71816093306305509924927857 53862069979729132443695893)
              ·
                refine ⟨2524784530299803083298245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53862069979729132443695893 2524784530299803083298245)
                ·
                  refine ⟨473397099431213078118421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2524784530299803083298245 473397099431213078118421)
                  ·
                    rfl

theorem cell22_4148719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 4].length) (baseStart_4148719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148719 prefixEnd_4148719 := by exact prefixLift 4148719
  have htrace : WordTrace (prefixWord ++ tailWord_4148719) baseStart_4148719 baseEnd_4148719 := by
    simpa [prefixWord, tailWord_4148719, baseEnd_4148719] using wordTrace_append hprefix tailTrace_4148719
  have hstable : (prefixWord ++ tailWord_4148719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148719).length < 2 ^ (prefixWord ++ tailWord_4148719).sum := by decide
  have hdescent : baseEnd_4148719 < baseStart_4148719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148732 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_4148732 : Nat := 118140960795 + 4148732 * 2 ^ 59
def prefixEnd_4148732 : Nat := 4983230072969 + 3 ^ 40 * 4148732 * 2
def baseEnd_4148732 : Nat := 1420195748459311533780223

theorem tailTrace_4148732 : CollatzResearch.WordTrace tailWord_4148732 prefixEnd_4148732 1420195748459311533780223 := by
  unfold tailWord_4148732
  simp only [CollatzResearch.WordTrace]
  refine ⟨75658343602929992930200225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100877791470573323906933633 75658343602929992930200225)
  ·
    refine ⟨56743757702197494697650169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75658343602929992930200225 56743757702197494697650169)
    ·
      refine ⟨42557818276648121023237627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56743757702197494697650169 42557818276648121023237627)
      ·
        refine ⟨63836727414972181534856441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42557818276648121023237627 63836727414972181534856441)
        ·
          refine ⟨47877545561229136151142331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63836727414972181534856441 47877545561229136151142331)
          ·
            refine ⟨71816318341843704226713497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47877545561229136151142331 71816318341843704226713497)
            ·
              refine ⟨53862238756382778170035123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71816318341843704226713497 53862238756382778170035123)
              ·
                refine ⟨80793358134574167255052685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53862238756382778170035123 80793358134574167255052685)
                ·
                  refine ⟨30297509300465312720644757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80793358134574167255052685 30297509300465312720644757)
                  ·
                    refine ⟨1420195748459311533780223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30297509300465312720644757 1420195748459311533780223)
                    ·
                      rfl

theorem cell22_4148732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_4148732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148732 prefixEnd_4148732 := by exact prefixLift 4148732
  have htrace : WordTrace (prefixWord ++ tailWord_4148732) baseStart_4148732 baseEnd_4148732 := by
    simpa [prefixWord, tailWord_4148732, baseEnd_4148732] using wordTrace_append hprefix tailTrace_4148732
  have hstable : (prefixWord ++ tailWord_4148732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148732).length < 2 ^ (prefixWord ++ tailWord_4148732).sum := by decide
  have hdescent : baseEnd_4148732 < baseStart_4148732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148738 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4148738 : Nat := 118140960795 + 4148738 * 2 ^ 59
def prefixEnd_4148738 : Nat := 4983230072969 + 3 ^ 40 * 4148738 * 2
def baseEnd_4148738 : Nat := 1420197802381929518130205

theorem tailTrace_4148738 : CollatzResearch.WordTrace tailWord_4148738 prefixEnd_4148738 1420197802381929518130205 := by
  unfold tailWord_4148738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37829226510959562221279717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100877937362558832590079245 37829226510959562221279717)
  ·
    refine ⟨7092979970804917916489947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37829226510959562221279717 7092979970804917916489947)
    ·
      refine ⟨10639469956207376874734921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7092979970804917916489947 10639469956207376874734921)
      ·
        refine ⟨7979602467155532656051191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10639469956207376874734921 7979602467155532656051191)
        ·
          refine ⟨11969403700733298984076787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7979602467155532656051191 11969403700733298984076787)
          ·
            refine ⟨17954105551099948476115181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11969403700733298984076787 17954105551099948476115181)
            ·
              refine ⟨6732789581662480678543193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17954105551099948476115181 6732789581662480678543193)
              ·
                refine ⟨5049592186246860508907395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6732789581662480678543193 5049592186246860508907395)
                ·
                  refine ⟨7574388279370290763361093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5049592186246860508907395 7574388279370290763361093)
                  ·
                    refine ⟨1420197802381929518130205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7574388279370290763361093 1420197802381929518130205)
                    ·
                      rfl

theorem cell22_4148738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4148738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148738 prefixEnd_4148738 := by exact prefixLift 4148738
  have htrace : WordTrace (prefixWord ++ tailWord_4148738) baseStart_4148738 baseEnd_4148738 := by
    simpa [prefixWord, tailWord_4148738, baseEnd_4148738] using wordTrace_append hprefix tailTrace_4148738
  have hstable : (prefixWord ++ tailWord_4148738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148738).length < 2 ^ (prefixWord ++ tailWord_4148738).sum := by decide
  have hdescent : baseEnd_4148738 < baseStart_4148738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148768 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 2, 3]
def baseStart_4148768 : Nat := 118140960795 + 4148768 * 2 ^ 59
def prefixEnd_4148768 : Nat := 4983230072969 + 3 ^ 40 * 4148768 * 2
def baseEnd_4148768 : Nat := 1420208071995019439880113

theorem tailTrace_4148768 : CollatzResearch.WordTrace tailWord_4148768 prefixEnd_4148768 1420208071995019439880113 := by
  unfold tailWord_4148768
  simp only [CollatzResearch.WordTrace]
  refine ⟨75659000116864782004355479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100878666822486376005807305 75659000116864782004355479)
  ·
    refine ⟨113488500175297173006533219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75659000116864782004355479 113488500175297173006533219)
    ·
      refine ⟨170232750262945759509799829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113488500175297173006533219 170232750262945759509799829)
      ·
        refine ⟨7979660168575582477021867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170232750262945759509799829 7979660168575582477021867)
        ·
          refine ⟨11969490252863373715532801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7979660168575582477021867 11969490252863373715532801)
          ·
            refine ⟨8977117689647530286649601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11969490252863373715532801 8977117689647530286649601)
            ·
              refine ⟨6732838267235647714987201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8977117689647530286649601 6732838267235647714987201)
              ·
                refine ⟨5049628700426735786240401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6732838267235647714987201 5049628700426735786240401)
                ·
                  refine ⟨3787221525320051839680301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5049628700426735786240401 3787221525320051839680301)
                  ·
                    refine ⟨1420208071995019439880113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3787221525320051839680301 1420208071995019439880113)
                    ·
                      rfl

theorem cell22_4148768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2, 3].length) (baseStart_4148768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148768 prefixEnd_4148768 := by exact prefixLift 4148768
  have htrace : WordTrace (prefixWord ++ tailWord_4148768) baseStart_4148768 baseEnd_4148768 := by
    simpa [prefixWord, tailWord_4148768, baseEnd_4148768] using wordTrace_append hprefix tailTrace_4148768
  have hstable : (prefixWord ++ tailWord_4148768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148768).length < 2 ^ (prefixWord ++ tailWord_4148768).sum := by decide
  have hdescent : baseEnd_4148768 < baseStart_4148768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148839 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 5, 4]
def baseStart_4148839 : Nat := 118140960795 + 4148839 * 2 ^ 59
def prefixEnd_4148839 : Nat := 4983230072969 + 3 ^ 40 * 4148839 * 2
def baseEnd_4148839 : Nat := 1420232376745998921354895

theorem tailTrace_4148839 : CollatzResearch.WordTrace tailWord_4148839 prefixEnd_4148839 1420232376745998921354895 := by
  unfold tailWord_4148839
  simp only [CollatzResearch.WordTrace]
  refine ⟨151320589816472343134545571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100880393210981562089697047 151320589816472343134545571)
  ·
    refine ⟨226980884724708514701818357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151320589816472343134545571 226980884724708514701818357)
    ·
      refine ⟨21279457942941423253295471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226980884724708514701818357 21279457942941423253295471)
      ·
        refine ⟨31919186914412134879943207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21279457942941423253295471 31919186914412134879943207)
        ·
          refine ⟨47878780371618202319914811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31919186914412134879943207 47878780371618202319914811)
          ·
            refine ⟨71818170557427303479872217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47878780371618202319914811 71818170557427303479872217)
            ·
              refine ⟨53863627918070477609904163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71818170557427303479872217 53863627918070477609904163)
              ·
                refine ⟨80795441877105716414856245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53863627918070477609904163 80795441877105716414856245)
                ·
                  refine ⟨7574572675978660913892773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80795441877105716414856245 7574572675978660913892773)
                  ·
                    refine ⟨1420232376745998921354895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7574572675978660913892773 1420232376745998921354895)
                    ·
                      rfl

theorem cell22_4148839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_4148839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148839 prefixEnd_4148839 := by exact prefixLift 4148839
  have htrace : WordTrace (prefixWord ++ tailWord_4148839) baseStart_4148839 baseEnd_4148839 := by
    simpa [prefixWord, tailWord_4148839, baseEnd_4148839] using wordTrace_append hprefix tailTrace_4148839
  have hstable : (prefixWord ++ tailWord_4148839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148839).length < 2 ^ (prefixWord ++ tailWord_4148839).sum := by decide
  have hdescent : baseEnd_4148839 < baseStart_4148839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148869 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_4148869 : Nat := 118140960795 + 4148869 * 2 ^ 59
def prefixEnd_4148869 : Nat := 4983230072969 + 3 ^ 40 * 4148869 * 2
def baseEnd_4148869 : Nat := 1420242646359088843104803

theorem tailTrace_4148869 : CollatzResearch.WordTrace tailWord_4148869 prefixEnd_4148869 1420242646359088843104803 := by
  unfold tailWord_4148869
  simp only [CollatzResearch.WordTrace]
  refine ⟨151321684006363658258137661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100881122670909105505425107 151321684006363658258137661)
  ·
    refine ⟨56745631502386371846801623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151321684006363658258137661 56745631502386371846801623)
    ·
      refine ⟨85118447253579557770202435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56745631502386371846801623 85118447253579557770202435)
      ·
        refine ⟨127677670880369336655303653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85118447253579557770202435 127677670880369336655303653)
        ·
          refine ⟨23939563290069250622869435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127677670880369336655303653 23939563290069250622869435)
          ·
            refine ⟨35909344935103875934304153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23939563290069250622869435 35909344935103875934304153)
            ·
              refine ⟨26932008701327906950728115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35909344935103875934304153 26932008701327906950728115)
              ·
                refine ⟨40398013051991860426092173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26932008701327906950728115 40398013051991860426092173)
                ·
                  refine ⟨15149254894496947659784565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40398013051991860426092173 15149254894496947659784565)
                  ·
                    refine ⟨1420242646359088843104803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15149254894496947659784565 1420242646359088843104803)
                    ·
                      rfl

theorem cell22_4148869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_4148869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148869 prefixEnd_4148869 := by exact prefixLift 4148869
  have htrace : WordTrace (prefixWord ++ tailWord_4148869) baseStart_4148869 baseEnd_4148869 := by
    simpa [prefixWord, tailWord_4148869, baseEnd_4148869] using wordTrace_append hprefix tailTrace_4148869
  have hstable : (prefixWord ++ tailWord_4148869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148869).length < 2 ^ (prefixWord ++ tailWord_4148869).sum := by decide
  have hdescent : baseEnd_4148869 < baseStart_4148869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148899 : List Nat := [1, 1, 1, 4, 1, 1, 6, 7]
def baseStart_4148899 : Nat := 118140960795 + 4148899 * 2 ^ 59
def prefixEnd_4148899 : Nat := 4983230072969 + 3 ^ 40 * 4148899 * 2
def baseEnd_4148899 : Nat := 157805879552464307206079

theorem tailTrace_4148899 : CollatzResearch.WordTrace tailWord_4148899 prefixEnd_4148899 157805879552464307206079 := by
  unfold tailWord_4148899
  simp only [CollatzResearch.WordTrace]
  refine ⟨151322778196254973381729751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100881852130836648921153167 151322778196254973381729751)
  ·
    refine ⟨226984167294382460072594627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151322778196254973381729751 226984167294382460072594627)
    ·
      refine ⟨340476250941573690108891941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226984167294382460072594627 340476250941573690108891941)
      ·
        refine ⟨63839297051545066895417239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340476250941573690108891941 63839297051545066895417239)
        ·
          refine ⟨95758945577317600343125859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63839297051545066895417239 95758945577317600343125859)
          ·
            refine ⟨143638418365976400514688789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95758945577317600343125859 143638418365976400514688789)
            ·
              refine ⟨6733050860905143774126037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143638418365976400514688789 6733050860905143774126037)
              ·
                refine ⟨157805879552464307206079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6733050860905143774126037 157805879552464307206079)
                ·
                  rfl

theorem cell22_4148899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 7].length) (baseStart_4148899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148899 prefixEnd_4148899 := by exact prefixLift 4148899
  have htrace : WordTrace (prefixWord ++ tailWord_4148899) baseStart_4148899 baseEnd_4148899 := by
    simpa [prefixWord, tailWord_4148899, baseEnd_4148899] using wordTrace_append hprefix tailTrace_4148899
  have hstable : (prefixWord ++ tailWord_4148899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148899).length < 2 ^ (prefixWord ++ tailWord_4148899).sum := by decide
  have hdescent : baseEnd_4148899 < baseStart_4148899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148914 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_4148914 : Nat := 118140960795 + 4148914 * 2 ^ 59
def prefixEnd_4148914 : Nat := 4983230072969 + 3 ^ 40 * 4148914 * 2
def baseEnd_4148914 : Nat := 1420258050778723725729665

theorem tailTrace_4148914 : CollatzResearch.WordTrace tailWord_4148914 prefixEnd_4148914 1420258050778723725729665 := by
  unfold tailWord_4148914
  simp only [CollatzResearch.WordTrace]
  refine ⟨37830831322800157735881449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100882216860800420629017197 37830831322800157735881449)
  ·
    refine ⟨28373123492100118301911087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37830831322800157735881449 28373123492100118301911087)
    ·
      refine ⟨42559685238150177452866631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28373123492100118301911087 42559685238150177452866631)
      ·
        refine ⟨63839527857225266179299947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42559685238150177452866631 63839527857225266179299947)
        ·
          refine ⟨95759291785837899268949921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63839527857225266179299947 95759291785837899268949921)
          ·
            refine ⟨71819468839378424451712441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95759291785837899268949921 71819468839378424451712441)
            ·
              refine ⟨53864601629533818338784331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71819468839378424451712441 53864601629533818338784331)
              ·
                refine ⟨80796902444300727508176497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53864601629533818338784331 80796902444300727508176497)
                ·
                  refine ⟨60597676833225545631132373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80796902444300727508176497 60597676833225545631132373)
                  ·
                    refine ⟨1420258050778723725729665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60597676833225545631132373 1420258050778723725729665)
                    ·
                      rfl

theorem cell22_4148914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_4148914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148914 prefixEnd_4148914 := by exact prefixLift 4148914
  have htrace : WordTrace (prefixWord ++ tailWord_4148914) baseStart_4148914 baseEnd_4148914 := by
    simpa [prefixWord, tailWord_4148914, baseEnd_4148914] using wordTrace_append hprefix tailTrace_4148914
  have hstable : (prefixWord ++ tailWord_4148914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148914).length < 2 ^ (prefixWord ++ tailWord_4148914).sum := by decide
  have hdescent : baseEnd_4148914 < baseStart_4148914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148946 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_4148946 : Nat := 118140960795 + 4148946 * 2 ^ 59
def prefixEnd_4148946 : Nat := 4983230072969 + 3 ^ 40 * 4148946 * 2
def baseEnd_4148946 : Nat := 1420269005032686308929567

theorem tailTrace_4148946 : CollatzResearch.WordTrace tailWord_4148946 prefixEnd_4148946 1420269005032686308929567 := by
  unfold tailWord_4148946
  simp only [CollatzResearch.WordTrace]
  refine ⟨37831123106771175102172673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100882994951389800272460461 37831123106771175102172673)
  ·
    refine ⟨28373342330078381326629505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37831123106771175102172673 28373342330078381326629505)
    ·
      refine ⟨21280006747558785994972129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28373342330078381326629505 21280006747558785994972129)
      ·
        refine ⟨15960005060669089496229097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21280006747558785994972129 15960005060669089496229097)
        ·
          refine ⟨11970003795501817122171823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15960005060669089496229097 11970003795501817122171823)
          ·
            refine ⟨17955005693252725683257735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970003795501817122171823 17955005693252725683257735)
            ·
              refine ⟨26932508539879088524886603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17955005693252725683257735 26932508539879088524886603)
              ·
                refine ⟨40398762809818632787329905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26932508539879088524886603 40398762809818632787329905)
                ·
                  refine ⟨30299072107363974590497429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40398762809818632787329905 30299072107363974590497429)
                  ·
                    refine ⟨1420269005032686308929567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30299072107363974590497429 1420269005032686308929567)
                    ·
                      rfl

theorem cell22_4148946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_4148946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148946 prefixEnd_4148946 := by exact prefixLift 4148946
  have htrace : WordTrace (prefixWord ++ tailWord_4148946) baseStart_4148946 baseEnd_4148946 := by
    simpa [prefixWord, tailWord_4148946, baseEnd_4148946] using wordTrace_append hprefix tailTrace_4148946
  have hstable : (prefixWord ++ tailWord_4148946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148946).length < 2 ^ (prefixWord ++ tailWord_4148946).sum := by decide
  have hdescent : baseEnd_4148946 < baseStart_4148946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148982 : List Nat := [5, 1, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_4148982 : Nat := 118140960795 + 4148982 * 2 ^ 59
def prefixEnd_4148982 : Nat := 4983230072969 + 3 ^ 40 * 4148982 * 2
def baseEnd_4148982 : Nat := 1420281328568394215029457

theorem tailTrace_4148982 : CollatzResearch.WordTrace tailWord_4148982 prefixEnd_4148982 1420281328568394215029457 := by
  unfold tailWord_4148982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9457862840934642409812575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100883870303302852371334133 9457862840934642409812575)
  ·
    refine ⟨14186794261401963614718863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9457862840934642409812575 14186794261401963614718863)
    ·
      refine ⟨21280191392102945422078295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14186794261401963614718863 21280191392102945422078295)
      ·
        refine ⟨31920287088154418133117443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21280191392102945422078295 31920287088154418133117443)
        ·
          refine ⟨47880430632231627199676165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31920287088154418133117443 47880430632231627199676165)
          ·
            refine ⟨8977580743543430099939281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47880430632231627199676165 8977580743543430099939281)
            ·
              refine ⟨6733185557657572574954461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8977580743543430099939281 6733185557657572574954461)
              ·
                refine ⟨2524944584121589715607923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6733185557657572574954461 2524944584121589715607923)
                ·
                  refine ⟨3787416876182384573411885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524944584121589715607923 3787416876182384573411885)
                  ·
                    refine ⟨1420281328568394215029457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3787416876182384573411885 1420281328568394215029457)
                    ·
                      rfl

theorem cell22_4148982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_4148982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4148982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4148982 prefixEnd_4148982 := by exact prefixLift 4148982
  have htrace : WordTrace (prefixWord ++ tailWord_4148982) baseStart_4148982 baseEnd_4148982 := by
    simpa [prefixWord, tailWord_4148982, baseEnd_4148982] using wordTrace_append hprefix tailTrace_4148982
  have hstable : (prefixWord ++ tailWord_4148982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148982).length < 2 ^ (prefixWord ++ tailWord_4148982).sum := by decide
  have hdescent : baseEnd_4148982 < baseStart_4148982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149006 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_4149006 : Nat := 118140960795 + 4149006 * 2 ^ 59
def prefixEnd_4149006 : Nat := 4983230072969 + 3 ^ 40 * 4149006 * 2
def baseEnd_4149006 : Nat := 473429848086288717476461

theorem tailTrace_4149006 : CollatzResearch.WordTrace tailWord_4149006 prefixEnd_4149006 473429848086288717476461 := by
  unfold tailWord_4149006
  simp only [CollatzResearch.WordTrace]
  refine ⟨18915835100858416331984359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100884453871244887103916581 18915835100858416331984359)
  ·
    refine ⟨28373752651287624497976539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18915835100858416331984359 28373752651287624497976539)
    ·
      refine ⟨42560628976931436746964809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28373752651287624497976539 42560628976931436746964809)
      ·
        refine ⟨31920471732698577560223607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42560628976931436746964809 31920471732698577560223607)
        ·
          refine ⟨47880707599047866340335411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31920471732698577560223607 47880707599047866340335411)
          ·
            refine ⟨71821061398571799510503117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47880707599047866340335411 71821061398571799510503117)
            ·
              refine ⟨26932898024464424816438669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71821061398571799510503117 26932898024464424816438669)
              ·
                refine ⟨10099836759174159306164501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26932898024464424816438669 10099836759174159306164501)
                ·
                  refine ⟨473429848086288717476461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10099836759174159306164501 473429848086288717476461)
                  ·
                    rfl

theorem cell22_4149006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_4149006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149006 prefixEnd_4149006 := by exact prefixLift 4149006
  have htrace : WordTrace (prefixWord ++ tailWord_4149006) baseStart_4149006 baseEnd_4149006 := by
    simpa [prefixWord, tailWord_4149006, baseEnd_4149006] using wordTrace_append hprefix tailTrace_4149006
  have hstable : (prefixWord ++ tailWord_4149006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149006).length < 2 ^ (prefixWord ++ tailWord_4149006).sum := by decide
  have hdescent : baseEnd_4149006 < baseStart_4149006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149036 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_4149036 : Nat := 118140960795 + 4149036 * 2 ^ 59
def prefixEnd_4149036 : Nat := 4983230072969 + 3 ^ 40 * 4149036 * 2
def baseEnd_4149036 : Nat := 1420299813871956074179291

theorem tailTrace_4149036 : CollatzResearch.WordTrace tailWord_4149036 prefixEnd_4149036 1420299813871956074179291 := by
  unfold tailWord_4149036
  simp only [CollatzResearch.WordTrace]
  refine ⟨75663887498379322889733481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100885183331172430519644641 75663887498379322889733481)
  ·
    refine ⟨56747915623784492167300111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75663887498379322889733481 56747915623784492167300111)
    ·
      refine ⟨85121873435676738250950167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56747915623784492167300111 85121873435676738250950167)
      ·
        refine ⟨127682810153515107376425251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85121873435676738250950167 127682810153515107376425251)
        ·
          refine ⟨191524215230272661064637877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127682810153515107376425251 191524215230272661064637877)
          ·
            refine ⟨17955395177838061974809801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191524215230272661064637877 17955395177838061974809801)
            ·
              refine ⟨13466546383378546481107351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17955395177838061974809801 13466546383378546481107351)
              ·
                refine ⟨20199819575067819721661027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13466546383378546481107351 20199819575067819721661027)
                ·
                  refine ⟨30299729362601729582491541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20199819575067819721661027 30299729362601729582491541)
                  ·
                    refine ⟨1420299813871956074179291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30299729362601729582491541 1420299813871956074179291)
                    ·
                      rfl

theorem cell22_4149036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_4149036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149036 prefixEnd_4149036 := by exact prefixLift 4149036
  have htrace : WordTrace (prefixWord ++ tailWord_4149036) baseStart_4149036 baseEnd_4149036 := by
    simpa [prefixWord, tailWord_4149036, baseEnd_4149036] using wordTrace_append hprefix tailTrace_4149036
  have hstable : (prefixWord ++ tailWord_4149036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149036).length < 2 ^ (prefixWord ++ tailWord_4149036).sum := by decide
  have hdescent : baseEnd_4149036 < baseStart_4149036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149053 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_4149053 : Nat := 118140960795 + 4149053 * 2 ^ 59
def prefixEnd_4149053 : Nat := 4983230072969 + 3 ^ 40 * 4149053 * 2
def baseEnd_4149053 : Nat := 1420305633319373696504239

theorem tailTrace_4149053 : CollatzResearch.WordTrace tailWord_4149053 prefixEnd_4149053 1420305633319373696504239 := by
  unfold tailWord_4149053
  simp only [CollatzResearch.WordTrace]
  refine ⟨151328395037697057682835813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100885596691798038455223875 151328395037697057682835813)
  ·
    refine ⟨28374074069568198315531715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151328395037697057682835813 28374074069568198315531715)
    ·
      refine ⟨42561111104352297473297573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28374074069568198315531715 42561111104352297473297573)
      ·
        refine ⟨7980208332066055776243295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42561111104352297473297573 7980208332066055776243295)
        ·
          refine ⟨11970312498099083664364943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7980208332066055776243295 11970312498099083664364943)
          ·
            refine ⟨17955468747148625496547415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970312498099083664364943 17955468747148625496547415)
            ·
              refine ⟨26933203120722938244821123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17955468747148625496547415 26933203120722938244821123)
              ·
                refine ⟨40399804681084407367231685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26933203120722938244821123 40399804681084407367231685)
                ·
                  refine ⟨7574963377703326381355941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40399804681084407367231685 7574963377703326381355941)
                  ·
                    refine ⟨1420305633319373696504239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7574963377703326381355941 1420305633319373696504239)
                    ·
                      rfl

theorem cell22_4149053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_4149053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149053 prefixEnd_4149053 := by exact prefixLift 4149053
  have htrace : WordTrace (prefixWord ++ tailWord_4149053) baseStart_4149053 baseEnd_4149053 := by
    simpa [prefixWord, tailWord_4149053, baseEnd_4149053] using wordTrace_append hprefix tailTrace_4149053
  have hstable : (prefixWord ++ tailWord_4149053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149053).length < 2 ^ (prefixWord ++ tailWord_4149053).sum := by decide
  have hdescent : baseEnd_4149053 < baseStart_4149053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149068 : List Nat := [2, 2, 1, 3, 4, 1, 2, 7]
def baseStart_4149068 : Nat := 118140960795 + 4149068 * 2 ^ 59
def prefixEnd_4149068 : Nat := 4983230072969 + 3 ^ 40 * 4149068 * 2
def baseEnd_4149068 : Nat := 157812307569546517486577

theorem tailTrace_4149068 : CollatzResearch.WordTrace tailWord_4149068 prefixEnd_4149068 157812307569546517486577 := by
  unfold tailWord_4149068
  simp only [CollatzResearch.WordTrace]
  refine ⟨75664471066321357622315929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100885961421761810163087905 75664471066321357622315929)
  ·
    refine ⟨56748353299741018216736947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75664471066321357622315929 56748353299741018216736947)
    ·
      refine ⟨85122529949611527325105421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56748353299741018216736947 85122529949611527325105421)
      ·
        refine ⟨31920948731104322746914533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85122529949611527325105421 31920948731104322746914533)
        ·
          refine ⟨5985177887082060515046475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31920948731104322746914533 5985177887082060515046475)
          ·
            refine ⟨8977766830623090772569713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5985177887082060515046475 8977766830623090772569713)
            ·
              refine ⟨6733325122967318079427285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8977766830623090772569713 6733325122967318079427285)
              ·
                refine ⟨157812307569546517486577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6733325122967318079427285 157812307569546517486577)
                ·
                  rfl

theorem cell22_4149068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 7].length) (baseStart_4149068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149068 prefixEnd_4149068 := by exact prefixLift 4149068
  have htrace : WordTrace (prefixWord ++ tailWord_4149068) baseStart_4149068 baseEnd_4149068 := by
    simpa [prefixWord, tailWord_4149068, baseEnd_4149068] using wordTrace_append hprefix tailTrace_4149068
  have hstable : (prefixWord ++ tailWord_4149068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149068).length < 2 ^ (prefixWord ++ tailWord_4149068).sum := by decide
  have hdescent : baseEnd_4149068 < baseStart_4149068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149113 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 5]
def baseStart_4149113 : Nat := 118140960795 + 4149113 * 2 ^ 59
def prefixEnd_4149113 : Nat := 4983230072969 + 3 ^ 40 * 4149113 * 2
def baseEnd_4149113 : Nat := 473442057515184513334685

theorem tailTrace_4149113 : CollatzResearch.WordTrace tailWord_4149113 prefixEnd_4149113 473442057515184513334685 := by
  unfold tailWord_4149113
  simp only [CollatzResearch.WordTrace]
  refine ⟨151330583417479687930019993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100887055611653125286679995 151330583417479687930019993)
  ·
    refine ⟨113497937563109765947514995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151330583417479687930019993 113497937563109765947514995)
    ·
      refine ⟨170246906344664648921272493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113497937563109765947514995 170246906344664648921272493)
      ·
        refine ⟨63842589879249243345477185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170246906344664648921272493 63842589879249243345477185)
        ·
          refine ⟨47881942409436932509107889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63842589879249243345477185 47881942409436932509107889)
          ·
            refine ⟨35911456807077699381830917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47881942409436932509107889 35911456807077699381830917)
            ·
              refine ⟨6733398151327068634093297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35911456807077699381830917 6733398151327068634093297)
              ·
                refine ⟨5050048613495301475569973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6733398151327068634093297 5050048613495301475569973)
                ·
                  refine ⟨473442057515184513334685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5050048613495301475569973 473442057515184513334685)
                  ·
                    rfl

theorem cell22_4149113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_4149113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149113 prefixEnd_4149113 := by exact prefixLift 4149113
  have htrace : WordTrace (prefixWord ++ tailWord_4149113) baseStart_4149113 baseEnd_4149113 := by
    simpa [prefixWord, tailWord_4149113, baseEnd_4149113] using wordTrace_append hprefix tailTrace_4149113
  have hstable : (prefixWord ++ tailWord_4149113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149113).length < 2 ^ (prefixWord ++ tailWord_4149113).sum := by decide
  have hdescent : baseEnd_4149113 < baseStart_4149113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149143 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 3, 4]
def baseStart_4149143 : Nat := 118140960795 + 4149143 * 2 ^ 59
def prefixEnd_4149143 : Nat := 4983230072969 + 3 ^ 40 * 4149143 * 2
def baseEnd_4149143 : Nat := 1420336442158643461753963

theorem tailTrace_4149143 : CollatzResearch.WordTrace tailWord_4149143 prefixEnd_4149143 1420336442158643461753963 := by
  unfold tailWord_4149143
  simp only [CollatzResearch.WordTrace]
  refine ⟨151331677607371003053612083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100887785071580668702408055 151331677607371003053612083)
  ·
    refine ⟨226997516411056504580418125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151331677607371003053612083 226997516411056504580418125)
    ·
      refine ⟨85124068654146189217656797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226997516411056504580418125 85124068654146189217656797)
      ·
        refine ⟨31921525745304820956621299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85124068654146189217656797 31921525745304820956621299)
        ·
          refine ⟨47882288617957231434931949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31921525745304820956621299 47882288617957231434931949)
          ·
            refine ⟨17955858231733961788099481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47882288617957231434931949 17955858231733961788099481)
            ·
              refine ⟨13466893673800471341074611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17955858231733961788099481 13466893673800471341074611)
              ·
                refine ⟨20200340510700707011611917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13466893673800471341074611 20200340510700707011611917)
                ·
                  refine ⟨7575127691512765129354469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20200340510700707011611917 7575127691512765129354469)
                  ·
                    refine ⟨1420336442158643461753963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7575127691512765129354469 1420336442158643461753963)
                    ·
                      rfl

theorem cell22_4149143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_4149143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149143 prefixEnd_4149143 := by exact prefixLift 4149143
  have htrace : WordTrace (prefixWord ++ tailWord_4149143) baseStart_4149143 baseEnd_4149143 := by
    simpa [prefixWord, tailWord_4149143, baseEnd_4149143] using wordTrace_append hprefix tailTrace_4149143
  have hstable : (prefixWord ++ tailWord_4149143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149143).length < 2 ^ (prefixWord ++ tailWord_4149143).sum := by decide
  have hdescent : baseEnd_4149143 < baseStart_4149143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149209 : List Nat := [1, 2, 1, 2, 7, 1, 1, 3, 4]
def baseStart_4149209 : Nat := 118140960795 + 4149209 * 2 ^ 59
def prefixEnd_4149209 : Nat := 4983230072969 + 3 ^ 40 * 4149209 * 2
def baseEnd_4149209 : Nat := 473453011769147096534587

theorem tailTrace_4149209 : CollatzResearch.WordTrace tailWord_4149209 prefixEnd_4149209 473453011769147096534587 := by
  unfold tailWord_4149209
  simp only [CollatzResearch.WordTrace]
  refine ⟨151334084825131896325514681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100889389883421264217009787 151334084825131896325514681)
  ·
    refine ⟨113500563618848922244136011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151334084825131896325514681 113500563618848922244136011)
    ·
      refine ⟨170250845428273383366204017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113500563618848922244136011 170250845428273383366204017)
      ·
        refine ⟨127688134071205037524653013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170250845428273383366204017 127688134071205037524653013)
        ·
          refine ⟨2992690642293868066984055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 127688134071205037524653013 2992690642293868066984055)
          ·
            refine ⟨4489035963440802100476083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992690642293868066984055 4489035963440802100476083)
            ·
              refine ⟨6733553945161203150714125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489035963440802100476083 6733553945161203150714125)
              ·
                refine ⟨2525082729435451181517797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6733553945161203150714125 2525082729435451181517797)
                ·
                  refine ⟨473453011769147096534587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525082729435451181517797 473453011769147096534587)
                  ·
                    rfl

theorem cell22_4149209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 4].length) (baseStart_4149209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149209 prefixEnd_4149209 := by exact prefixLift 4149209
  have htrace : WordTrace (prefixWord ++ tailWord_4149209) baseStart_4149209 baseEnd_4149209 := by
    simpa [prefixWord, tailWord_4149209, baseEnd_4149209] using wordTrace_append hprefix tailTrace_4149209
  have hstable : (prefixWord ++ tailWord_4149209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149209).length < 2 ^ (prefixWord ++ tailWord_4149209).sum := by decide
  have hdescent : baseEnd_4149209 < baseStart_4149209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149323 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 1, 6]
def baseStart_4149323 : Nat := 118140960795 + 4149323 * 2 ^ 59
def prefixEnd_4149323 : Nat := 4983230072969 + 3 ^ 40 * 4149323 * 2
def baseEnd_4149323 : Nat := 1420398059837182992253411

theorem tailTrace_4149323 : CollatzResearch.WordTrace tailWord_4149323 prefixEnd_4149323 1420398059837182992253411 := by
  unfold tailWord_4149323
  simp only [CollatzResearch.WordTrace]
  refine ⟨151338242746718893795164623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100892161831145929196776415 151338242746718893795164623)
  ·
    refine ⟨227007364120078340692746935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151338242746718893795164623 227007364120078340692746935)
    ·
      refine ⟨340511046180117511039120403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227007364120078340692746935 340511046180117511039120403)
      ·
        refine ⟨510766569270176266558680605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340511046180117511039120403 510766569270176266558680605)
        ·
          refine ⟨191537463476316099959505227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510766569270176266558680605 191537463476316099959505227)
          ·
            refine ⟨287306195214474149939257841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191537463476316099959505227 287306195214474149939257841)
            ·
              refine ⟨215479646410855612454443381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287306195214474149939257841 215479646410855612454443381)
              ·
                refine ⟨20201216851017713667604067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215479646410855612454443381 20201216851017713667604067)
                ·
                  refine ⟨30301825276526570501406101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20201216851017713667604067 30301825276526570501406101)
                  ·
                    refine ⟨1420398059837182992253411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30301825276526570501406101 1420398059837182992253411)
                    ·
                      rfl

theorem cell22_4149323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_4149323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149323 prefixEnd_4149323 := by exact prefixLift 4149323
  have htrace : WordTrace (prefixWord ++ tailWord_4149323) baseStart_4149323 baseEnd_4149323 := by
    simpa [prefixWord, tailWord_4149323, baseEnd_4149323] using wordTrace_append hprefix tailTrace_4149323
  have hstable : (prefixWord ++ tailWord_4149323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149323).length < 2 ^ (prefixWord ++ tailWord_4149323).sum := by decide
  have hdescent : baseEnd_4149323 < baseStart_4149323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149338 : List Nat := [3, 1, 1, 2, 1, 1, 13]
def baseStart_4149338 : Nat := 118140960795 + 4149338 * 2 ^ 59
def prefixEnd_4149338 : Nat := 4983230072969 + 3 ^ 40 * 4149338 * 2
def baseEnd_4149338 : Nat := 52607525727545479745495

theorem tailTrace_4149338 : CollatzResearch.WordTrace tailWord_4149338 prefixEnd_4149338 52607525727545479745495 := by
  unfold tailWord_4149338
  simp only [CollatzResearch.WordTrace]
  refine ⟨37834697460416137839240167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100892526561109700904640445 37834697460416137839240167)
  ·
    refine ⟨56752046190624206758860251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37834697460416137839240167 56752046190624206758860251)
    ·
      refine ⟨85128069285936310138290377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56752046190624206758860251 85128069285936310138290377)
      ·
        refine ⟨63846051964452232603717783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85128069285936310138290377 63846051964452232603717783)
        ·
          refine ⟨95769077946678348905576675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63846051964452232603717783 95769077946678348905576675)
          ·
            refine ⟨143653616920017523358365013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95769077946678348905576675 143653616920017523358365013)
            ·
              refine ⟨52607525727545479745495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 143653616920017523358365013 52607525727545479745495)
              ·
                rfl

theorem cell22_4149338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 13].length) (baseStart_4149338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149338 prefixEnd_4149338 := by exact prefixLift 4149338
  have htrace : WordTrace (prefixWord ++ tailWord_4149338) baseStart_4149338 baseEnd_4149338 := by
    simpa [prefixWord, tailWord_4149338, baseEnd_4149338] using wordTrace_append hprefix tailTrace_4149338
  have hstable : (prefixWord ++ tailWord_4149338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149338).length < 2 ^ (prefixWord ++ tailWord_4149338).sum := by decide
  have hdescent : baseEnd_4149338 < baseStart_4149338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149359 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 2, 3]
def baseStart_4149359 : Nat := 118140960795 + 4149359 * 2 ^ 59
def prefixEnd_4149359 : Nat := 4983230072969 + 3 ^ 40 * 4149359 * 2
def baseEnd_4149359 : Nat := 1420410383372890898353301

theorem tailTrace_4149359 : CollatzResearch.WordTrace tailWord_4149359 prefixEnd_4149359 1420410383372890898353301 := by
  unfold tailWord_4149359
  simp only [CollatzResearch.WordTrace]
  refine ⟨151339555774588471943475131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100893037183058981295650087 151339555774588471943475131)
  ·
    refine ⟨227009333661882707915212697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151339555774588471943475131 227009333661882707915212697)
    ·
      refine ⟨170257000246412030936409523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227009333661882707915212697 170257000246412030936409523)
      ·
        refine ⟨255385500369618046404614285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170257000246412030936409523 255385500369618046404614285)
        ·
          refine ⟨95769562638606767401730357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255385500369618046404614285 95769562638606767401730357)
          ·
            refine ⟨8978396497369384443912221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95769562638606767401730357 8978396497369384443912221)
            ·
              refine ⟨3366898686513519166467083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8978396497369384443912221 3366898686513519166467083)
              ·
                refine ⟨5050348029770278749700625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3366898686513519166467083 5050348029770278749700625)
                ·
                  refine ⟨3787761022327709062275469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5050348029770278749700625 3787761022327709062275469)
                  ·
                    refine ⟨1420410383372890898353301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3787761022327709062275469 1420410383372890898353301)
                    ·
                      rfl

theorem cell22_4149359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 2, 3].length) (baseStart_4149359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149359 prefixEnd_4149359 := by exact prefixLift 4149359
  have htrace : WordTrace (prefixWord ++ tailWord_4149359) baseStart_4149359 baseEnd_4149359 := by
    simpa [prefixWord, tailWord_4149359, baseEnd_4149359] using wordTrace_append hprefix tailTrace_4149359
  have hstable : (prefixWord ++ tailWord_4149359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149359).length < 2 ^ (prefixWord ++ tailWord_4149359).sum := by decide
  have hdescent : baseEnd_4149359 < baseStart_4149359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149372 : List Nat := [2, 2, 2, 1, 1, 6, 2, 6]
def baseStart_4149372 : Nat := 118140960795 + 4149372 * 2 ^ 59
def prefixEnd_4149372 : Nat := 4983230072969 + 3 ^ 40 * 4149372 * 2
def baseEnd_4149372 : Nat := 157823870393173688642029

theorem tailTrace_4149372 : CollatzResearch.WordTrace tailWord_4149372 prefixEnd_4149372 157823870393173688642029 := by
  unfold tailWord_4149372
  simp only [CollatzResearch.WordTrace]
  refine ⟨75670014961770687581849185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100893353282360916775798913 75670014961770687581849185)
  ·
    refine ⟨56752511221328015686386889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75670014961770687581849185 56752511221328015686386889)
    ·
      refine ⟨42564383415996011764790167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56752511221328015686386889 42564383415996011764790167)
      ·
        refine ⟨63846575123994017647185251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42564383415996011764790167 63846575123994017647185251)
        ·
          refine ⟨95769862685991026470777877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63846575123994017647185251 95769862685991026470777877)
          ·
            refine ⟨4489212313405829365817713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95769862685991026470777877 4489212313405829365817713)
            ·
              refine ⟨3366909235054372024363285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489212313405829365817713 3366909235054372024363285)
              ·
                refine ⟨157823870393173688642029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3366909235054372024363285 157823870393173688642029)
                ·
                  rfl

theorem cell22_4149372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 6].length) (baseStart_4149372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149372 prefixEnd_4149372 := by exact prefixLift 4149372
  have htrace : WordTrace (prefixWord ++ tailWord_4149372) baseStart_4149372 baseEnd_4149372 := by
    simpa [prefixWord, tailWord_4149372, baseEnd_4149372] using wordTrace_append hprefix tailTrace_4149372
  have hstable : (prefixWord ++ tailWord_4149372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149372).length < 2 ^ (prefixWord ++ tailWord_4149372).sum := by decide
  have hdescent : baseEnd_4149372 < baseStart_4149372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149477 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_4149477 : Nat := 118140960795 + 4149477 * 2 ^ 59
def prefixEnd_4149477 : Nat := 4983230072969 + 3 ^ 40 * 4149477 * 2
def baseEnd_4149477 : Nat := 1420450777184377923902939

theorem tailTrace_4149477 : CollatzResearch.WordTrace tailWord_4149477 prefixEnd_4149477 1420450777184377923902939 := by
  unfold tailWord_4149477
  simp only [CollatzResearch.WordTrace]
  refine ⟨151343859588160978096270685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100895906392107318730847123 151343859588160978096270685)
  ·
    refine ⟨56753947345560366786101507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151343859588160978096270685 56753947345560366786101507)
    ·
      refine ⟨85130921018340550179152261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56753947345560366786101507 85130921018340550179152261)
      ·
        refine ⟨15962047690938853158591049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85130921018340550179152261 15962047690938853158591049)
        ·
          refine ⟨11971535768204139868943287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15962047690938853158591049 11971535768204139868943287)
          ·
            refine ⟨17957303652306209803414931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11971535768204139868943287 17957303652306209803414931)
            ·
              refine ⟨26935955478459314705122397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17957303652306209803414931 26935955478459314705122397)
              ·
                refine ⟨10100983304422243014420899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26935955478459314705122397 10100983304422243014420899)
                ·
                  refine ⟨15151474956633364521631349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10100983304422243014420899 15151474956633364521631349)
                  ·
                    refine ⟨1420450777184377923902939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15151474956633364521631349 1420450777184377923902939)
                    ·
                      rfl

theorem cell22_4149477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_4149477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149477 prefixEnd_4149477 := by exact prefixLift 4149477
  have htrace : WordTrace (prefixWord ++ tailWord_4149477) baseStart_4149477 baseEnd_4149477 := by
    simpa [prefixWord, tailWord_4149477, baseEnd_4149477] using wordTrace_append hprefix tailTrace_4149477
  have hstable : (prefixWord ++ tailWord_4149477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149477).length < 2 ^ (prefixWord ++ tailWord_4149477).sum := by decide
  have hdescent : baseEnd_4149477 < baseStart_4149477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149511 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 4, 3]
def baseStart_4149511 : Nat := 118140960795 + 4149511 * 2 ^ 59
def prefixEnd_4149511 : Nat := 4983230072969 + 3 ^ 40 * 4149511 * 2
def baseEnd_4149511 : Nat := 1420462416079213168552835

theorem tailTrace_4149511 : CollatzResearch.WordTrace tailWord_4149511 prefixEnd_4149511 1420462416079213168552835 := by
  unfold tailWord_4149511
  simp only [CollatzResearch.WordTrace]
  refine ⟨151345099670037801903008387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100896733113358534602005591 151345099670037801903008387)
  ·
    refine ⟨227017649505056702854512581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151345099670037801903008387 227017649505056702854512581)
    ·
      refine ⟨42565809282198131785221109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227017649505056702854512581 42565809282198131785221109)
      ·
        refine ⟨3990544620206074854864479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42565809282198131785221109 3990544620206074854864479)
        ·
          refine ⟨5985816930309112282296719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990544620206074854864479 5985816930309112282296719)
          ·
            refine ⟨8978725395463668423445079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5985816930309112282296719 8978725395463668423445079)
            ·
              refine ⟨13468088093195502635167619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8978725395463668423445079 13468088093195502635167619)
              ·
                refine ⟨20202132139793253952751429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13468088093195502635167619 20202132139793253952751429)
                ·
                  refine ⟨3787899776211235116140893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20202132139793253952751429 3787899776211235116140893)
                  ·
                    refine ⟨1420462416079213168552835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3787899776211235116140893 1420462416079213168552835)
                    ·
                      rfl

theorem cell22_4149511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_4149511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149511 prefixEnd_4149511 := by exact prefixLift 4149511
  have htrace : WordTrace (prefixWord ++ tailWord_4149511) baseStart_4149511 baseEnd_4149511 := by
    simpa [prefixWord, tailWord_4149511, baseEnd_4149511] using wordTrace_append hprefix tailTrace_4149511
  have hstable : (prefixWord ++ tailWord_4149511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149511).length < 2 ^ (prefixWord ++ tailWord_4149511).sum := by decide
  have hdescent : baseEnd_4149511 < baseStart_4149511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149541 : List Nat := [1, 3, 1, 2, 6, 1, 2, 6]
def baseStart_4149541 : Nat := 118140960795 + 4149541 * 2 ^ 59
def prefixEnd_4149541 : Nat := 4983230072969 + 3 ^ 40 * 4149541 * 2
def baseEnd_4149541 : Nat := 157830298410255898922527

theorem tailTrace_4149541 : CollatzResearch.WordTrace tailWord_4149541 prefixEnd_4149541 157830298410255898922527 := by
  unfold tailWord_4149541
  simp only [CollatzResearch.WordTrace]
  refine ⟨151346193859929117026600477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100897462573286078017733651 151346193859929117026600477)
  ·
    refine ⟨56754822697473418884975179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151346193859929117026600477 56754822697473418884975179)
    ·
      refine ⟨85132234046210128327462769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56754822697473418884975179 85132234046210128327462769)
      ·
        refine ⟨63849175534657596245597077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85132234046210128327462769 63849175534657596245597077)
        ·
          refine ⟨2992930103187074824012363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63849175534657596245597077 2992930103187074824012363)
          ·
            refine ⟨4489395154780612236018545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992930103187074824012363 4489395154780612236018545)
            ·
              refine ⟨3367046366085459177013909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489395154780612236018545 3367046366085459177013909)
              ·
                refine ⟨157830298410255898922527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3367046366085459177013909 157830298410255898922527)
                ·
                  rfl

theorem cell22_4149541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 6].length) (baseStart_4149541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149541 prefixEnd_4149541 := by exact prefixLift 4149541
  have htrace : WordTrace (prefixWord ++ tailWord_4149541) baseStart_4149541 baseEnd_4149541 := by
    simpa [prefixWord, tailWord_4149541, baseEnd_4149541] using wordTrace_append hprefix tailTrace_4149541
  have hstable : (prefixWord ++ tailWord_4149541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149541).length < 2 ^ (prefixWord ++ tailWord_4149541).sum := by decide
  have hdescent : baseEnd_4149541 < baseStart_4149541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149599 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 1, 4]
def baseStart_4149599 : Nat := 118140960795 + 4149599 * 2 ^ 59
def prefixEnd_4149599 : Nat := 4983230072969 + 3 ^ 40 * 4149599 * 2
def baseEnd_4149599 : Nat := 1420492540277610272352565

theorem tailTrace_4149599 : CollatzResearch.WordTrace tailWord_4149599 prefixEnd_4149599 1420492540277610272352565 := by
  unfold tailWord_4149599
  simp only [CollatzResearch.WordTrace]
  refine ⟨151348309293718992932211851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100898872862479328621474567 151348309293718992932211851)
  ·
    refine ⟨227022463940578489398317777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151348309293718992932211851 227022463940578489398317777)
    ·
      refine ⟨170266847955433867048738333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227022463940578489398317777 170266847955433867048738333)
      ·
        refine ⟨63850067983287700143276875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170266847955433867048738333 63850067983287700143276875)
        ·
          refine ⟨95775101974931550214915313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63850067983287700143276875 95775101974931550214915313)
          ·
            refine ⟨71831326481198662661186485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95775101974931550214915313 71831326481198662661186485)
            ·
              refine ⟨6734186857612374624486233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71831326481198662661186485 6734186857612374624486233)
              ·
                refine ⟨5050640143209280968364675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6734186857612374624486233 5050640143209280968364675)
                ·
                  refine ⟨7575960214813921452547013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050640143209280968364675 7575960214813921452547013)
                  ·
                    refine ⟨1420492540277610272352565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7575960214813921452547013 1420492540277610272352565)
                    ·
                      rfl

theorem cell22_4149599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_4149599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149599 prefixEnd_4149599 := by exact prefixLift 4149599
  have htrace : WordTrace (prefixWord ++ tailWord_4149599) baseStart_4149599 baseEnd_4149599 := by
    simpa [prefixWord, tailWord_4149599, baseEnd_4149599] using wordTrace_append hprefix tailTrace_4149599
  have hstable : (prefixWord ++ tailWord_4149599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149599).length < 2 ^ (prefixWord ++ tailWord_4149599).sum := by decide
  have hdescent : baseEnd_4149599 < baseStart_4149599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149616 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 1, 4]
def baseStart_4149616 : Nat := 118140960795 + 4149616 * 2 ^ 59
def prefixEnd_4149616 : Nat := 4983230072969 + 3 ^ 40 * 4149616 * 2
def baseEnd_4149616 : Nat := 1420498359725027894677513

theorem tailTrace_4149616 : CollatzResearch.WordTrace tailWord_4149616 prefixEnd_4149616 1420498359725027894677513 := by
  unfold tailWord_4149616
  simp only [CollatzResearch.WordTrace]
  refine ⟨75674464667328702417790351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100899286223104936557053801 75674464667328702417790351)
  ·
    refine ⟨113511697000993053626685527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75674464667328702417790351 113511697000993053626685527)
    ·
      refine ⟨170267545501489580440028291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113511697000993053626685527 170267545501489580440028291)
      ·
        refine ⟨255401318252234370660042437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170267545501489580440028291 255401318252234370660042437)
        ·
          refine ⟨47887747172293944498757957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255401318252234370660042437 47887747172293944498757957)
          ·
            refine ⟨8978952594805114593517117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47887747172293944498757957 8978952594805114593517117)
            ·
              refine ⟨3367107223051917972568919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8978952594805114593517117 3367107223051917972568919)
              ·
                refine ⟨5050660834577876958853379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367107223051917972568919 5050660834577876958853379)
                ·
                  refine ⟨7575991251866815438280069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050660834577876958853379 7575991251866815438280069)
                  ·
                    refine ⟨1420498359725027894677513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7575991251866815438280069 1420498359725027894677513)
                    ·
                      rfl

theorem cell22_4149616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 4].length) (baseStart_4149616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149616 prefixEnd_4149616 := by exact prefixLift 4149616
  have htrace : WordTrace (prefixWord ++ tailWord_4149616) baseStart_4149616 baseEnd_4149616 := by
    simpa [prefixWord, tailWord_4149616, baseEnd_4149616] using wordTrace_append hprefix tailTrace_4149616
  have hstable : (prefixWord ++ tailWord_4149616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149616).length < 2 ^ (prefixWord ++ tailWord_4149616).sum := by decide
  have hdescent : baseEnd_4149616 < baseStart_4149616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149646 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_4149646 : Nat := 118140960795 + 4149646 * 2 ^ 59
def prefixEnd_4149646 : Nat := 4983230072969 + 3 ^ 40 * 4149646 * 2
def baseEnd_4149646 : Nat := 1420508629338117816427421

theorem tailTrace_4149646 : CollatzResearch.WordTrace tailWord_4149646 prefixEnd_4149646 1420508629338117816427421 := by
  unfold tailWord_4149646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18918752940568589994896599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100900015683032479972781861 18918752940568589994896599)
  ·
    refine ⟨28378129410852884992344899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18918752940568589994896599 28378129410852884992344899)
    ·
      refine ⟨42567194116279327488517349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28378129410852884992344899 42567194116279327488517349)
      ·
        refine ⟨7981348896802373904097003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42567194116279327488517349 7981348896802373904097003)
        ·
          refine ⟨11972023345203560856145505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7981348896802373904097003 11972023345203560856145505)
          ·
            refine ⟨8979017508902670642109129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11972023345203560856145505 8979017508902670642109129)
            ·
              refine ⟨6734263131677002981581847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8979017508902670642109129 6734263131677002981581847)
              ·
                refine ⟨10101394697515504472372771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734263131677002981581847 10101394697515504472372771)
                ·
                  refine ⟨15152092046273256708559157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10101394697515504472372771 15152092046273256708559157)
                  ·
                    refine ⟨1420508629338117816427421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15152092046273256708559157 1420508629338117816427421)
                    ·
                      rfl

theorem cell22_4149646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_4149646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149646 prefixEnd_4149646 := by exact prefixLift 4149646
  have htrace : WordTrace (prefixWord ++ tailWord_4149646) baseStart_4149646 baseEnd_4149646 := by
    simpa [prefixWord, tailWord_4149646, baseEnd_4149646] using wordTrace_append hprefix tailTrace_4149646
  have hstable : (prefixWord ++ tailWord_4149646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149646).length < 2 ^ (prefixWord ++ tailWord_4149646).sum := by decide
  have hdescent : baseEnd_4149646 < baseStart_4149646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149697 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4149697 : Nat := 118140960795 + 4149697 * 2 ^ 59
def prefixEnd_4149697 : Nat := 4983230072969 + 3 ^ 40 * 4149697 * 2
def baseEnd_4149697 : Nat := 1420526087680370683402265

theorem tailTrace_4149697 : CollatzResearch.WordTrace tailWord_4149697 prefixEnd_4149697 1420526087680370683402265 := by
  unfold tailWord_4149697
  simp only [CollatzResearch.WordTrace]
  refine ⟨151351883647363955669279345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100901255764909303779519563 151351883647363955669279345)
  ·
    refine ⟨113513912735522966751959509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151351883647363955669279345 113513912735522966751959509)
    ·
      refine ⟨2660482329738819533249051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 113513912735522966751959509 2660482329738819533249051)
      ·
        refine ⟨3990723494608229299873577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660482329738819533249051 3990723494608229299873577)
        ·
          refine ⟨2993042620956171974905183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3990723494608229299873577 2993042620956171974905183)
          ·
            refine ⟨4489563931434257962357775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993042620956171974905183 4489563931434257962357775)
            ·
              refine ⟨6734345897151386943536663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489563931434257962357775 6734345897151386943536663)
              ·
                refine ⟨10101518845727080415304995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734345897151386943536663 10101518845727080415304995)
                ·
                  refine ⟨15152278268590620622957493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10101518845727080415304995 15152278268590620622957493)
                  ·
                    refine ⟨1420526087680370683402265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15152278268590620622957493 1420526087680370683402265)
                    ·
                      rfl

theorem cell22_4149697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4149697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149697 prefixEnd_4149697 := by exact prefixLift 4149697
  have htrace : WordTrace (prefixWord ++ tailWord_4149697) baseStart_4149697 baseEnd_4149697 := by
    simpa [prefixWord, tailWord_4149697, baseEnd_4149697] using wordTrace_append hprefix tailTrace_4149697
  have hstable : (prefixWord ++ tailWord_4149697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149697).length < 2 ^ (prefixWord ++ tailWord_4149697).sum := by decide
  have hdescent : baseEnd_4149697 < baseStart_4149697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149800 : List Nat := [2, 1, 5, 2, 1, 1, 4, 2, 4]
def baseStart_4149800 : Nat := 118140960795 + 4149800 * 2 ^ 59
def prefixEnd_4149800 : Nat := 4983230072969 + 3 ^ 40 * 4149800 * 2
def baseEnd_4149800 : Nat := 473520448895104249358983

theorem tailTrace_4149800 : CollatzResearch.WordTrace tailWord_4149800 prefixEnd_4149800 473520448895104249358983 := by
  unfold tailWord_4149800
  simp only [CollatzResearch.WordTrace]
  refine ⟨75677820182995402130139427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100903760243993869506852569 75677820182995402130139427)
  ·
    refine ⟨113516730274493103195209141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75677820182995402130139427 113516730274493103195209141)
    ·
      refine ⟨10642193463233728424550857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113516730274493103195209141 10642193463233728424550857)
      ·
        refine ⟨7981645097425296318413143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10642193463233728424550857 7981645097425296318413143)
        ·
          refine ⟨11972467646137944477619715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7981645097425296318413143 11972467646137944477619715)
          ·
            refine ⟨17958701469206916716429573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11972467646137944477619715 17958701469206916716429573)
            ·
              refine ⟨3367256525476296884330545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17958701469206916716429573 3367256525476296884330545)
              ·
                refine ⟨2525442394107222663247909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3367256525476296884330545 2525442394107222663247909)
                ·
                  refine ⟨473520448895104249358983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525442394107222663247909 473520448895104249358983)
                  ·
                    rfl

theorem cell22_4149800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 4].length) (baseStart_4149800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149800 prefixEnd_4149800 := by exact prefixLift 4149800
  have htrace : WordTrace (prefixWord ++ tailWord_4149800) baseStart_4149800 baseEnd_4149800 := by
    simpa [prefixWord, tailWord_4149800, baseEnd_4149800] using wordTrace_append hprefix tailTrace_4149800
  have hstable : (prefixWord ++ tailWord_4149800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149800).length < 2 ^ (prefixWord ++ tailWord_4149800).sum := by decide
  have hdescent : baseEnd_4149800 < baseStart_4149800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149830 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_4149830 : Nat := 118140960795 + 4149830 * 2 ^ 59
def prefixEnd_4149830 : Nat := 4983230072969 + 3 ^ 40 * 4149830 * 2
def baseEnd_4149830 : Nat := 1420571616298402669826857

theorem tailTrace_4149830 : CollatzResearch.WordTrace tailWord_4149830 prefixEnd_4149830 1420571616298402669826857 := by
  unfold tailWord_4149830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4729897954871316230745967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100904489703921412922580629 4729897954871316230745967)
  ·
    refine ⟨7094846932306974346118951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4729897954871316230745967 7094846932306974346118951)
    ·
      refine ⟨10642270398460461519178427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7094846932306974346118951 10642270398460461519178427)
      ·
        refine ⟨15963405597690692278767641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10642270398460461519178427 15963405597690692278767641)
        ·
          refine ⟨11972554198268019209075731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15963405597690692278767641 11972554198268019209075731)
          ·
            refine ⟨17958831297402028813613597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11972554198268019209075731 17958831297402028813613597)
            ·
              refine ⟨6734561736525760805105099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17958831297402028813613597 6734561736525760805105099)
              ·
                refine ⟨10101842604788641207657649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734561736525760805105099 10101842604788641207657649)
                ·
                  refine ⟨7576381953591480905743237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10101842604788641207657649 7576381953591480905743237)
                  ·
                    refine ⟨1420571616298402669826857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7576381953591480905743237 1420571616298402669826857)
                    ·
                      rfl

theorem cell22_4149830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_4149830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149830 prefixEnd_4149830 := by exact prefixLift 4149830
  have htrace : WordTrace (prefixWord ++ tailWord_4149830) baseStart_4149830 baseEnd_4149830 := by
    simpa [prefixWord, tailWord_4149830, baseEnd_4149830] using wordTrace_append hprefix tailTrace_4149830
  have hstable : (prefixWord ++ tailWord_4149830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149830).length < 2 ^ (prefixWord ++ tailWord_4149830).sum := by decide
  have hdescent : baseEnd_4149830 < baseStart_4149830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149856 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 5]
def baseStart_4149856 : Nat := 118140960795 + 4149856 * 2 ^ 59
def prefixEnd_4149856 : Nat := 4983230072969 + 3 ^ 40 * 4149856 * 2
def baseEnd_4149856 : Nat := 473526838876582422892259

theorem tailTrace_4149856 : CollatzResearch.WordTrace tailWord_4149856 prefixEnd_4149856 473526838876582422892259 := by
  unfold tailWord_4149856
  simp only [CollatzResearch.WordTrace]
  refine ⟨75678841426893962912158711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100905121902525283882878281 75678841426893962912158711)
  ·
    refine ⟨113518262140340944368238067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75678841426893962912158711 113518262140340944368238067)
    ·
      refine ⟨170277393210511416552357101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113518262140340944368238067 170277393210511416552357101)
      ·
        refine ⟨63854022453941781207133913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170277393210511416552357101 63854022453941781207133913)
        ·
          refine ⟨47890516840456335905350435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63854022453941781207133913 47890516840456335905350435)
          ·
            refine ⟨71835775260684503858025653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47890516840456335905350435 71835775260684503858025653)
            ·
              refine ⟨6734603930689172236689905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71835775260684503858025653 6734603930689172236689905)
              ·
                refine ⟨5050952948016879177517429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6734603930689172236689905 5050952948016879177517429)
                ·
                  refine ⟨473526838876582422892259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5050952948016879177517429 473526838876582422892259)
                  ·
                    rfl

theorem cell22_4149856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_4149856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149856 prefixEnd_4149856 := by exact prefixLift 4149856
  have htrace : WordTrace (prefixWord ++ tailWord_4149856) baseStart_4149856 baseEnd_4149856 := by
    simpa [prefixWord, tailWord_4149856, baseEnd_4149856] using wordTrace_append hprefix tailTrace_4149856
  have hstable : (prefixWord ++ tailWord_4149856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149856).length < 2 ^ (prefixWord ++ tailWord_4149856).sum := by decide
  have hdescent : baseEnd_4149856 < baseStart_4149856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149929 : List Nat := [1, 2, 1, 1, 1, 1, 2, 13]
def baseStart_4149929 : Nat := 118140960795 + 4149929 * 2 ^ 59
def prefixEnd_4149929 : Nat := 4983230072969 + 3 ^ 40 * 4149929 * 2
def baseEnd_4149929 : Nat := 157845056224622156844617

theorem tailTrace_4149929 : CollatzResearch.WordTrace tailWord_4149929 prefixEnd_4149929 157845056224622156844617 := by
  unfold tailWord_4149929
  simp only [CollatzResearch.WordTrace]
  refine ⟨151360345382523459291724841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100906896921682306194483227 151360345382523459291724841)
  ·
    refine ⟨113520259036892594468793631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151360345382523459291724841 113520259036892594468793631)
    ·
      refine ⟨170280388555338891703190447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113520259036892594468793631 170280388555338891703190447)
      ·
        refine ⟨255420582833008337554785671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170280388555338891703190447 255420582833008337554785671)
        ·
          refine ⟨383130874249512506332178507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255420582833008337554785671 383130874249512506332178507)
          ·
            refine ⟨574696311374268759498267761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383130874249512506332178507 574696311374268759498267761)
            ·
              refine ⟨431022233530701569623700821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574696311374268759498267761 431022233530701569623700821)
              ·
                refine ⟨157845056224622156844617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 431022233530701569623700821 157845056224622156844617)
                ·
                  rfl

theorem cell22_4149929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 13].length) (baseStart_4149929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149929 prefixEnd_4149929 := by exact prefixLift 4149929
  have htrace : WordTrace (prefixWord ++ tailWord_4149929) baseStart_4149929 baseEnd_4149929 := by
    simpa [prefixWord, tailWord_4149929, baseEnd_4149929] using wordTrace_append hprefix tailTrace_4149929
  have hstable : (prefixWord ++ tailWord_4149929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149929).length < 2 ^ (prefixWord ++ tailWord_4149929).sum := by decide
  have hdescent : baseEnd_4149929 < baseStart_4149929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149937 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 1, 4]
def baseStart_4149937 : Nat := 118140960795 + 4149937 * 2 ^ 59
def prefixEnd_4149937 : Nat := 4983230072969 + 3 ^ 40 * 4149937 * 2
def baseEnd_4149937 : Nat := 1420608244585090057401529

theorem tailTrace_4149937 : CollatzResearch.WordTrace tailWord_4149937 prefixEnd_4149937 1420608244585090057401529 := by
  unfold tailWord_4149937
  simp only [CollatzResearch.WordTrace]
  refine ⟨151360637166494476658016065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100907091444329651105344043 151360637166494476658016065)
  ·
    refine ⟨113520477874870857493512049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151360637166494476658016065 113520477874870857493512049)
    ·
      refine ⟨85140358406153143120134037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113520477874870857493512049 85140358406153143120134037)
      ·
        refine ⟨3990954300288428583756283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85140358406153143120134037 3990954300288428583756283)
        ·
          refine ⟨5986431450432642875634425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990954300288428583756283 5986431450432642875634425)
          ·
            refine ⟨4489823587824482156725819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5986431450432642875634425 4489823587824482156725819)
            ·
              refine ⟨6734735381736723235088729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489823587824482156725819 6734735381736723235088729)
              ·
                refine ⟨5051051536302542426316547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6734735381736723235088729 5051051536302542426316547)
                ·
                  refine ⟨7576577304453813639474821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051051536302542426316547 7576577304453813639474821)
                  ·
                    refine ⟨1420608244585090057401529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7576577304453813639474821 1420608244585090057401529)
                    ·
                      rfl

theorem cell22_4149937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_4149937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149937 prefixEnd_4149937 := by exact prefixLift 4149937
  have htrace : WordTrace (prefixWord ++ tailWord_4149937) baseStart_4149937 baseEnd_4149937 := by
    simpa [prefixWord, tailWord_4149937, baseEnd_4149937] using wordTrace_append hprefix tailTrace_4149937
  have hstable : (prefixWord ++ tailWord_4149937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149937).length < 2 ^ (prefixWord ++ tailWord_4149937).sum := by decide
  have hdescent : baseEnd_4149937 < baseStart_4149937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149948 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_4149948 : Nat := 118140960795 + 4149948 * 2 ^ 59
def prefixEnd_4149948 : Nat := 4983230072969 + 3 ^ 40 * 4149948 * 2
def baseEnd_4149948 : Nat := 1420612010109889695376495

theorem tailTrace_4149948 : CollatzResearch.WordTrace tailWord_4149948 prefixEnd_4149948 1420612010109889695376495 := by
  unfold tailWord_4149948
  simp only [CollatzResearch.WordTrace]
  refine ⟨75680519184727312768333249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100907358912969750357777665 75680519184727312768333249)
  ·
    refine ⟨56760389388545484576249937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75680519184727312768333249 56760389388545484576249937)
    ·
      refine ⟨42570292041409113432187453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56760389388545484576249937 42570292041409113432187453)
      ·
        refine ⟨15963859515528417537070295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42570292041409113432187453 15963859515528417537070295)
        ·
          refine ⟨23945789273292626305605443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15963859515528417537070295 23945789273292626305605443)
          ·
            refine ⟨35918683909938939458408165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23945789273292626305605443 35918683909938939458408165)
            ·
              refine ⟨6734753233113551148451531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35918683909938939458408165 6734753233113551148451531)
              ·
                refine ⟨10102129849670326722677297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734753233113551148451531 10102129849670326722677297)
                ·
                  refine ⟨7576597387252745042007973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10102129849670326722677297 7576597387252745042007973)
                  ·
                    refine ⟨1420612010109889695376495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7576597387252745042007973 1420612010109889695376495)
                    ·
                      rfl

theorem cell22_4149948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_4149948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149948 prefixEnd_4149948 := by exact prefixLift 4149948
  have htrace : WordTrace (prefixWord ++ tailWord_4149948) baseStart_4149948 baseEnd_4149948 := by
    simpa [prefixWord, tailWord_4149948, baseEnd_4149948] using wordTrace_append hprefix tailTrace_4149948
  have hstable : (prefixWord ++ tailWord_4149948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149948).length < 2 ^ (prefixWord ++ tailWord_4149948).sum := by decide
  have hdescent : baseEnd_4149948 < baseStart_4149948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149976 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_4149976 : Nat := 118140960795 + 4149976 * 2 ^ 59
def prefixEnd_4149976 : Nat := 4983230072969 + 3 ^ 40 * 4149976 * 2
def baseEnd_4149976 : Nat := 1420621595082106955676409

theorem tailTrace_4149976 : CollatzResearch.WordTrace tailWord_4149976 prefixEnd_4149976 1420621595082106955676409 := by
  unfold tailWord_4149976
  simp only [CollatzResearch.WordTrace]
  refine ⟨75681029806676593159342891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100908039742235457545790521 75681029806676593159342891)
  ·
    refine ⟨113521544710014889739014337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75681029806676593159342891 113521544710014889739014337)
    ·
      refine ⟨85141158532511167304260753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113521544710014889739014337 85141158532511167304260753)
      ·
        refine ⟨63855868899383375478195565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85141158532511167304260753 63855868899383375478195565)
        ·
          refine ⟨23945950837268765804323337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63855868899383375478195565 23945950837268765804323337)
          ·
            refine ⟨17959463127951574353242503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23945950837268765804323337 17959463127951574353242503)
            ·
              refine ⟨26939194691927361529863755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17959463127951574353242503 26939194691927361529863755)
              ·
                refine ⟨40408792037891042294795633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26939194691927361529863755 40408792037891042294795633)
                ·
                  refine ⟨30306594028418281721096725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40408792037891042294795633 30306594028418281721096725)
                  ·
                    refine ⟨1420621595082106955676409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30306594028418281721096725 1420621595082106955676409)
                    ·
                      rfl

theorem cell22_4149976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_4149976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149976 prefixEnd_4149976 := by exact prefixLift 4149976
  have htrace : WordTrace (prefixWord ++ tailWord_4149976) baseStart_4149976 baseEnd_4149976 := by
    simpa [prefixWord, tailWord_4149976, baseEnd_4149976] using wordTrace_append hprefix tailTrace_4149976
  have hstable : (prefixWord ++ tailWord_4149976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149976).length < 2 ^ (prefixWord ++ tailWord_4149976).sum := by decide
  have hdescent : baseEnd_4149976 < baseStart_4149976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149978 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 3, 3]
def baseStart_4149978 : Nat := 118140960795 + 4149978 * 2 ^ 59
def prefixEnd_4149978 : Nat := 4983230072969 + 3 ^ 40 * 4149978 * 2
def baseEnd_4149978 : Nat := 1420622279722979617126403

theorem tailTrace_4149978 : CollatzResearch.WordTrace tailWord_4149978 prefixEnd_4149978 1420622279722979617126403 := by
  unfold tailWord_4149978
  simp only [CollatzResearch.WordTrace]
  refine ⟨37840533139836485165064647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100908088372897293773505725 37840533139836485165064647)
  ·
    refine ⟨56760799709754727747596971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37840533139836485165064647 56760799709754727747596971)
    ·
      refine ⟨85141199564632091621395457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56760799709754727747596971 85141199564632091621395457)
      ·
        refine ⟨63855899673474068716046593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85141199564632091621395457 63855899673474068716046593)
        ·
          refine ⟨47891924755105551537034945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63855899673474068716046593 47891924755105551537034945)
          ·
            refine ⟨35918943566329163652776209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47891924755105551537034945 35918943566329163652776209)
            ·
              refine ⟨26939207674746872739582157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35918943566329163652776209 26939207674746872739582157)
              ·
                refine ⟨10102202878030077277343309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26939207674746872739582157 10102202878030077277343309)
                ·
                  refine ⟨3788326079261278979003741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10102202878030077277343309 3788326079261278979003741)
                  ·
                    refine ⟨1420622279722979617126403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3788326079261278979003741 1420622279722979617126403)
                    ·
                      rfl

theorem cell22_4149978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_4149978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149978 prefixEnd_4149978 := by exact prefixLift 4149978
  have htrace : WordTrace (prefixWord ++ tailWord_4149978) baseStart_4149978 baseEnd_4149978 := by
    simpa [prefixWord, tailWord_4149978, baseEnd_4149978] using wordTrace_append hprefix tailTrace_4149978
  have hstable : (prefixWord ++ tailWord_4149978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149978).length < 2 ^ (prefixWord ++ tailWord_4149978).sum := by decide
  have hdescent : baseEnd_4149978 < baseStart_4149978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149980 : List Nat := [2, 2, 5, 1, 1, 3, 1, 7]
def baseStart_4149980 : Nat := 118140960795 + 4149980 * 2 ^ 59
def prefixEnd_4149980 : Nat := 4983230072969 + 3 ^ 40 * 4149980 * 2
def baseEnd_4149980 : Nat := 157846996040428030952933

theorem tailTrace_4149980 : CollatzResearch.WordTrace tailWord_4149980 prefixEnd_4149980 157846996040428030952933 := by
  unfold tailWord_4149980
  simp only [CollatzResearch.WordTrace]
  refine ⟨75681102752669347500915697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100908137003559130001220929 75681102752669347500915697)
  ·
    refine ⟨56760827064502010625686773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75681102752669347500915697 56760827064502010625686773)
    ·
      refine ⟨5321327537297063496158135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56760827064502010625686773 5321327537297063496158135)
      ·
        refine ⟨7981991305945595244237203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5321327537297063496158135 7981991305945595244237203)
        ·
          refine ⟨11972986958918392866355805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7981991305945595244237203 11972986958918392866355805)
          ·
            refine ⟨4489870109594397324883427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11972986958918392866355805 4489870109594397324883427)
            ·
              refine ⟨6734805164391595987325141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489870109594397324883427 6734805164391595987325141)
              ·
                refine ⟨157846996040428030952933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6734805164391595987325141 157846996040428030952933)
                ·
                  rfl

theorem cell22_4149980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 7].length) (baseStart_4149980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4149980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4149980 prefixEnd_4149980 := by exact prefixLift 4149980
  have htrace : WordTrace (prefixWord ++ tailWord_4149980) baseStart_4149980 baseEnd_4149980 := by
    simpa [prefixWord, tailWord_4149980, baseEnd_4149980] using wordTrace_append hprefix tailTrace_4149980
  have hstable : (prefixWord ++ tailWord_4149980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149980).length < 2 ^ (prefixWord ++ tailWord_4149980).sum := by decide
  have hdescent : baseEnd_4149980 < baseStart_4149980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150012 : List Nat := [2, 2, 2, 1, 3, 3, 2, 3, 1, 3]
def baseStart_4150012 : Nat := 118140960795 + 4150012 * 2 ^ 59
def prefixEnd_4150012 : Nat := 4983230072969 + 3 ^ 40 * 4150012 * 2
def baseEnd_4150012 : Nat := 1420633918617814861776299

theorem tailTrace_4150012 : CollatzResearch.WordTrace tailWord_4150012 prefixEnd_4150012 1420633918617814861776299 := by
  unfold tailWord_4150012
  simp only [CollatzResearch.WordTrace]
  refine ⟨75681686320611382233498145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100908915094148509644664193 75681686320611382233498145)
  ·
    refine ⟨56761264740458536675123609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75681686320611382233498145 56761264740458536675123609)
    ·
      refine ⟨42570948555343902506342707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56761264740458536675123609 42570948555343902506342707)
      ·
        refine ⟨63856422833015853759514061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42570948555343902506342707 63856422833015853759514061)
        ·
          refine ⟨23946158562380945159817773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63856422833015853759514061 23946158562380945159817773)
          ·
            refine ⟨8979809460892854434931665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23946158562380945159817773 8979809460892854434931665)
            ·
              refine ⟨6734857095669640826198749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8979809460892854434931665 6734857095669640826198749)
              ·
                refine ⟨2525571410876115309824531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6734857095669640826198749 2525571410876115309824531)
                ·
                  refine ⟨3788357116314172964736797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525571410876115309824531 3788357116314172964736797)
                  ·
                    refine ⟨1420633918617814861776299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3788357116314172964736797 1420633918617814861776299)
                    ·
                      rfl

theorem cell22_4150012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_4150012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150012 prefixEnd_4150012 := by exact prefixLift 4150012
  have htrace : WordTrace (prefixWord ++ tailWord_4150012) baseStart_4150012 baseEnd_4150012 := by
    simpa [prefixWord, tailWord_4150012, baseEnd_4150012] using wordTrace_append hprefix tailTrace_4150012
  have hstable : (prefixWord ++ tailWord_4150012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150012).length < 2 ^ (prefixWord ++ tailWord_4150012).sum := by decide
  have hdescent : baseEnd_4150012 < baseStart_4150012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150023 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 2, 5]
def baseStart_4150023 : Nat := 118140960795 + 4150023 * 2 ^ 59
def prefixEnd_4150023 : Nat := 4983230072969 + 3 ^ 40 * 4150023 * 2
def baseEnd_4150023 : Nat := 1420637684142614499751265

theorem tailTrace_4150023 : CollatzResearch.WordTrace tailWord_4150023 prefixEnd_4150023 1420637684142614499751265 := by
  unfold tailWord_4150023
  simp only [CollatzResearch.WordTrace]
  refine ⟨151363773844182913345646723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100909182562788608897097815 151363773844182913345646723)
  ·
    refine ⟨227045660766274370018470085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151363773844182913345646723 227045660766274370018470085)
    ·
      refine ⟨42571061393676444378463141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227045660766274370018470085 42571061393676444378463141)
      ·
        refine ⟨7982074011314333320961839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42571061393676444378463141 7982074011314333320961839)
        ·
          refine ⟨11973111016971499981442759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7982074011314333320961839 11973111016971499981442759)
          ·
            refine ⟨17959666525457249972164139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11973111016971499981442759 17959666525457249972164139)
            ·
              refine ⟨26939499788185874958246209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17959666525457249972164139 26939499788185874958246209)
              ·
                refine ⟨20204624841139406218684657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26939499788185874958246209 20204624841139406218684657)
                ·
                  refine ⟨15153468630854554664013493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20204624841139406218684657 15153468630854554664013493)
                  ·
                    refine ⟨1420637684142614499751265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15153468630854554664013493 1420637684142614499751265)
                    ·
                      rfl

theorem cell22_4150023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_4150023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150023 prefixEnd_4150023 := by exact prefixLift 4150023
  have htrace : WordTrace (prefixWord ++ tailWord_4150023) baseStart_4150023 baseEnd_4150023 := by
    simpa [prefixWord, tailWord_4150023, baseEnd_4150023] using wordTrace_append hprefix tailTrace_4150023
  have hstable : (prefixWord ++ tailWord_4150023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150023).length < 2 ^ (prefixWord ++ tailWord_4150023).sum := by decide
  have hdescent : baseEnd_4150023 < baseStart_4150023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150083 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 2, 4]
def baseStart_4150083 : Nat := 118140960795 + 4150083 * 2 ^ 59
def prefixEnd_4150083 : Nat := 4983230072969 + 3 ^ 40 * 4150083 * 2
def baseEnd_4150083 : Nat := 1420658223368794343251081

theorem tailTrace_4150083 : CollatzResearch.WordTrace tailWord_4150083 prefixEnd_4150083 1420658223368794343251081 := by
  unfold tailWord_4150083
  simp only [CollatzResearch.WordTrace]
  refine ⟨151365962223965543592830903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100910641482643695728553935 151365962223965543592830903)
  ·
    refine ⟨227048943335948315389246355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151365962223965543592830903 227048943335948315389246355)
    ·
      refine ⟨340573415003922473083869533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227048943335948315389246355 340573415003922473083869533)
      ·
        refine ⟨127715030626470927406451075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340573415003922473083869533 127715030626470927406451075)
        ·
          refine ⟨191572545939706391109676613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127715030626470927406451075 191572545939706391109676613)
          ·
            refine ⟨35919852363694948333064365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191572545939706391109676613 35919852363694948333064365)
            ·
              refine ⟨13469944636385605624899137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35919852363694948333064365 13469944636385605624899137)
              ·
                refine ⟨10102458477289204218674353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13469944636385605624899137 10102458477289204218674353)
                ·
                  refine ⟨7576843857966903164005765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10102458477289204218674353 7576843857966903164005765)
                  ·
                    refine ⟨1420658223368794343251081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7576843857966903164005765 1420658223368794343251081)
                    ·
                      rfl

theorem cell22_4150083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 4].length) (baseStart_4150083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150083 prefixEnd_4150083 := by exact prefixLift 4150083
  have htrace : WordTrace (prefixWord ++ tailWord_4150083) baseStart_4150083 baseEnd_4150083 := by
    simpa [prefixWord, tailWord_4150083, baseEnd_4150083] using wordTrace_append hprefix tailTrace_4150083
  have hstable : (prefixWord ++ tailWord_4150083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150083).length < 2 ^ (prefixWord ++ tailWord_4150083).sum := by decide
  have hdescent : baseEnd_4150083 < baseStart_4150083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150098 : List Nat := [3, 2, 2, 1, 1, 2, 4, 7]
def baseStart_4150098 : Nat := 118140960795 + 4150098 * 2 ^ 59
def prefixEnd_4150098 : Nat := 4983230072969 + 3 ^ 40 * 4150098 * 2
def baseEnd_4150098 : Nat := 157851484241704367125115

theorem tailTrace_4150098 : CollatzResearch.WordTrace tailWord_4150098 prefixEnd_4150098 157851484241704367125115 := by
  unfold tailWord_4150098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37841627329727800288656737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100911006212607467436417965 37841627329727800288656737)
  ·
    refine ⟨28381220497295850216492553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37841627329727800288656737 28381220497295850216492553)
    ·
      refine ⟨21285915372971887662369415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28381220497295850216492553 21285915372971887662369415)
      ·
        refine ⟨31928873059457831493554123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21285915372971887662369415 31928873059457831493554123)
        ·
          refine ⟨47893309589186747240331185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31928873059457831493554123 47893309589186747240331185)
          ·
            refine ⟨35919982191890060430248389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47893309589186747240331185 35919982191890060430248389)
            ·
              refine ⟨6734996660979386330671573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35919982191890060430248389 6734996660979386330671573)
              ·
                refine ⟨157851484241704367125115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6734996660979386330671573 157851484241704367125115)
                ·
                  rfl

theorem cell22_4150098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_4150098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150098 prefixEnd_4150098 := by exact prefixLift 4150098
  have htrace : WordTrace (prefixWord ++ tailWord_4150098) baseStart_4150098 baseEnd_4150098 := by
    simpa [prefixWord, tailWord_4150098, baseEnd_4150098] using wordTrace_append hprefix tailTrace_4150098
  have hstable : (prefixWord ++ tailWord_4150098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150098).length < 2 ^ (prefixWord ++ tailWord_4150098).sum := by decide
  have hdescent : baseEnd_4150098 < baseStart_4150098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150143 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 5]
def baseStart_4150143 : Nat := 118140960795 + 4150143 * 2 ^ 59
def prefixEnd_4150143 : Nat := 4983230072969 + 3 ^ 40 * 4150143 * 2
def baseEnd_4150143 : Nat := 473559587531658062250299

theorem tailTrace_4150143 : CollatzResearch.WordTrace tailWord_4150143 prefixEnd_4150143 473559587531658062250299 := by
  unfold tailWord_4150143
  simp only [CollatzResearch.WordTrace]
  refine ⟨151368150603748173840015083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100912100402498782560010055 151368150603748173840015083)
  ·
    refine ⟨227052225905622260760022625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151368150603748173840015083 227052225905622260760022625)
    ·
      refine ⟨170289169429216695570016969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227052225905622260760022625 170289169429216695570016969)
      ·
        refine ⟨127716877071912521677512727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170289169429216695570016969 127716877071912521677512727)
        ·
          refine ⟨191575315607868782516269091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127716877071912521677512727 191575315607868782516269091)
          ·
            refine ⟨287362973411803173774403637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191575315607868782516269091 287362973411803173774403637)
            ·
              refine ⟨26940278757356547541350341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287362973411803173774403637 26940278757356547541350341)
              ·
                refine ⟨5051302267004352664003189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26940278757356547541350341 5051302267004352664003189)
                ·
                  refine ⟨473559587531658062250299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5051302267004352664003189 473559587531658062250299)
                  ·
                    rfl

theorem cell22_4150143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 5].length) (baseStart_4150143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150143 prefixEnd_4150143 := by exact prefixLift 4150143
  have htrace : WordTrace (prefixWord ++ tailWord_4150143) baseStart_4150143 baseEnd_4150143 := by
    simpa [prefixWord, tailWord_4150143, baseEnd_4150143] using wordTrace_append hprefix tailTrace_4150143
  have hstable : (prefixWord ++ tailWord_4150143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150143).length < 2 ^ (prefixWord ++ tailWord_4150143).sum := by decide
  have hdescent : baseEnd_4150143 < baseStart_4150143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150147 : List Nat := [1, 1, 1, 3, 4, 1, 3, 4, 1, 3]
def baseStart_4150147 : Nat := 118140960795 + 4150147 * 2 ^ 59
def prefixEnd_4150147 : Nat := 4983230072969 + 3 ^ 40 * 4150147 * 2
def baseEnd_4150147 : Nat := 1420680131876719509650885

theorem tailTrace_4150147 : CollatzResearch.WordTrace tailWord_4150147 prefixEnd_4150147 1420680131876719509650885 := by
  unfold tailWord_4150147
  simp only [CollatzResearch.WordTrace]
  refine ⟨151368296495733682523160695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100912197663822455015440463 151368296495733682523160695)
  ·
    refine ⟨227052444743600523784741043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151368296495733682523160695 227052444743600523784741043)
    ·
      refine ⟨340578667115400785677111565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227052444743600523784741043 340578667115400785677111565)
      ·
        refine ⟨127717000168275294628916837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340578667115400785677111565 127717000168275294628916837)
        ·
          refine ⟨23946937531551617742921907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127717000168275294628916837 23946937531551617742921907)
          ·
            refine ⟨35920406297327426614382861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23946937531551617742921907 35920406297327426614382861)
            ·
              refine ⟨13470152361497784980393573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35920406297327426614382861 13470152361497784980393573)
              ·
                refine ⟨2525653567780834683823795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13470152361497784980393573 2525653567780834683823795)
                ·
                  refine ⟨3788480351671252025735693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525653567780834683823795 3788480351671252025735693)
                  ·
                    refine ⟨1420680131876719509650885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3788480351671252025735693 1420680131876719509650885)
                    ·
                      rfl

theorem cell22_4150147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 1, 3].length) (baseStart_4150147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150147 prefixEnd_4150147 := by exact prefixLift 4150147
  have htrace : WordTrace (prefixWord ++ tailWord_4150147) baseStart_4150147 baseEnd_4150147 := by
    simpa [prefixWord, tailWord_4150147, baseEnd_4150147] using wordTrace_append hprefix tailTrace_4150147
  have hstable : (prefixWord ++ tailWord_4150147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150147).length < 2 ^ (prefixWord ++ tailWord_4150147).sum := by decide
  have hdescent : baseEnd_4150147 < baseStart_4150147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150198 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4150198 : Nat := 118140960795 + 4150198 * 2 ^ 59
def prefixEnd_4150198 : Nat := 4983230072969 + 3 ^ 40 * 4150198 * 2
def baseEnd_4150198 : Nat := 1420697590218972376625729

theorem tailTrace_4150198 : CollatzResearch.WordTrace tailWord_4150198 prefixEnd_4150198 1420697590218972376625729 := by
  unfold tailWord_4150198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9460634788659307389579203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100913437745699278822178165 9460634788659307389579203)
  ·
    refine ⟨14190952182988961084368805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9460634788659307389579203 14190952182988961084368805)
    ·
      refine ⟨2660803534310430203319151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14190952182988961084368805 2660803534310430203319151)
      ·
        refine ⟨3991205301465645304978727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660803534310430203319151 3991205301465645304978727)
        ·
          refine ⟨5986807952198467957468091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991205301465645304978727 5986807952198467957468091)
          ·
            refine ⟨8980211928297701936202137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986807952198467957468091 8980211928297701936202137)
            ·
              refine ⟨6735158946223276452151603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8980211928297701936202137 6735158946223276452151603)
              ·
                refine ⟨10102738419334914678227405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6735158946223276452151603 10102738419334914678227405)
                ·
                  refine ⟨3788526907250593004335277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10102738419334914678227405 3788526907250593004335277)
                  ·
                    refine ⟨1420697590218972376625729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3788526907250593004335277 1420697590218972376625729)
                    ·
                      rfl

theorem cell22_4150198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4150198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150198 prefixEnd_4150198 := by exact prefixLift 4150198
  have htrace : WordTrace (prefixWord ++ tailWord_4150198) baseStart_4150198 baseEnd_4150198 := by
    simpa [prefixWord, tailWord_4150198, baseEnd_4150198] using wordTrace_append hprefix tailTrace_4150198
  have hstable : (prefixWord ++ tailWord_4150198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150198).length < 2 ^ (prefixWord ++ tailWord_4150198).sum := by decide
  have hdescent : baseEnd_4150198 < baseStart_4150198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150237 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_4150237 : Nat := 118140960795 + 4150237 * 2 ^ 59
def prefixEnd_4150237 : Nat := 4983230072969 + 3 ^ 40 * 4150237 * 2
def baseEnd_4150237 : Nat := 1420710940715989274900609

theorem tailTrace_4150237 : CollatzResearch.WordTrace tailWord_4150237 prefixEnd_4150237 1420710940715989274900609 := by
  unfold tailWord_4150237
  simp only [CollatzResearch.WordTrace]
  refine ⟨151371579065407627893936965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100914386043605085262624643 151371579065407627893936965)
  ·
    refine ⟨28382171074763930230113181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151371579065407627893936965 28382171074763930230113181)
    ·
      refine ⟨10643314153036473836292443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28382171074763930230113181 10643314153036473836292443)
      ·
        refine ⟨15964971229554710754438665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10643314153036473836292443 15964971229554710754438665)
        ·
          refine ⟨11973728422166033065828999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15964971229554710754438665 11973728422166033065828999)
          ·
            refine ⟨17960592633249049598743499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11973728422166033065828999 17960592633249049598743499)
            ·
              refine ⟨26940888949873574398115249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17960592633249049598743499 26940888949873574398115249)
              ·
                refine ⟨20205666712405180798586437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26940888949873574398115249 20205666712405180798586437)
                ·
                  refine ⟨3788562508575971399734957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20205666712405180798586437 3788562508575971399734957)
                  ·
                    refine ⟨1420710940715989274900609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3788562508575971399734957 1420710940715989274900609)
                    ·
                      rfl

theorem cell22_4150237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_4150237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150237 prefixEnd_4150237 := by exact prefixLift 4150237
  have htrace : WordTrace (prefixWord ++ tailWord_4150237) baseStart_4150237 baseEnd_4150237 := by
    simpa [prefixWord, tailWord_4150237, baseEnd_4150237] using wordTrace_append hprefix tailTrace_4150237
  have hstable : (prefixWord ++ tailWord_4150237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150237).length < 2 ^ (prefixWord ++ tailWord_4150237).sum := by decide
  have hdescent : baseEnd_4150237 < baseStart_4150237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150239 : List Nat := [1, 1, 2, 3, 5, 2, 1, 3, 4]
def baseStart_4150239 : Nat := 118140960795 + 4150239 * 2 ^ 59
def prefixEnd_4150239 : Nat := 4983230072969 + 3 ^ 40 * 4150239 * 2
def baseEnd_4150239 : Nat := 473570541785620645450201

theorem tailTrace_4150239 : CollatzResearch.WordTrace tailWord_4150239 prefixEnd_4150239 473570541785620645450201 := by
  unfold tailWord_4150239
  simp only [CollatzResearch.WordTrace]
  refine ⟨151371652011400382235509771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100914434674266921490339847 151371652011400382235509771)
  ·
    refine ⟨227057478017100573353264657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151371652011400382235509771 227057478017100573353264657)
    ·
      refine ⟨170293108512825430014948493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227057478017100573353264657 170293108512825430014948493)
      ·
        refine ⟨63859915692309536255605685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170293108512825430014948493 63859915692309536255605685)
        ·
          refine ⟨5986867096154019023963033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63859915692309536255605685 5986867096154019023963033)
          ·
            refine ⟨4490150322115514267972275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5986867096154019023963033 4490150322115514267972275)
            ·
              refine ⟨6735225483173271401958413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490150322115514267972275 6735225483173271401958413)
              ·
                refine ⟨2525709556189976775734405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6735225483173271401958413 2525709556189976775734405)
                ·
                  refine ⟨473570541785620645450201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525709556189976775734405 473570541785620645450201)
                  ·
                    rfl

theorem cell22_4150239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 4].length) (baseStart_4150239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150239 prefixEnd_4150239 := by exact prefixLift 4150239
  have htrace : WordTrace (prefixWord ++ tailWord_4150239) baseStart_4150239 baseEnd_4150239 := by
    simpa [prefixWord, tailWord_4150239, baseEnd_4150239] using wordTrace_append hprefix tailTrace_4150239
  have hstable : (prefixWord ++ tailWord_4150239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150239).length < 2 ^ (prefixWord ++ tailWord_4150239).sum := by decide
  have hdescent : baseEnd_4150239 < baseStart_4150239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150250 : List Nat := [3, 1, 3, 1, 2, 4, 8]
def baseStart_4150250 : Nat := 118140960795 + 4150250 * 2 ^ 59
def prefixEnd_4150250 : Nat := 4983230072969 + 3 ^ 40 * 4150250 * 2
def baseEnd_4150250 : Nat := 52619088551172650900947

theorem tailTrace_4150250 : CollatzResearch.WordTrace tailWord_4150250 prefixEnd_4150250 52619088551172650900947 := by
  unfold tailWord_4150250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37843013303590132778540051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100914702142907020742773469 37843013303590132778540051)
  ·
    refine ⟨56764519955385199167810077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37843013303590132778540051 56764519955385199167810077)
    ·
      refine ⟨21286694983269449687928779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56764519955385199167810077 21286694983269449687928779)
      ·
        refine ⟨31930042474904174531893169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21286694983269449687928779 31930042474904174531893169)
        ·
          refine ⟨23947531856178130898919877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31930042474904174531893169 23947531856178130898919877)
          ·
            refine ⟨4490162223033399543547477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23947531856178130898919877 4490162223033399543547477)
            ·
              refine ⟨52619088551172650900947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4490162223033399543547477 52619088551172650900947)
              ·
                rfl

theorem cell22_4150250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 8].length) (baseStart_4150250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150250 prefixEnd_4150250 := by exact prefixLift 4150250
  have htrace : WordTrace (prefixWord ++ tailWord_4150250) baseStart_4150250 baseEnd_4150250 := by
    simpa [prefixWord, tailWord_4150250, baseEnd_4150250] using wordTrace_append hprefix tailTrace_4150250
  have hstable : (prefixWord ++ tailWord_4150250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150250).length < 2 ^ (prefixWord ++ tailWord_4150250).sum := by decide
  have hdescent : baseEnd_4150250 < baseStart_4150250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150408 : List Nat := [2, 1, 3, 4, 3, 1, 1, 3, 4]
def baseStart_4150408 : Nat := 118140960795 + 4150408 * 2 ^ 59
def prefixEnd_4150408 : Nat := 4983230072969 + 3 ^ 40 * 4150408 * 2
def baseEnd_4150408 : Nat := 473589825836867276291695

theorem tailTrace_4150408 : CollatzResearch.WordTrace tailWord_4150408 prefixEnd_4150408 473589825836867276291695 := by
  unfold tailWord_4150408
  simp only [CollatzResearch.WordTrace]
  refine ⟨75688907973894062049205939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100918543965192082732274585 75688907973894062049205939)
  ·
    refine ⟨113533361960841093073808909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75688907973894062049205939 113533361960841093073808909)
    ·
      refine ⟨42575010735315409902678341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113533361960841093073808909 42575010735315409902678341)
      ·
        refine ⟨7982814512871639356752189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42575010735315409902678341 7982814512871639356752189)
        ·
          refine ⟨2993555442326864758782071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7982814512871639356752189 2993555442326864758782071)
          ·
            refine ⟨4490333163490297138173107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993555442326864758782071 4490333163490297138173107)
            ·
              refine ⟨6735499745235445707259661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490333163490297138173107 6735499745235445707259661)
              ·
                refine ⟨2525812404463292140222373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6735499745235445707259661 2525812404463292140222373)
                ·
                  refine ⟨473589825836867276291695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525812404463292140222373 473589825836867276291695)
                  ·
                    rfl

theorem cell22_4150408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 4].length) (baseStart_4150408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150408 prefixEnd_4150408 := by exact prefixLift 4150408
  have htrace : WordTrace (prefixWord ++ tailWord_4150408) baseStart_4150408 baseEnd_4150408 := by
    simpa [prefixWord, tailWord_4150408, baseEnd_4150408] using wordTrace_append hprefix tailTrace_4150408
  have hstable : (prefixWord ++ tailWord_4150408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150408).length < 2 ^ (prefixWord ++ tailWord_4150408).sum := by decide
  have hdescent : baseEnd_4150408 < baseStart_4150408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150475 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 10]
def baseStart_4150475 : Nat := 118140960795 + 4150475 * 2 ^ 59
def prefixEnd_4150475 : Nat := 4983230072969 + 3 ^ 40 * 4150475 * 2
def baseEnd_4150475 : Nat := 473597470993278662483293

theorem tailTrace_4150475 : CollatzResearch.WordTrace tailWord_4150475 prefixEnd_4150475 473597470993278662483293 := by
  unfold tailWord_4150475
  simp only [CollatzResearch.WordTrace]
  refine ⟨151380259638545394541100879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100920173092363596360733919 151380259638545394541100879)
  ·
    refine ⟨227070389457818091811651319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151380259638545394541100879 227070389457818091811651319)
    ·
      refine ⟨340605584186727137717476979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227070389457818091811651319 340605584186727137717476979)
      ·
        refine ⟨510908376280090706576215469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340605584186727137717476979 510908376280090706576215469)
        ·
          refine ⟨191590641105034014966080801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510908376280090706576215469 191590641105034014966080801)
          ·
            refine ⟨143692980828775511224560601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191590641105034014966080801 143692980828775511224560601)
            ·
              refine ⟨107769735621581633418420451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143692980828775511224560601 107769735621581633418420451)
              ·
                refine ⟨161654603432372450127630677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107769735621581633418420451 161654603432372450127630677)
                ·
                  refine ⟨473597470993278662483293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 161654603432372450127630677 473597470993278662483293)
                  ·
                    rfl

theorem cell22_4150475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 10].length) (baseStart_4150475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150475 prefixEnd_4150475 := by exact prefixLift 4150475
  have htrace : WordTrace (prefixWord ++ tailWord_4150475) baseStart_4150475 baseEnd_4150475 := by
    simpa [prefixWord, tailWord_4150475, baseEnd_4150475] using wordTrace_append hprefix tailTrace_4150475
  have hstable : (prefixWord ++ tailWord_4150475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150475).length < 2 ^ (prefixWord ++ tailWord_4150475).sum := by decide
  have hdescent : baseEnd_4150475 < baseStart_4150475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150485 : List Nat := [1, 3, 2, 4, 1, 3, 2, 2, 1, 3]
def baseStart_4150485 : Nat := 118140960795 + 4150485 * 2 ^ 59
def prefixEnd_4150485 : Nat := 4983230072969 + 3 ^ 40 * 4150485 * 2
def baseEnd_4150485 : Nat := 1420795836184199294699849

theorem tailTrace_4150485 : CollatzResearch.WordTrace tailWord_4150485 prefixEnd_4150485 1420795836184199294699849 := by
  unfold tailWord_4150485
  simp only [CollatzResearch.WordTrace]
  refine ⟨151380624368509166248964909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100920416245672777499309939 151380624368509166248964909)
  ·
    refine ⟨56767734138190937343361841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151380624368509166248964909 56767734138190937343361841)
    ·
      refine ⟨42575800603643203007521381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56767734138190937343361841 42575800603643203007521381)
      ·
        refine ⟨7982962613183100563910259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42575800603643203007521381 7982962613183100563910259)
        ·
          refine ⟨11974443919774650845865389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7982962613183100563910259 11974443919774650845865389)
          ·
            refine ⟨4490416469915494067199521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11974443919774650845865389 4490416469915494067199521)
            ·
              refine ⟨3367812352436620550399641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4490416469915494067199521 3367812352436620550399641)
              ·
                refine ⟨2525859264327465412799731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3367812352436620550399641 2525859264327465412799731)
                ·
                  refine ⟨3788788896491198119199597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525859264327465412799731 3788788896491198119199597)
                  ·
                    refine ⟨1420795836184199294699849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3788788896491198119199597 1420795836184199294699849)
                    ·
                      rfl

theorem cell22_4150485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_4150485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150485 prefixEnd_4150485 := by exact prefixLift 4150485
  have htrace : WordTrace (prefixWord ++ tailWord_4150485) baseStart_4150485 baseEnd_4150485 := by
    simpa [prefixWord, tailWord_4150485, baseEnd_4150485] using wordTrace_append hprefix tailTrace_4150485
  have hstable : (prefixWord ++ tailWord_4150485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150485).length < 2 ^ (prefixWord ++ tailWord_4150485).sum := by decide
  have hdescent : baseEnd_4150485 < baseStart_4150485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150507 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 1, 5]
def baseStart_4150507 : Nat := 118140960795 + 4150507 * 2 ^ 59
def prefixEnd_4150507 : Nat := 4983230072969 + 3 ^ 40 * 4150507 * 2
def baseEnd_4150507 : Nat := 1420803367233798570649781

theorem tailTrace_4150507 : CollatzResearch.WordTrace tailWord_4150507 prefixEnd_4150507 1420803367233798570649781 := by
  unfold tailWord_4150507
  simp only [CollatzResearch.WordTrace]
  refine ⟨151381426774429464006265775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100920951182952976004177183 151381426774429464006265775)
  ·
    refine ⟨227072140161644196009398663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151381426774429464006265775 227072140161644196009398663)
    ·
      refine ⟨340608210242466294014097995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227072140161644196009398663 340608210242466294014097995)
      ·
        refine ⟨510912315363699441021146993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340608210242466294014097995 510912315363699441021146993)
        ·
          refine ⟨383184236522774580765860245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510912315363699441021146993 383184236522774580765860245)
          ·
            refine ⟨17961761087005058473399699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 383184236522774580765860245 17961761087005058473399699)
            ·
              refine ⟨26942641630507587710099549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17961761087005058473399699 26942641630507587710099549)
              ·
                refine ⟨10103490611440345391287331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26942641630507587710099549 10103490611440345391287331)
                ·
                  refine ⟨15155235917160518086930997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10103490611440345391287331 15155235917160518086930997)
                  ·
                    refine ⟨1420803367233798570649781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15155235917160518086930997 1420803367233798570649781)
                    ·
                      rfl

theorem cell22_4150507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 5].length) (baseStart_4150507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150507 prefixEnd_4150507 := by exact prefixLift 4150507
  have htrace : WordTrace (prefixWord ++ tailWord_4150507) baseStart_4150507 baseEnd_4150507 := by
    simpa [prefixWord, tailWord_4150507, baseEnd_4150507] using wordTrace_append hprefix tailTrace_4150507
  have hstable : (prefixWord ++ tailWord_4150507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150507).length < 2 ^ (prefixWord ++ tailWord_4150507).sum := by decide
  have hdescent : baseEnd_4150507 < baseStart_4150507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150509 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 6]
def baseStart_4150509 : Nat := 118140960795 + 4150509 * 2 ^ 59
def prefixEnd_4150509 : Nat := 4983230072969 + 3 ^ 40 * 4150509 * 2
def baseEnd_4150509 : Nat := 473601350624890410699925

theorem tailTrace_4150509 : CollatzResearch.WordTrace tailWord_4150509 prefixEnd_4150509 473601350624890410699925 := by
  unfold tailWord_4150509
  simp only [CollatzResearch.WordTrace]
  refine ⟨151381499720422218347838581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100920999813614812231892387 151381499720422218347838581)
  ·
    refine ⟨14192015598789582970109867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151381499720422218347838581 14192015598789582970109867)
    ·
      refine ⟨21288023398184374455164801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14192015598789582970109867 21288023398184374455164801)
      ·
        refine ⟨15966017548638280841373601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21288023398184374455164801 15966017548638280841373601)
        ·
          refine ⟨11974513161478710631030201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15966017548638280841373601 11974513161478710631030201)
          ·
            refine ⟨8980884871109032973272651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11974513161478710631030201 8980884871109032973272651)
            ·
              refine ⟨13471327306663549459908977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8980884871109032973272651 13471327306663549459908977)
              ·
                refine ⟨10103495479997662094931733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13471327306663549459908977 10103495479997662094931733)
                ·
                  refine ⟨473601350624890410699925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10103495479997662094931733 473601350624890410699925)
                  ·
                    rfl

theorem cell22_4150509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_4150509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150509 prefixEnd_4150509 := by exact prefixLift 4150509
  have htrace : WordTrace (prefixWord ++ tailWord_4150509) baseStart_4150509 baseEnd_4150509 := by
    simpa [prefixWord, tailWord_4150509, baseEnd_4150509] using wordTrace_append hprefix tailTrace_4150509
  have hstable : (prefixWord ++ tailWord_4150509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150509).length < 2 ^ (prefixWord ++ tailWord_4150509).sum := by decide
  have hdescent : baseEnd_4150509 < baseStart_4150509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150522 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_4150522 : Nat := 118140960795 + 4150522 * 2 ^ 59
def prefixEnd_4150522 : Nat := 4983230072969 + 3 ^ 40 * 4150522 * 2
def baseEnd_4150522 : Nat := 1420808502040343531524735

theorem tailTrace_4150522 : CollatzResearch.WordTrace tailWord_4150522 prefixEnd_4150522 1420808502040343531524735 := by
  unfold tailWord_4150522
  simp only [CollatzResearch.WordTrace]
  refine ⟨37845493467343780392015455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100921315912916747712041213 37845493467343780392015455)
  ·
    refine ⟨56768240201015670588023183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37845493467343780392015455 56768240201015670588023183)
    ·
      refine ⟨85152360301523505882034775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56768240201015670588023183 85152360301523505882034775)
      ·
        refine ⟨127728540452285258823052163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85152360301523505882034775 127728540452285258823052163)
        ·
          refine ⟨191592810678427888234578245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127728540452285258823052163 191592810678427888234578245)
          ·
            refine ⟨35923652002205229043983421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191592810678427888234578245 35923652002205229043983421)
            ·
              refine ⟨13471369500826960891493783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35923652002205229043983421 13471369500826960891493783)
              ·
                refine ⟨20207054251240441337240675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13471369500826960891493783 20207054251240441337240675)
                ·
                  refine ⟨30310581376860662005861013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20207054251240441337240675 30310581376860662005861013)
                  ·
                    refine ⟨1420808502040343531524735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30310581376860662005861013 1420808502040343531524735)
                    ·
                      rfl

theorem cell22_4150522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_4150522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150522 prefixEnd_4150522 := by exact prefixLift 4150522
  have htrace : WordTrace (prefixWord ++ tailWord_4150522) baseStart_4150522 baseEnd_4150522 := by
    simpa [prefixWord, tailWord_4150522, baseEnd_4150522] using wordTrace_append hprefix tailTrace_4150522
  have hstable : (prefixWord ++ tailWord_4150522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150522).length < 2 ^ (prefixWord ++ tailWord_4150522).sum := by decide
  have hdescent : baseEnd_4150522 < baseStart_4150522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150526 : List Nat := [4, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_4150526 : Nat := 118140960795 + 4150526 * 2 ^ 59
def prefixEnd_4150526 : Nat := 4983230072969 + 3 ^ 40 * 4150526 * 2
def baseEnd_4150526 : Nat := 473603290440696284808241

theorem tailTrace_4150526 : CollatzResearch.WordTrace tailWord_4150526 prefixEnd_4150526 473603290440696284808241 := by
  unfold tailWord_4150526
  simp only [CollatzResearch.WordTrace]
  refine ⟨18922764970170078781400929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100921413174240420167471621 18922764970170078781400929)
  ·
    refine ⟨14192073727627559086050697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18922764970170078781400929 14192073727627559086050697)
    ·
      refine ⟨10644055295720669314538023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14192073727627559086050697 10644055295720669314538023)
      ·
        refine ⟨15966082943581003971807035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10644055295720669314538023 15966082943581003971807035)
        ·
          refine ⟨23949124415371505957710553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15966082943581003971807035 23949124415371505957710553)
          ·
            refine ⟨17961843311528629468282915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23949124415371505957710553 17961843311528629468282915)
            ·
              refine ⟨26942764967292944202424373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17961843311528629468282915 26942764967292944202424373)
              ·
                refine ⟨2525884215683713518977285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26942764967292944202424373 2525884215683713518977285)
                ·
                  refine ⟨473603290440696284808241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525884215683713518977285 473603290440696284808241)
                  ·
                    rfl

theorem cell22_4150526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_4150526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150526 prefixEnd_4150526 := by exact prefixLift 4150526
  have htrace : WordTrace (prefixWord ++ tailWord_4150526) baseStart_4150526 baseEnd_4150526 := by
    simpa [prefixWord, tailWord_4150526, baseEnd_4150526] using wordTrace_append hprefix tailTrace_4150526
  have hstable : (prefixWord ++ tailWord_4150526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150526).length < 2 ^ (prefixWord ++ tailWord_4150526).sum := by decide
  have hdescent : baseEnd_4150526 < baseStart_4150526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150597 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_4150597 : Nat := 118140960795 + 4150597 * 2 ^ 59
def prefixEnd_4150597 : Nat := 4983230072969 + 3 ^ 40 * 4150597 * 2
def baseEnd_4150597 : Nat := 1420834176073068335899505

theorem tailTrace_4150597 : CollatzResearch.WordTrace tailWord_4150597 prefixEnd_4150597 1420834176073068335899505 := by
  unfold tailWord_4150597
  simp only [CollatzResearch.WordTrace]
  refine ⟨151384709344103409377042045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100923139562735606251361363 151384709344103409377042045)
  ·
    refine ⟨56769266004038778516390767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151384709344103409377042045 56769266004038778516390767)
    ·
      refine ⟨85153899006058167774586151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56769266004038778516390767 85153899006058167774586151)
      ·
        refine ⟨127730848509087251661879227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85153899006058167774586151 127730848509087251661879227)
        ·
          refine ⟨191596272763630877492818841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127730848509087251661879227 191596272763630877492818841)
          ·
            refine ⟨143697204572723158119614131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191596272763630877492818841 143697204572723158119614131)
            ·
              refine ⟨215545806859084737179421197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143697204572723158119614131 215545806859084737179421197)
              ·
                refine ⟨80829677572156776442282949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215545806859084737179421197 80829677572156776442282949)
                ·
                  refine ⟨15155564544779395582928053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80829677572156776442282949 15155564544779395582928053)
                  ·
                    refine ⟨1420834176073068335899505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15155564544779395582928053 1420834176073068335899505)
                    ·
                      rfl

theorem cell22_4150597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_4150597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150597 prefixEnd_4150597 := by exact prefixLift 4150597
  have htrace : WordTrace (prefixWord ++ tailWord_4150597) baseStart_4150597 baseEnd_4150597 := by
    simpa [prefixWord, tailWord_4150597, baseEnd_4150597] using wordTrace_append hprefix tailTrace_4150597
  have hstable : (prefixWord ++ tailWord_4150597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150597).length < 2 ^ (prefixWord ++ tailWord_4150597).sum := by decide
  have hdescent : baseEnd_4150597 < baseStart_4150597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150629 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_4150629 : Nat := 118140960795 + 4150629 * 2 ^ 59
def prefixEnd_4150629 : Nat := 4983230072969 + 3 ^ 40 * 4150629 * 2
def baseEnd_4150629 : Nat := 1420845130327030919099407

theorem tailTrace_4150629 : CollatzResearch.WordTrace tailWord_4150629 prefixEnd_4150629 1420845130327030919099407 := by
  unfold tailWord_4150629
  simp only [CollatzResearch.WordTrace]
  refine ⟨151385876479987478842206941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100923917653324985894804627 151385876479987478842206941)
  ·
    refine ⟨56769703679995304565827603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151385876479987478842206941 56769703679995304565827603)
    ·
      refine ⟨85154555519992956848741405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56769703679995304565827603 85154555519992956848741405)
      ·
        refine ⟨31932958319997358818278027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85154555519992956848741405 31932958319997358818278027)
        ·
          refine ⟨47899437479996038227417041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31932958319997358818278027 47899437479996038227417041)
          ·
            refine ⟨35924578109997028670562781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47899437479996038227417041 35924578109997028670562781)
            ·
              refine ⟨13471716791248885751461043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35924578109997028670562781 13471716791248885751461043)
              ·
                refine ⟨20207575186873328627191565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13471716791248885751461043 20207575186873328627191565)
                ·
                  refine ⟨7577840695077498235196837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20207575186873328627191565 7577840695077498235196837)
                  ·
                    refine ⟨1420845130327030919099407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7577840695077498235196837 1420845130327030919099407)
                    ·
                      rfl

theorem cell22_4150629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_4150629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150629 prefixEnd_4150629 := by exact prefixLift 4150629
  have htrace : WordTrace (prefixWord ++ tailWord_4150629) baseStart_4150629 baseEnd_4150629 := by
    simpa [prefixWord, tailWord_4150629, baseEnd_4150629] using wordTrace_append hprefix tailTrace_4150629
  have hstable : (prefixWord ++ tailWord_4150629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150629).length < 2 ^ (prefixWord ++ tailWord_4150629).sum := by decide
  have hdescent : baseEnd_4150629 < baseStart_4150629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150676 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4150676 : Nat := 118140960795 + 4150676 * 2 ^ 59
def prefixEnd_4150676 : Nat := 4983230072969 + 3 ^ 40 * 4150676 * 2
def baseEnd_4150676 : Nat := 1420861219387538463174263

theorem tailTrace_4150676 : CollatzResearch.WordTrace tailWord_4150676 prefixEnd_4150676 1420861219387538463174263 := by
  unfold tailWord_4150676
  simp only [CollatzResearch.WordTrace]
  refine ⟨75693795355408602934583941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100925060473878137246111921 75693795355408602934583941)
  ·
    refine ⟨14192586629139113050234489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75693795355408602934583941 14192586629139113050234489)
    ·
      refine ⟨10644439971854334787675867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14192586629139113050234489 10644439971854334787675867)
      ·
        refine ⟨15966659957781502181513801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10644439971854334787675867 15966659957781502181513801)
        ·
          refine ⟨11974994968336126636135351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15966659957781502181513801 11974994968336126636135351)
          ·
            refine ⟨17962492452504189954203027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11974994968336126636135351 17962492452504189954203027)
            ·
              refine ⟨26943738678756284931304541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17962492452504189954203027 26943738678756284931304541)
              ·
                refine ⟨10103902004533606849239203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26943738678756284931304541 10103902004533606849239203)
                ·
                  refine ⟨15155853006800410273858805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10103902004533606849239203 15155853006800410273858805)
                  ·
                    refine ⟨1420861219387538463174263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15155853006800410273858805 1420861219387538463174263)
                    ·
                      rfl

theorem cell22_4150676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4150676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150676 prefixEnd_4150676 := by exact prefixLift 4150676
  have htrace : WordTrace (prefixWord ++ tailWord_4150676) baseStart_4150676 baseEnd_4150676 := by
    simpa [prefixWord, tailWord_4150676, baseEnd_4150676] using wordTrace_append hprefix tailTrace_4150676
  have hstable : (prefixWord ++ tailWord_4150676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150676).length < 2 ^ (prefixWord ++ tailWord_4150676).sum := by decide
  have hdescent : baseEnd_4150676 < baseStart_4150676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150740 : List Nat := [2, 4, 1, 2, 4, 1, 2, 6]
def baseStart_4150740 : Nat := 118140960795 + 4150740 * 2 ^ 59
def prefixEnd_4150740 : Nat := 4983230072969 + 3 ^ 40 * 4150740 * 2
def baseEnd_4150740 : Nat := 157875903099495958841563

theorem tailTrace_4150740 : CollatzResearch.WordTrace tailWord_4150740 prefixEnd_4150740 157875903099495958841563 := by
  unfold tailWord_4150740
  simp only [CollatzResearch.WordTrace]
  refine ⟨75694962491292672399748837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100926616655056896532998449 75694962491292672399748837)
  ·
    refine ⟨14192805467117376074952907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75694962491292672399748837 14192805467117376074952907)
    ·
      refine ⟨21289208200676064112429361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14192805467117376074952907 21289208200676064112429361)
      ·
        refine ⟨15966906150507048084322021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21289208200676064112429361 15966906150507048084322021)
        ·
          refine ⟨2993794903220071515810379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15966906150507048084322021 2993794903220071515810379)
          ·
            refine ⟨4490692354830107273715569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993794903220071515810379 4490692354830107273715569)
            ·
              refine ⟨3368019266122580455286677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4490692354830107273715569 3368019266122580455286677)
              ·
                refine ⟨157875903099495958841563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3368019266122580455286677 157875903099495958841563)
                ·
                  rfl

theorem cell22_4150740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 6].length) (baseStart_4150740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150740 prefixEnd_4150740 := by exact prefixLift 4150740
  have htrace : WordTrace (prefixWord ++ tailWord_4150740) baseStart_4150740 baseEnd_4150740 := by
    simpa [prefixWord, tailWord_4150740, baseEnd_4150740] using wordTrace_append hprefix tailTrace_4150740
  have hstable : (prefixWord ++ tailWord_4150740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150740).length < 2 ^ (prefixWord ++ tailWord_4150740).sum := by decide
  have hdescent : baseEnd_4150740 < baseStart_4150740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150755 : List Nat := [1, 1, 1, 6, 2, 1, 3, 3, 1, 3]
def baseStart_4150755 : Nat := 118140960795 + 4150755 * 2 ^ 59
def prefixEnd_4150755 : Nat := 4983230072969 + 3 ^ 40 * 4150755 * 2
def baseEnd_4150755 : Nat := 1420888262702008590449021

theorem tailTrace_4150755 : CollatzResearch.WordTrace tailWord_4150755 prefixEnd_4150755 1420888262702008590449021 := by
  unfold tailWord_4150755
  simp only [CollatzResearch.WordTrace]
  refine ⟨151390472077531002361293719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100926981385020668240862479 151390472077531002361293719)
  ·
    refine ⟨227085708116296503541940579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151390472077531002361293719 227085708116296503541940579)
    ·
      refine ⟨340628562174444755312910869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227085708116296503541940579 340628562174444755312910869)
      ·
        refine ⟨15966963851927097905292697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 340628562174444755312910869 15966963851927097905292697)
        ·
          refine ⟨11975222888945323428969523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15966963851927097905292697 11975222888945323428969523)
          ·
            refine ⟨17962834333417985143454285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11975222888945323428969523 17962834333417985143454285)
            ·
              refine ⟨6736062875031744428795357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17962834333417985143454285 6736062875031744428795357)
              ·
                refine ⟨2526023578136904160798259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6736062875031744428795357 2526023578136904160798259)
                ·
                  refine ⟨3789035367205356241197389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526023578136904160798259 3789035367205356241197389)
                  ·
                    refine ⟨1420888262702008590449021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789035367205356241197389 1420888262702008590449021)
                    ·
                      rfl

theorem cell22_4150755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 1, 3].length) (baseStart_4150755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150755 prefixEnd_4150755 := by exact prefixLift 4150755
  have htrace : WordTrace (prefixWord ++ tailWord_4150755) baseStart_4150755 baseEnd_4150755 := by
    simpa [prefixWord, tailWord_4150755, baseEnd_4150755] using wordTrace_append hprefix tailTrace_4150755
  have hstable : (prefixWord ++ tailWord_4150755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150755).length < 2 ^ (prefixWord ++ tailWord_4150755).sum := by decide
  have hdescent : baseEnd_4150755 < baseStart_4150755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150785 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 5]
def baseStart_4150785 : Nat := 118140960795 + 4150785 * 2 ^ 59
def prefixEnd_4150785 : Nat := 4983230072969 + 3 ^ 40 * 4150785 * 2
def baseEnd_4150785 : Nat := 473632844105032837399643

theorem tailTrace_4150785 : CollatzResearch.WordTrace tailWord_4150785 prefixEnd_4150785 473632844105032837399643 := by
  unfold tailWord_4150785
  simp only [CollatzResearch.WordTrace]
  refine ⟨151391566267422317484885809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100927710844948211656590539 151391566267422317484885809)
  ·
    refine ⟨113543674700566738113664357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151391566267422317484885809 113543674700566738113664357)
    ·
      refine ⟨21289439006356263396312067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113543674700566738113664357 21289439006356263396312067)
      ·
        refine ⟨31934158509534395094468101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21289439006356263396312067 31934158509534395094468101)
        ·
          refine ⟨5987654720537699080212769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31934158509534395094468101 5987654720537699080212769)
          ·
            refine ⟨4490741040403274310159577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5987654720537699080212769 4490741040403274310159577)
            ·
              refine ⟨3368055780302455732619683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4490741040403274310159577 3368055780302455732619683)
              ·
                refine ⟨5052083670453683598929525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368055780302455732619683 5052083670453683598929525)
                ·
                  refine ⟨473632844105032837399643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5052083670453683598929525 473632844105032837399643)
                  ·
                    rfl

theorem cell22_4150785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 5].length) (baseStart_4150785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150785 prefixEnd_4150785 := by exact prefixLift 4150785
  have htrace : WordTrace (prefixWord ++ tailWord_4150785) baseStart_4150785 baseEnd_4150785 := by
    simpa [prefixWord, tailWord_4150785, baseEnd_4150785] using wordTrace_append hprefix tailTrace_4150785
  have hstable : (prefixWord ++ tailWord_4150785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150785).length < 2 ^ (prefixWord ++ tailWord_4150785).sum := by decide
  have hdescent : baseEnd_4150785 < baseStart_4150785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150798 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_4150798 : Nat := 118140960795 + 4150798 * 2 ^ 59
def prefixEnd_4150798 : Nat := 4983230072969 + 3 ^ 40 * 4150798 * 2
def baseEnd_4150798 : Nat := 1420902982480770811623889

theorem tailTrace_4150798 : CollatzResearch.WordTrace tailWord_4150798 prefixEnd_4150798 1420902982480770811623889 := by
  unfold tailWord_4150798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18924005052046902588138631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100928026944250147136739365 18924005052046902588138631)
  ·
    refine ⟨28386007578070353882207947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18924005052046902588138631 28386007578070353882207947)
    ·
      refine ⟨42579011367105530823311921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28386007578070353882207947 42579011367105530823311921)
      ·
        refine ⟨31934258525329148117483941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42579011367105530823311921 31934258525329148117483941)
        ·
          refine ⟨5987673473499215272028239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31934258525329148117483941 5987673473499215272028239)
          ·
            refine ⟨8981510210248822908042359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987673473499215272028239 8981510210248822908042359)
            ·
              refine ⟨13472265315373234362063539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8981510210248822908042359 13472265315373234362063539)
              ·
                refine ⟨20208397973059851543095309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13472265315373234362063539 20208397973059851543095309)
                ·
                  refine ⟨7578149239897444328660741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20208397973059851543095309 7578149239897444328660741)
                  ·
                    refine ⟨1420902982480770811623889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7578149239897444328660741 1420902982480770811623889)
                    ·
                      rfl

theorem cell22_4150798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_4150798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150798 prefixEnd_4150798 := by exact prefixLift 4150798
  have htrace : WordTrace (prefixWord ++ tailWord_4150798) baseStart_4150798 baseEnd_4150798 := by
    simpa [prefixWord, tailWord_4150798, baseEnd_4150798] using wordTrace_append hprefix tailTrace_4150798
  have hstable : (prefixWord ++ tailWord_4150798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150798).length < 2 ^ (prefixWord ++ tailWord_4150798).sum := by decide
  have hdescent : baseEnd_4150798 < baseStart_4150798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150813 : List Nat := [1, 4, 2, 2, 1, 1, 2, 5, 4]
def baseStart_4150813 : Nat := 118140960795 + 4150813 * 2 ^ 59
def prefixEnd_4150813 : Nat := 4983230072969 + 3 ^ 40 * 4150813 * 2
def baseEnd_4150813 : Nat := 473636039095771924166281

theorem tailTrace_4150813 : CollatzResearch.WordTrace tailWord_4150813 prefixEnd_4150813 473636039095771924166281 := by
  unfold tailWord_4150813
  simp only [CollatzResearch.WordTrace]
  refine ⟨151392587511320878266905093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100928391674213918844603395 151392587511320878266905093)
  ·
    refine ⟨28386110158372664675044705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151392587511320878266905093 28386110158372664675044705)
    ·
      refine ⟨21289582618779498506283529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28386110158372664675044705 21289582618779498506283529)
      ·
        refine ⟨15967186964084623879712647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21289582618779498506283529 15967186964084623879712647)
        ·
          refine ⟨23950780446126935819568971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15967186964084623879712647 23950780446126935819568971)
          ·
            refine ⟨35926170669190403729353457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23950780446126935819568971 35926170669190403729353457)
            ·
              refine ⟨26944628001892802797015093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35926170669190403729353457 26944628001892802797015093)
              ·
                refine ⟨2526058875177450262220165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26944628001892802797015093 2526058875177450262220165)
                ·
                  refine ⟨473636039095771924166281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526058875177450262220165 473636039095771924166281)
                  ·
                    rfl

theorem cell22_4150813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_4150813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150813 prefixEnd_4150813 := by exact prefixLift 4150813
  have htrace : WordTrace (prefixWord ++ tailWord_4150813) baseStart_4150813 baseEnd_4150813 := by
    simpa [prefixWord, tailWord_4150813, baseEnd_4150813] using wordTrace_append hprefix tailTrace_4150813
  have hstable : (prefixWord ++ tailWord_4150813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150813).length < 2 ^ (prefixWord ++ tailWord_4150813).sum := by decide
  have hdescent : baseEnd_4150813 < baseStart_4150813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150830 : List Nat := [4, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_4150830 : Nat := 118140960795 + 4150830 * 2 ^ 59
def prefixEnd_4150830 : Nat := 4983230072969 + 3 ^ 40 * 4150830 * 2
def baseEnd_4150830 : Nat := 473637978911577798274597

theorem tailTrace_4150830 : CollatzResearch.WordTrace tailWord_4150830 prefixEnd_4150830 473637978911577798274597 := by
  unfold tailWord_4150830
  simp only [CollatzResearch.WordTrace]
  refine ⟨18924150944032411271284243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100928805034839526780182629 18924150944032411271284243)
  ·
    refine ⟨28386226416048616906926365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18924150944032411271284243 28386226416048616906926365)
    ·
      refine ⟨10644834906018231340097387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28386226416048616906926365 10644834906018231340097387)
      ·
        refine ⟨15967252359027347010146081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10644834906018231340097387 15967252359027347010146081)
        ·
          refine ⟨11975439269270510257609561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15967252359027347010146081 11975439269270510257609561)
          ·
            refine ⟨8981579451952882693207171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11975439269270510257609561 8981579451952882693207171)
            ·
              refine ⟨13472369177929324039810757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8981579451952882693207171 13472369177929324039810757)
              ·
                refine ⟨2526069220861748257464517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13472369177929324039810757 2526069220861748257464517)
                ·
                  refine ⟨473637978911577798274597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526069220861748257464517 473637978911577798274597)
                  ·
                    rfl

theorem cell22_4150830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_4150830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150830 prefixEnd_4150830 := by exact prefixLift 4150830
  have htrace : WordTrace (prefixWord ++ tailWord_4150830) baseStart_4150830 baseEnd_4150830 := by
    simpa [prefixWord, tailWord_4150830, baseEnd_4150830] using wordTrace_append hprefix tailTrace_4150830
  have hstable : (prefixWord ++ tailWord_4150830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150830).length < 2 ^ (prefixWord ++ tailWord_4150830).sum := by decide
  have hdescent : baseEnd_4150830 < baseStart_4150830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150841 : List Nat := [1, 2, 1, 5, 1, 2, 3, 7]
def baseStart_4150841 : Nat := 118140960795 + 4150841 * 2 ^ 59
def prefixEnd_4150841 : Nat := 4983230072969 + 3 ^ 40 * 4150841 * 2
def baseEnd_4150841 : Nat := 157879744695503670310973

theorem tailTrace_4150841 : CollatzResearch.WordTrace tailWord_4150841 prefixEnd_4150841 157879744695503670310973 := by
  unfold tailWord_4150841
  simp only [CollatzResearch.WordTrace]
  refine ⟨151393608755219439048924377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100929072503479626032616251 151393608755219439048924377)
  ·
    refine ⟨113545206566414579286693283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151393608755219439048924377 113545206566414579286693283)
    ·
      refine ⟨170317809849621868930039925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113545206566414579286693283 170317809849621868930039925)
      ·
        refine ⟨15967294673402050212191243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170317809849621868930039925 15967294673402050212191243)
        ·
          refine ⟨23950942010103075318286865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15967294673402050212191243 23950942010103075318286865)
          ·
            refine ⟨17963206507577306488715149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23950942010103075318286865 17963206507577306488715149)
            ·
              refine ⟨6736202440341489933268181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17963206507577306488715149 6736202440341489933268181)
              ·
                refine ⟨157879744695503670310973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6736202440341489933268181 157879744695503670310973)
                ·
                  rfl

theorem cell22_4150841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 7].length) (baseStart_4150841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150841 prefixEnd_4150841 := by exact prefixLift 4150841
  have htrace : WordTrace (prefixWord ++ tailWord_4150841) baseStart_4150841 baseEnd_4150841 := by
    simpa [prefixWord, tailWord_4150841, baseEnd_4150841] using wordTrace_append hprefix tailTrace_4150841
  have hstable : (prefixWord ++ tailWord_4150841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150841).length < 2 ^ (prefixWord ++ tailWord_4150841).sum := by decide
  have hdescent : baseEnd_4150841 < baseStart_4150841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150890 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 3, 3]
def baseStart_4150890 : Nat := 118140960795 + 4150890 * 2 ^ 59
def prefixEnd_4150890 : Nat := 4983230072969 + 3 ^ 40 * 4150890 * 2
def baseEnd_4150890 : Nat := 1420934475960913238323607

theorem tailTrace_4150890 : CollatzResearch.WordTrace tailWord_4150890 prefixEnd_4150890 1420934475960913238323607 := by
  unfold tailWord_4150890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37848848983010480104364531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100930263954694613611638749 37848848983010480104364531)
  ·
    refine ⟨56773273474515720156546797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37848848983010480104364531 56773273474515720156546797)
    ·
      refine ⟨21289977552943395058705049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56773273474515720156546797 21289977552943395058705049)
      ·
        refine ⟨15967483164707546294028787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21289977552943395058705049 15967483164707546294028787)
        ·
          refine ⟨23951224747061319441043181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15967483164707546294028787 23951224747061319441043181)
          ·
            refine ⟨8981709280147994790391193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23951224747061319441043181 8981709280147994790391193)
            ·
              refine ⟨6736281960110996092793395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8981709280147994790391193 6736281960110996092793395)
              ·
                refine ⟨10104422940166494139190093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736281960110996092793395 10104422940166494139190093)
                ·
                  refine ⟨3789158602562435302196285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10104422940166494139190093 3789158602562435302196285)
                  ·
                    refine ⟨1420934475960913238323607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789158602562435302196285 1420934475960913238323607)
                    ·
                      rfl

theorem cell22_4150890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_4150890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150890 prefixEnd_4150890 := by exact prefixLift 4150890
  have htrace : WordTrace (prefixWord ++ tailWord_4150890) baseStart_4150890 baseEnd_4150890 := by
    simpa [prefixWord, tailWord_4150890, baseEnd_4150890] using wordTrace_append hprefix tailTrace_4150890
  have hstable : (prefixWord ++ tailWord_4150890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150890).length < 2 ^ (prefixWord ++ tailWord_4150890).sum := by decide
  have hdescent : baseEnd_4150890 < baseStart_4150890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150948 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 6]
def baseStart_4150948 : Nat := 118140960795 + 4150948 * 2 ^ 59
def prefixEnd_4150948 : Nat := 4983230072969 + 3 ^ 40 * 4150948 * 2
def baseEnd_4150948 : Nat := 473651443515406806791143

theorem tailTrace_4150948 : CollatzResearch.WordTrace tailWord_4150948 prefixEnd_4150948 473651443515406806791143 := by
  unfold tailWord_4150948
  simp only [CollatzResearch.WordTrace]
  refine ⟨75698755682915898161534749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100931674243887864215379665 75698755682915898161534749)
  ·
    refine ⟨28387033381093461810575531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75698755682915898161534749 28387033381093461810575531)
    ·
      refine ⟨42580550071640192715863297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28387033381093461810575531 42580550071640192715863297)
      ·
        refine ⟨31935412553730144536897473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42580550071640192715863297 31935412553730144536897473)
        ·
          refine ⟨23951559415297608402673105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31935412553730144536897473 23951559415297608402673105)
          ·
            refine ⟨17963669561473206302004829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23951559415297608402673105 17963669561473206302004829)
            ·
              refine ⟨6736376085552452363251811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17963669561473206302004829 6736376085552452363251811)
              ·
                refine ⟨10104564128328678544877717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736376085552452363251811 10104564128328678544877717)
                ·
                  refine ⟨473651443515406806791143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10104564128328678544877717 473651443515406806791143)
                  ·
                    rfl

theorem cell22_4150948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_4150948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150948 prefixEnd_4150948 := by exact prefixLift 4150948
  have htrace : WordTrace (prefixWord ++ tailWord_4150948) baseStart_4150948 baseEnd_4150948 := by
    simpa [prefixWord, tailWord_4150948, baseEnd_4150948] using wordTrace_append hprefix tailTrace_4150948
  have hstable : (prefixWord ++ tailWord_4150948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150948).length < 2 ^ (prefixWord ++ tailWord_4150948).sum := by decide
  have hdescent : baseEnd_4150948 < baseStart_4150948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150976 : List Nat := [2, 1, 1, 2, 4, 1, 1, 10]
def baseStart_4150976 : Nat := 118140960795 + 4150976 * 2 ^ 59
def prefixEnd_4150976 : Nat := 4983230072969 + 3 ^ 40 * 4150976 * 2
def baseEnd_4150976 : Nat := 157884879502048631185927

theorem tailTrace_4150976 : CollatzResearch.WordTrace tailWord_4150976 prefixEnd_4150976 157884879502048631185927 := by
  unfold tailWord_4150976
  simp only [CollatzResearch.WordTrace]
  refine ⟨75699266304865178552544391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100932355073153571403392521 75699266304865178552544391)
  ·
    refine ⟨113548899457297767828816587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75699266304865178552544391 113548899457297767828816587)
    ·
      refine ⟨170323349185946651743224881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113548899457297767828816587 170323349185946651743224881)
      ·
        refine ⟨127742511889459988807418661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170323349185946651743224881 127742511889459988807418661)
        ·
          refine ⟨23951720979273747901390999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127742511889459988807418661 23951720979273747901390999)
          ·
            refine ⟨35927581468910621852086499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23951720979273747901390999 35927581468910621852086499)
            ·
              refine ⟨53891372203365932778129749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35927581468910621852086499 53891372203365932778129749)
              ·
                refine ⟨157884879502048631185927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53891372203365932778129749 157884879502048631185927)
                ·
                  rfl

theorem cell22_4150976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 10].length) (baseStart_4150976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4150976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4150976 prefixEnd_4150976 := by exact prefixLift 4150976
  have htrace : WordTrace (prefixWord ++ tailWord_4150976) baseStart_4150976 baseEnd_4150976 := by
    simpa [prefixWord, tailWord_4150976, baseEnd_4150976] using wordTrace_append hprefix tailTrace_4150976
  have hstable : (prefixWord ++ tailWord_4150976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150976).length < 2 ^ (prefixWord ++ tailWord_4150976).sum := by decide
  have hdescent : baseEnd_4150976 < baseStart_4150976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151025 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 3, 3]
def baseStart_4151025 : Nat := 118140960795 + 4151025 * 2 ^ 59
def prefixEnd_4151025 : Nat := 4983230072969 + 3 ^ 40 * 4151025 * 2
def baseEnd_4151025 : Nat := 1420980689219817886198193

theorem tailTrace_4151025 : CollatzResearch.WordTrace tailWord_4151025 prefixEnd_4151025 1420980689219817886198193 := by
  unfold tailWord_4151025
  simp only [CollatzResearch.WordTrace]
  refine ⟨151400319786552838473622529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100933546524368558982415019 151400319786552838473622529)
  ·
    refine ⟨113550239839914628855216897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151400319786552838473622529 113550239839914628855216897)
    ·
      refine ⟨85162679879935971641412673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113550239839914628855216897 85162679879935971641412673)
      ·
        refine ⟨63872009909951978731059505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85162679879935971641412673 63872009909951978731059505)
        ·
          refine ⟨47904007432463984048294629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63872009909951978731059505 47904007432463984048294629)
          ·
            refine ⟨8982001393586997009055243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47904007432463984048294629 8982001393586997009055243)
            ·
              refine ⟨13473002090380495513582865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8982001393586997009055243 13473002090380495513582865)
              ·
                refine ⟨10104751567785371635187149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13473002090380495513582865 10104751567785371635187149)
                ·
                  refine ⟨3789281837919514363195181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10104751567785371635187149 3789281837919514363195181)
                  ·
                    refine ⟨1420980689219817886198193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789281837919514363195181 1420980689219817886198193)
                    ·
                      rfl

theorem cell22_4151025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_4151025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151025 prefixEnd_4151025 := by exact prefixLift 4151025
  have htrace : WordTrace (prefixWord ++ tailWord_4151025) baseStart_4151025 baseEnd_4151025 := by
    simpa [prefixWord, tailWord_4151025, baseEnd_4151025] using wordTrace_append hprefix tailTrace_4151025
  have hstable : (prefixWord ++ tailWord_4151025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151025).length < 2 ^ (prefixWord ++ tailWord_4151025).sum := by decide
  have hdescent : baseEnd_4151025 < baseStart_4151025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151102 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4151102 : Nat := 118140960795 + 4151102 * 2 ^ 59
def prefixEnd_4151102 : Nat := 4983230072969 + 3 ^ 40 * 4151102 * 2
def baseEnd_4151102 : Nat := 1421007047893415352022957

theorem tailTrace_4151102 : CollatzResearch.WordTrace tailWord_4151102 prefixEnd_4151102 1421007047893415352022957 := by
  unfold tailWord_4151102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18925391025909235078021945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100935418804849253749450373 18925391025909235078021945)
  ·
    refine ⟨14194043269431926308516459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18925391025909235078021945 14194043269431926308516459)
    ·
      refine ⟨21291064904147889462774689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14194043269431926308516459 21291064904147889462774689)
      ·
        refine ⟨15968298678110917097081017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21291064904147889462774689 15968298678110917097081017)
        ·
          refine ⟨11976224008583187822810763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15968298678110917097081017 11976224008583187822810763)
          ·
            refine ⟨17964336012874781734216145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11976224008583187822810763 17964336012874781734216145)
            ·
              refine ⟨13473252009656086300662109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17964336012874781734216145 13473252009656086300662109)
              ·
                refine ⟨5052469503621032362748291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13473252009656086300662109 5052469503621032362748291)
                ·
                  refine ⟨7578704255431548544122437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052469503621032362748291 7578704255431548544122437)
                  ·
                    refine ⟨1421007047893415352022957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7578704255431548544122437 1421007047893415352022957)
                    ·
                      rfl

theorem cell22_4151102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4151102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151102 prefixEnd_4151102 := by exact prefixLift 4151102
  have htrace : WordTrace (prefixWord ++ tailWord_4151102) baseStart_4151102 baseEnd_4151102 := by
    simpa [prefixWord, tailWord_4151102, baseEnd_4151102] using wordTrace_append hprefix tailTrace_4151102
  have hstable : (prefixWord ++ tailWord_4151102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151102).length < 2 ^ (prefixWord ++ tailWord_4151102).sum := by decide
  have hdescent : baseEnd_4151102 < baseStart_4151102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151117 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4151117 : Nat := 118140960795 + 4151117 * 2 ^ 59
def prefixEnd_4151117 : Nat := 4983230072969 + 3 ^ 40 * 4151117 * 2
def baseEnd_4151117 : Nat := 473670727566653437632637

theorem tailTrace_4151117 : CollatzResearch.WordTrace tailWord_4151117 prefixEnd_4151117 473670727566653437632637 := by
  unfold tailWord_4151117
  simp only [CollatzResearch.WordTrace]
  refine ⟨151403675302219538185971605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100935783534813025457314403 151403675302219538185971605)
  ·
    refine ⟨7097047279791540852467419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151403675302219538185971605 7097047279791540852467419)
    ·
      refine ⟨10645570919687311278701129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7097047279791540852467419 10645570919687311278701129)
      ·
        refine ⟨7984178189765483459025847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10645570919687311278701129 7984178189765483459025847)
        ·
          refine ⟨11976267284648225188538771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7984178189765483459025847 11976267284648225188538771)
          ·
            refine ⟨17964400926972337782808157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11976267284648225188538771 17964400926972337782808157)
            ·
              refine ⟨6736650347614626668553059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17964400926972337782808157 6736650347614626668553059)
              ·
                refine ⟨10104975521421940002829589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736650347614626668553059 10104975521421940002829589)
                ·
                  refine ⟨473670727566653437632637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10104975521421940002829589 473670727566653437632637)
                  ·
                    rfl

theorem cell22_4151117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4151117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151117 prefixEnd_4151117 := by exact prefixLift 4151117
  have htrace : WordTrace (prefixWord ++ tailWord_4151117) baseStart_4151117 baseEnd_4151117 := by
    simpa [prefixWord, tailWord_4151117, baseEnd_4151117] using wordTrace_append hprefix tailTrace_4151117
  have hstable : (prefixWord ++ tailWord_4151117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151117).length < 2 ^ (prefixWord ++ tailWord_4151117).sum := by decide
  have hdescent : baseEnd_4151117 < baseStart_4151117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151166 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_4151166 : Nat := 118140960795 + 4151166 * 2 ^ 59
def prefixEnd_4151166 : Nat := 4983230072969 + 3 ^ 40 * 4151166 * 2
def baseEnd_4151166 : Nat := 1421028956401340518422761

theorem tailTrace_4151166 : CollatzResearch.WordTrace tailWord_4151166 prefixEnd_4151166 1421028956401340518422761 := by
  unfold tailWord_4151166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18925682809880252444313169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100936974986028013036336901 18925682809880252444313169)
  ·
    refine ⟨14194262107410189333234877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18925682809880252444313169 14194262107410189333234877)
    ·
      refine ⟨5322848290278820999963079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14194262107410189333234877 5322848290278820999963079)
      ·
        refine ⟨7984272435418231499944619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5322848290278820999963079 7984272435418231499944619)
        ·
          refine ⟨11976408653127347249916929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7984272435418231499944619 11976408653127347249916929)
          ·
            refine ⟨8982306489845510437437697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11976408653127347249916929 8982306489845510437437697)
            ·
              refine ⟨6736729867384132828078273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8982306489845510437437697 6736729867384132828078273)
              ·
                refine ⟨5052547400538099621058705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6736729867384132828078273 5052547400538099621058705)
                ·
                  refine ⟨3789410550403574715794029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5052547400538099621058705 3789410550403574715794029)
                  ·
                    refine ⟨1421028956401340518422761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789410550403574715794029 1421028956401340518422761)
                    ·
                      rfl

theorem cell22_4151166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_4151166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151166 prefixEnd_4151166 := by exact prefixLift 4151166
  have htrace : WordTrace (prefixWord ++ tailWord_4151166) baseStart_4151166 baseEnd_4151166 := by
    simpa [prefixWord, tailWord_4151166, baseEnd_4151166] using wordTrace_append hprefix tailTrace_4151166
  have hstable : (prefixWord ++ tailWord_4151166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151166).length < 2 ^ (prefixWord ++ tailWord_4151166).sum := by decide
  have hdescent : baseEnd_4151166 < baseStart_4151166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151198 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_4151198 : Nat := 118140960795 + 4151198 * 2 ^ 59
def prefixEnd_4151198 : Nat := 4983230072969 + 3 ^ 40 * 4151198 * 2
def baseEnd_4151198 : Nat := 1421039910655303101622663

theorem tailTrace_4151198 : CollatzResearch.WordTrace tailWord_4151198 prefixEnd_4151198 1421039910655303101622663 := by
  unfold tailWord_4151198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18925828701865761127458781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100937753076617392679780165 18925828701865761127458781)
  ·
    refine ⟨7097185763199660422797043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18925828701865761127458781 7097185763199660422797043)
    ·
      refine ⟨10645778644799490634195565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7097185763199660422797043 10645778644799490634195565)
      ·
        refine ⟨3992166991799808987823337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10645778644799490634195565 3992166991799808987823337)
        ·
          refine ⟨2994125243849856740867503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3992166991799808987823337 2994125243849856740867503)
          ·
            refine ⟨4491187865774785111301255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994125243849856740867503 4491187865774785111301255)
            ·
              refine ⟨6736781798662177666951883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491187865774785111301255 6736781798662177666951883)
              ·
                refine ⟨10105172697993266500427825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736781798662177666951883 10105172697993266500427825)
                ·
                  refine ⟨7578879523494949875320869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10105172697993266500427825 7578879523494949875320869)
                  ·
                    refine ⟨1421039910655303101622663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7578879523494949875320869 1421039910655303101622663)
                    ·
                      rfl

theorem cell22_4151198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_4151198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151198 prefixEnd_4151198 := by exact prefixLift 4151198
  have htrace : WordTrace (prefixWord ++ tailWord_4151198) baseStart_4151198 baseEnd_4151198 := by
    simpa [prefixWord, tailWord_4151198, baseEnd_4151198] using wordTrace_append hprefix tailTrace_4151198
  have hstable : (prefixWord ++ tailWord_4151198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151198).length < 2 ^ (prefixWord ++ tailWord_4151198).sum := by decide
  have hdescent : baseEnd_4151198 < baseStart_4151198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151265 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_4151265 : Nat := 118140960795 + 4151265 * 2 ^ 59
def prefixEnd_4151265 : Nat := 4983230072969 + 3 ^ 40 * 4151265 * 2
def baseEnd_4151265 : Nat := 1421062846124537260197457

theorem tailTrace_4151265 : CollatzResearch.WordTrace tailWord_4151265 prefixEnd_4151265 1421062846124537260197457 := by
  unfold tailWord_4151265
  simp only [CollatzResearch.WordTrace]
  refine ⟨151409073305683359462359249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100939382203788906308239499 151409073305683359462359249)
  ·
    refine ⟨113556804979262519596769437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151409073305683359462359249 113556804979262519596769437)
    ·
      refine ⟨42583801867223444848788539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113556804979262519596769437 42583801867223444848788539)
      ·
        refine ⟨63875702800835167273182809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42583801867223444848788539 63875702800835167273182809)
        ·
          refine ⟨47906777100626375454887107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63875702800835167273182809 47906777100626375454887107)
          ·
            refine ⟨71860165650939563182330661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47906777100626375454887107 71860165650939563182330661)
            ·
              refine ⟨13473781059551168096686999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71860165650939563182330661 13473781059551168096686999)
              ·
                refine ⟨20210671589326752145030499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13473781059551168096686999 20210671589326752145030499)
                ·
                  refine ⟨30316007383990128217545749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20210671589326752145030499 30316007383990128217545749)
                  ·
                    refine ⟨1421062846124537260197457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30316007383990128217545749 1421062846124537260197457)
                    ·
                      rfl

theorem cell22_4151265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_4151265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151265 prefixEnd_4151265 := by exact prefixLift 4151265
  have htrace : WordTrace (prefixWord ++ tailWord_4151265) baseStart_4151265 baseEnd_4151265 := by
    simpa [prefixWord, tailWord_4151265, baseEnd_4151265] using wordTrace_append hprefix tailTrace_4151265
  have hstable : (prefixWord ++ tailWord_4151265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151265).length < 2 ^ (prefixWord ++ tailWord_4151265).sum := by decide
  have hdescent : baseEnd_4151265 < baseStart_4151265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151267 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 4, 3]
def baseStart_4151267 : Nat := 118140960795 + 4151267 * 2 ^ 59
def prefixEnd_4151267 : Nat := 4983230072969 + 3 ^ 40 * 4151267 * 2
def baseEnd_4151267 : Nat := 1421063530765409921647451

theorem tailTrace_4151267 : CollatzResearch.WordTrace tailWord_4151267 prefixEnd_4151267 1421063530765409921647451 := by
  unfold tailWord_4151267
  simp only [CollatzResearch.WordTrace]
  refine ⟨151409146251676113803932055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100939430834450742535954703 151409146251676113803932055)
  ·
    refine ⟨227113719377514170705898083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151409146251676113803932055 227113719377514170705898083)
    ·
      refine ⟨340670579066271256058847125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227113719377514170705898083 340670579066271256058847125)
      ·
        refine ⟨15968933393731465127758459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 340670579066271256058847125 15968933393731465127758459)
        ·
          refine ⟨23953400090597197691637689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15968933393731465127758459 23953400090597197691637689)
          ·
            refine ⟨17965050067947898268728267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23953400090597197691637689 17965050067947898268728267)
            ·
              refine ⟨26947575101921847403092401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17965050067947898268728267 26947575101921847403092401)
              ·
                refine ⟨20210681326441385552319301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26947575101921847403092401 20210681326441385552319301)
                ·
                  refine ⟨3789502748707759791059869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20210681326441385552319301 3789502748707759791059869)
                  ·
                    refine ⟨1421063530765409921647451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789502748707759791059869 1421063530765409921647451)
                    ·
                      rfl

theorem cell22_4151267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 3].length) (baseStart_4151267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151267 prefixEnd_4151267 := by exact prefixLift 4151267
  have htrace : WordTrace (prefixWord ++ tailWord_4151267) baseStart_4151267 baseEnd_4151267 := by
    simpa [prefixWord, tailWord_4151267, baseEnd_4151267] using wordTrace_append hprefix tailTrace_4151267
  have hstable : (prefixWord ++ tailWord_4151267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151267).length < 2 ^ (prefixWord ++ tailWord_4151267).sum := by decide
  have hdescent : baseEnd_4151267 < baseStart_4151267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151286 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_4151286 : Nat := 118140960795 + 4151286 * 2 ^ 59
def prefixEnd_4151286 : Nat := 4983230072969 + 3 ^ 40 * 4151286 * 2
def baseEnd_4151286 : Nat := 473690011617900068474131

theorem tailTrace_4151286 : CollatzResearch.WordTrace tailWord_4151286 prefixEnd_4151286 473690011617900068474131 := by
  unfold tailWord_4151286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9463114952412955003054607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100939892825738186699249141 9463114952412955003054607)
  ·
    refine ⟨14194672428619432504581911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9463114952412955003054607 14194672428619432504581911)
    ·
      refine ⟨21292008642929148756872867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14194672428619432504581911 21292008642929148756872867)
      ·
        refine ⟨31938012964393723135309301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21292008642929148756872867 31938012964393723135309301)
        ·
          refine ⟨2994188715411911543935247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31938012964393723135309301 2994188715411911543935247)
          ·
            refine ⟨4491283073117867315902871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994188715411911543935247 4491283073117867315902871)
            ·
              refine ⟨6736924609676800973854307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491283073117867315902871 6736924609676800973854307)
              ·
                refine ⟨10105386914515201460781461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736924609676800973854307 10105386914515201460781461)
                ·
                  refine ⟨473690011617900068474131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10105386914515201460781461 473690011617900068474131)
                  ·
                    rfl

theorem cell22_4151286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_4151286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151286 prefixEnd_4151286 := by exact prefixLift 4151286
  have htrace : WordTrace (prefixWord ++ tailWord_4151286) baseStart_4151286 baseEnd_4151286 := by
    simpa [prefixWord, tailWord_4151286, baseEnd_4151286] using wordTrace_append hprefix tailTrace_4151286
  have hstable : (prefixWord ++ tailWord_4151286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151286).length < 2 ^ (prefixWord ++ tailWord_4151286).sum := by decide
  have hdescent : baseEnd_4151286 < baseStart_4151286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151301 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 2, 3]
def baseStart_4151301 : Nat := 118140960795 + 4151301 * 2 ^ 59
def prefixEnd_4151301 : Nat := 4983230072969 + 3 ^ 40 * 4151301 * 2
def baseEnd_4151301 : Nat := 1421075169660245166297347

theorem tailTrace_4151301 : CollatzResearch.WordTrace tailWord_4151301 prefixEnd_4151301 1421075169660245166297347 := by
  unfold tailWord_4151301
  simp only [CollatzResearch.WordTrace]
  refine ⟨151410386333552937610669757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100940257555701958407113171 151410386333552937610669757)
  ·
    refine ⟨56778894875082351604001159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151410386333552937610669757 56778894875082351604001159)
    ·
      refine ⟨85168342312623527406001739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56778894875082351604001159 85168342312623527406001739)
      ·
        refine ⟨127752513468935291109002609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85168342312623527406001739 127752513468935291109002609)
        ·
          refine ⟨95814385101701468331751957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127752513468935291109002609 95814385101701468331751957)
          ·
            refine ⟨4491299301642256328050873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95814385101701468331751957 4491299301642256328050873)
            ·
              refine ⟨3368474476231692246038155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491299301642256328050873 3368474476231692246038155)
              ·
                refine ⟨5052711714347538369057233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368474476231692246038155 5052711714347538369057233)
                ·
                  refine ⟨3789533785760653776792925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5052711714347538369057233 3789533785760653776792925)
                  ·
                    refine ⟨1421075169660245166297347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789533785760653776792925 1421075169660245166297347)
                    ·
                      rfl

theorem cell22_4151301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_4151301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151301 prefixEnd_4151301 := by exact prefixLift 4151301
  have htrace : WordTrace (prefixWord ++ tailWord_4151301) baseStart_4151301 baseEnd_4151301 := by
    simpa [prefixWord, tailWord_4151301, baseEnd_4151301] using wordTrace_append hprefix tailTrace_4151301
  have hstable : (prefixWord ++ tailWord_4151301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151301).length < 2 ^ (prefixWord ++ tailWord_4151301).sum := by decide
  have hdescent : baseEnd_4151301 < baseStart_4151301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151346 : List Nat := [3, 2, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_4151346 : Nat := 118140960795 + 4151346 * 2 ^ 59
def prefixEnd_4151346 : Nat := 4983230072969 + 3 ^ 40 * 4151346 * 2
def baseEnd_4151346 : Nat := 1421090574079880048922209

theorem tailTrace_4151346 : CollatzResearch.WordTrace tailWord_4151346 prefixEnd_4151346 1421090574079880048922209 := by
  unfold tailWord_4151346
  simp only [CollatzResearch.WordTrace]
  refine ⟨37853006904597477574014473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100941351745593273530705261 37853006904597477574014473)
  ·
    refine ⟨28389755178448108180510855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37853006904597477574014473 28389755178448108180510855)
    ·
      refine ⟨42584632767672162270766283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28389755178448108180510855 42584632767672162270766283)
      ·
        refine ⟨63876949151508243406149425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42584632767672162270766283 63876949151508243406149425)
        ·
          refine ⟨47907711863631182554612069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63876949151508243406149425 47907711863631182554612069)
          ·
            refine ⟨8982695974430846728989763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47907711863631182554612069 8982695974430846728989763)
            ·
              refine ⟨13474043961646270093484645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8982695974430846728989763 13474043961646270093484645)
              ·
                refine ⟨2526383242808675642528371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13474043961646270093484645 2526383242808675642528371)
                ·
                  refine ⟨3789574864213013463792557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526383242808675642528371 3789574864213013463792557)
                  ·
                    refine ⟨1421090574079880048922209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789574864213013463792557 1421090574079880048922209)
                    ·
                      rfl

theorem cell22_4151346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_4151346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151346 prefixEnd_4151346 := by exact prefixLift 4151346
  have htrace : WordTrace (prefixWord ++ tailWord_4151346) baseStart_4151346 baseEnd_4151346 := by
    simpa [prefixWord, tailWord_4151346, baseEnd_4151346] using wordTrace_append hprefix tailTrace_4151346
  have hstable : (prefixWord ++ tailWord_4151346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151346).length < 2 ^ (prefixWord ++ tailWord_4151346).sum := by decide
  have hdescent : baseEnd_4151346 < baseStart_4151346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151357 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_4151357 : Nat := 118140960795 + 4151357 * 2 ^ 59
def prefixEnd_4151357 : Nat := 4983230072969 + 3 ^ 40 * 4151357 * 2
def baseEnd_4151357 : Nat := 1421094339604679686897175

theorem tailTrace_4151357 : CollatzResearch.WordTrace tailWord_4151357 prefixEnd_4151357 1421094339604679686897175 := by
  unfold tailWord_4151357
  simp only [CollatzResearch.WordTrace]
  refine ⟨151412428821350059174708325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100941619214233372783138883 151412428821350059174708325)
  ·
    refine ⟨28389830404003136095257811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151412428821350059174708325 28389830404003136095257811)
    ·
      refine ⟨42584745606004704142886717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28389830404003136095257811 42584745606004704142886717)
      ·
        refine ⟨15969279602251764053582519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42584745606004704142886717 15969279602251764053582519)
        ·
          refine ⟨23953919403377646080373779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15969279602251764053582519 23953919403377646080373779)
          ·
            refine ⟨35930879105066469120560669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23953919403377646080373779 35930879105066469120560669)
            ·
              refine ⟨13474079664399925920210251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35930879105066469120560669 13474079664399925920210251)
              ·
                refine ⟨20211119496599888880315377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13474079664399925920210251 20211119496599888880315377)
                ·
                  refine ⟨15158339622449916660236533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20211119496599888880315377 15158339622449916660236533)
                  ·
                    refine ⟨1421094339604679686897175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15158339622449916660236533 1421094339604679686897175)
                    ·
                      rfl

theorem cell22_4151357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_4151357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151357 prefixEnd_4151357 := by exact prefixLift 4151357
  have htrace : WordTrace (prefixWord ++ tailWord_4151357) baseStart_4151357 baseEnd_4151357 := by
    simpa [prefixWord, tailWord_4151357, baseEnd_4151357] using wordTrace_append hprefix tailTrace_4151357
  have hstable : (prefixWord ++ tailWord_4151357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151357).length < 2 ^ (prefixWord ++ tailWord_4151357).sum := by decide
  have hdescent : baseEnd_4151357 < baseStart_4151357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151372 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_4151372 : Nat := 118140960795 + 4151372 * 2 ^ 59
def prefixEnd_4151372 : Nat := 4983230072969 + 3 ^ 40 * 4151372 * 2
def baseEnd_4151372 : Nat := 1421099474411224647772129

theorem tailTrace_4151372 : CollatzResearch.WordTrace tailWord_4151372 prefixEnd_4151372 1421099474411224647772129 := by
  unfold tailWord_4151372
  simp only [CollatzResearch.WordTrace]
  refine ⟨75706487958147858368252185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100941983944197144491002913 75706487958147858368252185)
  ·
    refine ⟨56779865968610893776189139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75706487958147858368252185 56779865968610893776189139)
    ·
      refine ⟨85169798952916340664283709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56779865968610893776189139 85169798952916340664283709)
      ·
        refine ⟨31938674607343627749106391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85169798952916340664283709 31938674607343627749106391)
        ·
          refine ⟨47908011911015441623659587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31938674607343627749106391 47908011911015441623659587)
          ·
            refine ⟨71862017866523162435489381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47908011911015441623659587 71862017866523162435489381)
            ·
              refine ⟨13474128349973092956654259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71862017866523162435489381 13474128349973092956654259)
              ·
                refine ⟨20211192524959639434981389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13474128349973092956654259 20211192524959639434981389)
                ·
                  refine ⟨7579197196859864788118021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20211192524959639434981389 7579197196859864788118021)
                  ·
                    refine ⟨1421099474411224647772129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7579197196859864788118021 1421099474411224647772129)
                    ·
                      rfl

theorem cell22_4151372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_4151372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151372 prefixEnd_4151372 := by exact prefixLift 4151372
  have htrace : WordTrace (prefixWord ++ tailWord_4151372) baseStart_4151372 baseEnd_4151372 := by
    simpa [prefixWord, tailWord_4151372, baseEnd_4151372] using wordTrace_append hprefix tailTrace_4151372
  have hstable : (prefixWord ++ tailWord_4151372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151372).length < 2 ^ (prefixWord ++ tailWord_4151372).sum := by decide
  have hdescent : baseEnd_4151372 < baseStart_4151372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151404 : List Nat := [2, 2, 1, 1, 3, 3, 2, 4, 4]
def baseStart_4151404 : Nat := 118140960795 + 4151404 * 2 ^ 59
def prefixEnd_4151404 : Nat := 4983230072969 + 3 ^ 40 * 4151404 * 2
def baseEnd_4151404 : Nat := 473703476221729076990677

theorem tailTrace_4151404 : CollatzResearch.WordTrace tailWord_4151404 prefixEnd_4151404 473703476221729076990677 := by
  unfold tailWord_4151404
  simp only [CollatzResearch.WordTrace]
  refine ⟨75707071526089893100834633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100942762034786524134446177 75707071526089893100834633)
  ·
    refine ⟨56780303644567419825625975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75707071526089893100834633 56780303644567419825625975)
    ·
      refine ⟨85170455466851129738438963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56780303644567419825625975 85170455466851129738438963)
      ·
        refine ⟨127755683200276694607658445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85170455466851129738438963 127755683200276694607658445)
        ·
          refine ⟨47908381200103760477871917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127755683200276694607658445 47908381200103760477871917)
          ·
            refine ⟨17965642950038910179201969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47908381200103760477871917 17965642950038910179201969)
            ·
              refine ⟨13474232212529182634401477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17965642950038910179201969 13474232212529182634401477)
              ·
                refine ⟨2526418539849221743950277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13474232212529182634401477 2526418539849221743950277)
                ·
                  refine ⟨473703476221729076990677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526418539849221743950277 473703476221729076990677)
                  ·
                    rfl

theorem cell22_4151404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_4151404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151404 prefixEnd_4151404 := by exact prefixLift 4151404
  have htrace : WordTrace (prefixWord ++ tailWord_4151404) baseStart_4151404 baseEnd_4151404 := by
    simpa [prefixWord, tailWord_4151404, baseEnd_4151404] using wordTrace_append hprefix tailTrace_4151404
  have hstable : (prefixWord ++ tailWord_4151404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151404).length < 2 ^ (prefixWord ++ tailWord_4151404).sum := by decide
  have hdescent : baseEnd_4151404 < baseStart_4151404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151417 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_4151417 : Nat := 118140960795 + 4151417 * 2 ^ 59
def prefixEnd_4151417 : Nat := 4983230072969 + 3 ^ 40 * 4151417 * 2
def baseEnd_4151417 : Nat := 1421114878830859530396991

theorem tailTrace_4151417 : CollatzResearch.WordTrace tailWord_4151417 prefixEnd_4151417 1421114878830859530396991 := by
  unfold tailWord_4151417
  simp only [CollatzResearch.WordTrace]
  refine ⟨151414617201132689421892505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100943078134088459614595003 151414617201132689421892505)
  ·
    refine ⟨113560962900849517066419379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151414617201132689421892505 113560962900849517066419379)
    ·
      refine ⟨170341444351274275599629069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113560962900849517066419379 170341444351274275599629069)
      ·
        refine ⟨63878041631727853349860901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170341444351274275599629069 63878041631727853349860901)
        ·
          refine ⟨11977132805948972503098919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63878041631727853349860901 11977132805948972503098919)
          ·
            refine ⟨17965699208923458754648379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11977132805948972503098919 17965699208923458754648379)
            ·
              refine ⟨26948548813385188131972569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17965699208923458754648379 26948548813385188131972569)
              ·
                refine ⟨20211411610038891098979427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26948548813385188131972569 20211411610038891098979427)
                ·
                  refine ⟨30317117415058336648469141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20211411610038891098979427 30317117415058336648469141)
                  ·
                    refine ⟨1421114878830859530396991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30317117415058336648469141 1421114878830859530396991)
                    ·
                      rfl

theorem cell22_4151417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_4151417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151417 prefixEnd_4151417 := by exact prefixLift 4151417
  have htrace : WordTrace (prefixWord ++ tailWord_4151417) baseStart_4151417 baseEnd_4151417 := by
    simpa [prefixWord, tailWord_4151417, baseEnd_4151417] using wordTrace_append hprefix tailTrace_4151417
  have hstable : (prefixWord ++ tailWord_4151417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151417).length < 2 ^ (prefixWord ++ tailWord_4151417).sum := by decide
  have hdescent : baseEnd_4151417 < baseStart_4151417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151438 : List Nat := [4, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_4151438 : Nat := 118140960795 + 4151438 * 2 ^ 59
def prefixEnd_4151438 : Nat := 4983230072969 + 3 ^ 40 * 4151438 * 2
def baseEnd_4151438 : Nat := 473707355853340825207309

theorem tailTrace_4151438 : CollatzResearch.WordTrace tailWord_4151438 prefixEnd_4151438 473707355853340825207309 := by
  unfold tailWord_4151438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18926922891757076251050871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100943588756037740005604645 18926922891757076251050871)
  ·
    refine ⟨28390384337635614376576307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18926922891757076251050871 28390384337635614376576307)
    ·
      refine ⟨42585576506453421564864461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28390384337635614376576307 42585576506453421564864461)
      ·
        refine ⟨15969591189920033086824173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42585576506453421564864461 15969591189920033086824173)
        ·
          refine ⟨5988596696220012407559065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15969591189920033086824173 5988596696220012407559065)
          ·
            refine ⟨4491447522165009305669299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5988596696220012407559065 4491447522165009305669299)
            ·
              refine ⟨6737171283247513958503949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491447522165009305669299 6737171283247513958503949)
              ·
                refine ⟨2526439231217817734438981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6737171283247513958503949 2526439231217817734438981)
                ·
                  refine ⟨473707355853340825207309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526439231217817734438981 473707355853340825207309)
                  ·
                    rfl

theorem cell22_4151438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_4151438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151438 prefixEnd_4151438 := by exact prefixLift 4151438
  have htrace : WordTrace (prefixWord ++ tailWord_4151438) baseStart_4151438 baseEnd_4151438 := by
    simpa [prefixWord, tailWord_4151438, baseEnd_4151438] using wordTrace_append hprefix tailTrace_4151438
  have hstable : (prefixWord ++ tailWord_4151438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151438).length < 2 ^ (prefixWord ++ tailWord_4151438).sum := by decide
  have hdescent : baseEnd_4151438 < baseStart_4151438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151466 : List Nat := [3, 1, 5, 1, 2, 1, 2, 7]
def baseStart_4151466 : Nat := 118140960795 + 4151466 * 2 ^ 59
def prefixEnd_4151466 : Nat := 4983230072969 + 3 ^ 40 * 4151466 * 2
def baseEnd_4151466 : Nat := 157903516948026637324649

theorem tailTrace_4151466 : CollatzResearch.WordTrace tailWord_4151466 prefixEnd_4151466 157903516948026637324649 := by
  unfold tailWord_4151466
  simp only [CollatzResearch.WordTrace]
  refine ⟨37854101094488792697606563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100944269585303447193617501 37854101094488792697606563)
  ·
    refine ⟨56781151641733189046409845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37854101094488792697606563 56781151641733189046409845)
    ·
      refine ⟨5323232966412486473100923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56781151641733189046409845 5323232966412486473100923)
      ·
        refine ⟨7984849449618729709651385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5323232966412486473100923 7984849449618729709651385)
        ·
          refine ⟨5988637087214047282238539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7984849449618729709651385 5988637087214047282238539)
          ·
            refine ⟨8982955630821070923357809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988637087214047282238539 8982955630821070923357809)
            ·
              refine ⟨6737216723115803192518357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8982955630821070923357809 6737216723115803192518357)
              ·
                refine ⟨157903516948026637324649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6737216723115803192518357 157903516948026637324649)
                ·
                  rfl

theorem cell22_4151466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_4151466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151466 prefixEnd_4151466 := by exact prefixLift 4151466
  have htrace : WordTrace (prefixWord ++ tailWord_4151466) baseStart_4151466 baseEnd_4151466 := by
    simpa [prefixWord, tailWord_4151466, baseEnd_4151466] using wordTrace_append hprefix tailTrace_4151466
  have hstable : (prefixWord ++ tailWord_4151466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151466).length < 2 ^ (prefixWord ++ tailWord_4151466).sum := by decide
  have hdescent : baseEnd_4151466 < baseStart_4151466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151470 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4151470 : Nat := 118140960795 + 4151470 * 2 ^ 59
def prefixEnd_4151470 : Nat := 4983230072969 + 3 ^ 40 * 4151470 * 2
def baseEnd_4151470 : Nat := 1421133021813985058821829

theorem tailTrace_4151470 : CollatzResearch.WordTrace tailWord_4151470 prefixEnd_4151470 1421133021813985058821829 := by
  unfold tailWord_4151470
  simp only [CollatzResearch.WordTrace]
  refine ⟨18927068783742584934196483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100944366846627119649047909 18927068783742584934196483)
  ·
    refine ⟨28390603175613877401294725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18927068783742584934196483 28390603175613877401294725)
    ·
      refine ⟨5323238095427602012742761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28390603175613877401294725 5323238095427602012742761)
      ·
        refine ⟨3992428571570701509557071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5323238095427602012742761 3992428571570701509557071)
        ·
          refine ⟨5988642857356052264335607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992428571570701509557071 5988642857356052264335607)
          ·
            refine ⟨8982964286034078396503411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988642857356052264335607 8982964286034078396503411)
            ·
              refine ⟨13474446429051117594755117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8982964286034078396503411 13474446429051117594755117)
              ·
                refine ⟨5052917410894169098033169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13474446429051117594755117 5052917410894169098033169)
                ·
                  refine ⟨3789688058170626823524877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5052917410894169098033169 3789688058170626823524877)
                  ·
                    refine ⟨1421133021813985058821829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789688058170626823524877 1421133021813985058821829)
                    ·
                      rfl

theorem cell22_4151470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4151470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151470 prefixEnd_4151470 := by exact prefixLift 4151470
  have htrace : WordTrace (prefixWord ++ tailWord_4151470) baseStart_4151470 baseEnd_4151470 := by
    simpa [prefixWord, tailWord_4151470, baseEnd_4151470] using wordTrace_append hprefix tailTrace_4151470
  have hstable : (prefixWord ++ tailWord_4151470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151470).length < 2 ^ (prefixWord ++ tailWord_4151470).sum := by decide
  have hdescent : baseEnd_4151470 < baseStart_4151470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151507 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 7, 4]
def baseStart_4151507 : Nat := 118140960795 + 4151507 * 2 ^ 59
def prefixEnd_4151507 : Nat := 4983230072969 + 3 ^ 40 * 4151507 * 2
def baseEnd_4151507 : Nat := 1421145687670129295646715

theorem tailTrace_4151507 : CollatzResearch.WordTrace tailWord_4151507 prefixEnd_4151507 1421145687670129295646715 := by
  unfold tailWord_4151507
  simp only [CollatzResearch.WordTrace]
  refine ⟨151417899770806634792668775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100945266513871089861779183 151417899770806634792668775)
  ·
    refine ⟨227126849656209952189003163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151417899770806634792668775 227126849656209952189003163)
    ·
      refine ⟨340690274484314928283504745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227126849656209952189003163 340690274484314928283504745)
      ·
        refine ⟨255517705863236196212628559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340690274484314928283504745 255517705863236196212628559)
        ·
          refine ⟨383276558794854294318942839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255517705863236196212628559 383276558794854294318942839)
          ·
            refine ⟨574914838192281441478414259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383276558794854294318942839 574914838192281441478414259)
            ·
              refine ⟨862372257288422162217621389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574914838192281441478414259 862372257288422162217621389)
              ·
                refine ⟨323389596483158310831608021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 862372257288422162217621389 323389596483158310831608021)
                ·
                  refine ⟨7579443667574022910115813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 323389596483158310831608021 7579443667574022910115813)
                  ·
                    refine ⟨1421145687670129295646715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7579443667574022910115813 1421145687670129295646715)
                    ·
                      rfl

theorem cell22_4151507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 4].length) (baseStart_4151507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151507 prefixEnd_4151507 := by exact prefixLift 4151507
  have htrace : WordTrace (prefixWord ++ tailWord_4151507) baseStart_4151507 baseEnd_4151507 := by
    simpa [prefixWord, tailWord_4151507, baseEnd_4151507] using wordTrace_append hprefix tailTrace_4151507
  have hstable : (prefixWord ++ tailWord_4151507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151507).length < 2 ^ (prefixWord ++ tailWord_4151507).sum := by decide
  have hdescent : baseEnd_4151507 < baseStart_4151507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151633 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 3, 3]
def baseStart_4151633 : Nat := 118140960795 + 4151633 * 2 ^ 59
def prefixEnd_4151633 : Nat := 4983230072969 + 3 ^ 40 * 4151633 * 2
def baseEnd_4151633 : Nat := 1421188820045106966996329

theorem tailTrace_4151633 : CollatzResearch.WordTrace tailWord_4151633 prefixEnd_4151633 1421188820045106966996329 := by
  unfold tailWord_4151633
  simp only [CollatzResearch.WordTrace]
  refine ⟨151422495368350158311755553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100948330245566772207837035 151422495368350158311755553)
  ·
    refine ⟨113566871526262618733816665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151422495368350158311755553 113566871526262618733816665)
    ·
      refine ⟨85175153644696964050362499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113566871526262618733816665 85175153644696964050362499)
      ·
        refine ⟨127762730467045446075543749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85175153644696964050362499 127762730467045446075543749)
        ·
          refine ⟨23955511962571021139164453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127762730467045446075543749 23955511962571021139164453)
          ·
            refine ⟨4491658492982066463593335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23955511962571021139164453 4491658492982066463593335)
            ·
              refine ⟨6737487739473099695390003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491658492982066463593335 6737487739473099695390003)
              ·
                refine ⟨10106231609209649543085005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6737487739473099695390003 10106231609209649543085005)
                ·
                  refine ⟨3789836853453618578656877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10106231609209649543085005 3789836853453618578656877)
                  ·
                    refine ⟨1421188820045106966996329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789836853453618578656877 1421188820045106966996329)
                    ·
                      rfl

theorem cell22_4151633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_4151633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151633 prefixEnd_4151633 := by exact prefixLift 4151633
  have htrace : WordTrace (prefixWord ++ tailWord_4151633) baseStart_4151633 baseEnd_4151633 := by
    simpa [prefixWord, tailWord_4151633, baseEnd_4151633] using wordTrace_append hprefix tailTrace_4151633
  have hstable : (prefixWord ++ tailWord_4151633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151633).length < 2 ^ (prefixWord ++ tailWord_4151633).sum := by decide
  have hdescent : baseEnd_4151633 < baseStart_4151633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151659 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 3, 4]
def baseStart_4151659 : Nat := 118140960795 + 4151659 * 2 ^ 59
def prefixEnd_4151659 : Nat := 4983230072969 + 3 ^ 40 * 4151659 * 2
def baseEnd_4151659 : Nat := 1421197720376451565846249

theorem tailTrace_4151659 : CollatzResearch.WordTrace tailWord_4151659 prefixEnd_4151659 1421197720376451565846249 := by
  unfold tailWord_4151659
  simp only [CollatzResearch.WordTrace]
  refine ⟨151423443666255964752202031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100948962444170643168134687 151423443666255964752202031)
  ·
    refine ⟨227135165499383947128303047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151423443666255964752202031 227135165499383947128303047)
    ·
      refine ⟨340702748249075920692454571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227135165499383947128303047 340702748249075920692454571)
      ·
        refine ⟨511054122373613881038681857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340702748249075920692454571 511054122373613881038681857)
        ·
          refine ⟨383290591780210410779011393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511054122373613881038681857 383290591780210410779011393)
          ·
            refine ⟨287467943835157808084258545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383290591780210410779011393 287467943835157808084258545)
            ·
              refine ⟨215600957876368356063193909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287467943835157808084258545 215600957876368356063193909)
              ·
                refine ⟨20212589800909533380924429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215600957876368356063193909 20212589800909533380924429)
                ·
                  refine ⟨7579721175341075017846661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20212589800909533380924429 7579721175341075017846661)
                  ·
                    refine ⟨1421197720376451565846249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7579721175341075017846661 1421197720376451565846249)
                    ·
                      rfl

theorem cell22_4151659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 4].length) (baseStart_4151659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151659 prefixEnd_4151659 := by exact prefixLift 4151659
  have htrace : WordTrace (prefixWord ++ tailWord_4151659) baseStart_4151659 baseEnd_4151659 := by
    simpa [prefixWord, tailWord_4151659, baseEnd_4151659] using wordTrace_append hprefix tailTrace_4151659
  have hstable : (prefixWord ++ tailWord_4151659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151659).length < 2 ^ (prefixWord ++ tailWord_4151659).sum := by decide
  have hdescent : baseEnd_4151659 < baseStart_4151659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151706 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_4151706 : Nat := 118140960795 + 4151706 * 2 ^ 59
def prefixEnd_4151706 : Nat := 4983230072969 + 3 ^ 40 * 4151706 * 2
def baseEnd_4151706 : Nat := 1421213809436959109921105

theorem tailTrace_4151706 : CollatzResearch.WordTrace tailWord_4151706 prefixEnd_4151706 1421213809436959109921105 := by
  unfold tailWord_4151706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37856289474271422944790743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100950105264723794519441981 37856289474271422944790743)
  ·
    refine ⟨56784434211407134417186115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37856289474271422944790743 56784434211407134417186115)
    ·
      refine ⟨85176651317110701625779173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56784434211407134417186115 85176651317110701625779173)
      ·
        refine ⟨15970622121958256554833595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85176651317110701625779173 15970622121958256554833595)
        ·
          refine ⟨23955933182937384832250393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15970622121958256554833595 23955933182937384832250393)
          ·
            refine ⟨17966949887203038624187795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23955933182937384832250393 17966949887203038624187795)
            ·
              refine ⟨26950424830804557936281693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17966949887203038624187795 26950424830804557936281693)
              ·
                refine ⟨10106409311551709226105635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26950424830804557936281693 10106409311551709226105635)
                ·
                  refine ⟨15159613967327563839158453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10106409311551709226105635 15159613967327563839158453)
                  ·
                    refine ⟨1421213809436959109921105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15159613967327563839158453 1421213809436959109921105)
                    ·
                      rfl

theorem cell22_4151706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_4151706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151706 prefixEnd_4151706 := by exact prefixLift 4151706
  have htrace : WordTrace (prefixWord ++ tailWord_4151706) baseStart_4151706 baseEnd_4151706 := by
    simpa [prefixWord, tailWord_4151706, baseEnd_4151706] using wordTrace_append hprefix tailTrace_4151706
  have hstable : (prefixWord ++ tailWord_4151706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151706).length < 2 ^ (prefixWord ++ tailWord_4151706).sum := by decide
  have hdescent : baseEnd_4151706 < baseStart_4151706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151740 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 2, 3]
def baseStart_4151740 : Nat := 118140960795 + 4151740 * 2 ^ 59
def prefixEnd_4151740 : Nat := 4983230072969 + 3 ^ 40 * 4151740 * 2
def baseEnd_4151740 : Nat := 1421225448331794354571001

theorem tailTrace_4151740 : CollatzResearch.WordTrace tailWord_4151740 prefixEnd_4151740 1421225448331794354571001 := by
  unfold tailWord_4151740
  simp only [CollatzResearch.WordTrace]
  refine ⟨75713198989481257792950337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100950931985975010390600449 75713198989481257792950337)
  ·
    refine ⟨56784899242110943344712753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75713198989481257792950337 56784899242110943344712753)
    ·
      refine ⟨42588674431583207508534565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56784899242110943344712753 42588674431583207508534565)
      ·
        refine ⟨7985376455921851407850231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42588674431583207508534565 7985376455921851407850231)
        ·
          refine ⟨11978064683882777111775347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7985376455921851407850231 11978064683882777111775347)
          ·
            refine ⟨17967097025824165667663021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11978064683882777111775347 17967097025824165667663021)
            ·
              refine ⟨6737661384684062125373633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17967097025824165667663021 6737661384684062125373633)
              ·
                refine ⟨5053246038513046594030225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6737661384684062125373633 5053246038513046594030225)
                ·
                  refine ⟨3789934528884784945522669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5053246038513046594030225 3789934528884784945522669)
                  ·
                    refine ⟨1421225448331794354571001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789934528884784945522669 1421225448331794354571001)
                    ·
                      rfl

theorem cell22_4151740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_4151740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151740 prefixEnd_4151740 := by exact prefixLift 4151740
  have htrace : WordTrace (prefixWord ++ tailWord_4151740) baseStart_4151740 baseEnd_4151740 := by
    simpa [prefixWord, tailWord_4151740, baseEnd_4151740] using wordTrace_append hprefix tailTrace_4151740
  have hstable : (prefixWord ++ tailWord_4151740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151740).length < 2 ^ (prefixWord ++ tailWord_4151740).sum := by decide
  have hdescent : baseEnd_4151740 < baseStart_4151740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151798 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_4151798 : Nat := 118140960795 + 4151798 * 2 ^ 59
def prefixEnd_4151798 : Nat := 4983230072969 + 3 ^ 40 * 4151798 * 2
def baseEnd_4151798 : Nat := 473748434305700512206941

theorem tailTrace_4151798 : CollatzResearch.WordTrace tailWord_4151798 prefixEnd_4151798 473748434305700512206941 := by
  unfold tailWord_4151798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464282088297024468219503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100952342275168260994341365 9464282088297024468219503)
  ·
    refine ⟨14196423132445536702329255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9464282088297024468219503 14196423132445536702329255)
    ·
      refine ⟨21294634698668305053493883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14196423132445536702329255 21294634698668305053493883)
      ·
        refine ⟨31941952048002457580240825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21294634698668305053493883 31941952048002457580240825)
        ·
          refine ⟨23956464036001843185180619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31941952048002457580240825 23956464036001843185180619)
          ·
            refine ⟨35934696054002764777770929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23956464036001843185180619 35934696054002764777770929)
            ·
              refine ⟨26951022040502073583328197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35934696054002764777770929 26951022040502073583328197)
              ·
                refine ⟨5053316632594138796874037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26951022040502073583328197 5053316632594138796874037)
                ·
                  refine ⟨473748434305700512206941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5053316632594138796874037 473748434305700512206941)
                  ·
                    rfl

theorem cell22_4151798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_4151798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151798 prefixEnd_4151798 := by exact prefixLift 4151798
  have htrace : WordTrace (prefixWord ++ tailWord_4151798) baseStart_4151798 baseEnd_4151798 := by
    simpa [prefixWord, tailWord_4151798, baseEnd_4151798] using wordTrace_append hprefix tailTrace_4151798
  have hstable : (prefixWord ++ tailWord_4151798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151798).length < 2 ^ (prefixWord ++ tailWord_4151798).sum := by decide
  have hdescent : baseEnd_4151798 < baseStart_4151798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151811 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 3, 4]
def baseStart_4151811 : Nat := 118140960795 + 4151811 * 2 ^ 59
def prefixEnd_4151811 : Nat := 4983230072969 + 3 ^ 40 * 4151811 * 2
def baseEnd_4151811 : Nat := 1421249753082773836045783

theorem tailTrace_4151811 : CollatzResearch.WordTrace tailWord_4151811 prefixEnd_4151811 1421249753082773836045783 := by
  unfold tailWord_4151811
  simp only [CollatzResearch.WordTrace]
  refine ⟨151428987561705294711735287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100952658374470196474490191 151428987561705294711735287)
  ·
    refine ⟨227143481342557942067602931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151428987561705294711735287 227143481342557942067602931)
    ·
      refine ⟨340715222013836913101404397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227143481342557942067602931 340715222013836913101404397)
      ·
        refine ⟨127768208255188842413026649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340715222013836913101404397 127768208255188842413026649)
        ·
          refine ⟨95826156191391631809769987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127768208255188842413026649 95826156191391631809769987)
          ·
            refine ⟨143739234287087447714654981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95826156191391631809769987 143739234287087447714654981)
            ·
              refine ⟨26951106428828896446497809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143739234287087447714654981 26951106428828896446497809)
              ·
                refine ⟨20213329821621672334873357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26951106428828896446497809 20213329821621672334873357)
                ·
                  refine ⟨7579998683108127125577509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20213329821621672334873357 7579998683108127125577509)
                  ·
                    refine ⟨1421249753082773836045783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7579998683108127125577509 1421249753082773836045783)
                    ·
                      rfl

theorem cell22_4151811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 4].length) (baseStart_4151811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151811 prefixEnd_4151811 := by exact prefixLift 4151811
  have htrace : WordTrace (prefixWord ++ tailWord_4151811) baseStart_4151811 baseEnd_4151811 := by
    simpa [prefixWord, tailWord_4151811, baseEnd_4151811] using wordTrace_append hprefix tailTrace_4151811
  have hstable : (prefixWord ++ tailWord_4151811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151811).length < 2 ^ (prefixWord ++ tailWord_4151811).sum := by decide
  have hdescent : baseEnd_4151811 < baseStart_4151811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151858 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_4151858 : Nat := 118140960795 + 4151858 * 2 ^ 59
def prefixEnd_4151858 : Nat := 4983230072969 + 3 ^ 40 * 4151858 * 2
def baseEnd_4151858 : Nat := 1421265842143281380120639

theorem tailTrace_4151858 : CollatzResearch.WordTrace tailWord_4151858 prefixEnd_4151858 1421265842143281380120639 := by
  unfold tailWord_4151858
  simp only [CollatzResearch.WordTrace]
  refine ⟨37857675448133755434674057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100953801195023347825797485 37857675448133755434674057)
  ·
    refine ⟨28393256586100316576005543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37857675448133755434674057 28393256586100316576005543)
    ·
      refine ⟨42589884879150474864008315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28393256586100316576005543 42589884879150474864008315)
      ·
        refine ⟨63884827318725712296012473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42589884879150474864008315 63884827318725712296012473)
        ·
          refine ⟨47913620489044284222009355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63884827318725712296012473 47913620489044284222009355)
          ·
            refine ⟨71870430733566426333014033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47913620489044284222009355 71870430733566426333014033)
            ·
              refine ⟨53902823050174819749760525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71870430733566426333014033 53902823050174819749760525)
              ·
                refine ⟨20213558643815557406160197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53902823050174819749760525 20213558643815557406160197)
                ·
                  refine ⟨3790042245715417013655037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20213558643815557406160197 3790042245715417013655037)
                  ·
                    refine ⟨1421265842143281380120639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3790042245715417013655037 1421265842143281380120639)
                    ·
                      rfl

theorem cell22_4151858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_4151858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151858 prefixEnd_4151858 := by exact prefixLift 4151858
  have htrace : WordTrace (prefixWord ++ tailWord_4151858) baseStart_4151858 baseEnd_4151858 := by
    simpa [prefixWord, tailWord_4151858, baseEnd_4151858] using wordTrace_append hprefix tailTrace_4151858
  have hstable : (prefixWord ++ tailWord_4151858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151858).length < 2 ^ (prefixWord ++ tailWord_4151858).sum := by decide
  have hdescent : baseEnd_4151858 < baseStart_4151858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151909 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 2, 3]
def baseStart_4151909 : Nat := 118140960795 + 4151909 * 2 ^ 59
def prefixEnd_4151909 : Nat := 4983230072969 + 3 ^ 40 * 4151909 * 2
def baseEnd_4151909 : Nat := 1421283300485534247095483

theorem tailTrace_4151909 : CollatzResearch.WordTrace tailWord_4151909 prefixEnd_4151909 1421283300485534247095483 := by
  unfold tailWord_4151909
  simp only [CollatzResearch.WordTrace]
  refine ⟨151432561915350257448802781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100955041276900171632535187 151432561915350257448802781)
  ·
    refine ⟨56787210718256346543301043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151432561915350257448802781 56787210718256346543301043)
    ·
      refine ⟨85180816077384519814951565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56787210718256346543301043 85180816077384519814951565)
      ·
        refine ⟨31942806029019194930606837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85180816077384519814951565 31942806029019194930606837)
        ·
          refine ⟨2994638065220549524744391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31942806029019194930606837 2994638065220549524744391)
          ·
            refine ⟨4491957097830824287116587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994638065220549524744391 4491957097830824287116587)
            ·
              refine ⟨6737935646746236430674881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491957097830824287116587 6737935646746236430674881)
              ·
                refine ⟨5053451735059677323006161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6737935646746236430674881 5053451735059677323006161)
                ·
                  refine ⟨3790088801294757992254621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5053451735059677323006161 3790088801294757992254621)
                  ·
                    refine ⟨1421283300485534247095483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3790088801294757992254621 1421283300485534247095483)
                    ·
                      rfl

theorem cell22_4151909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_4151909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151909 prefixEnd_4151909 := by exact prefixLift 4151909
  have htrace : WordTrace (prefixWord ++ tailWord_4151909) baseStart_4151909 baseEnd_4151909 := by
    simpa [prefixWord, tailWord_4151909, baseEnd_4151909] using wordTrace_append hprefix tailTrace_4151909
  have hstable : (prefixWord ++ tailWord_4151909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151909).length < 2 ^ (prefixWord ++ tailWord_4151909).sum := by decide
  have hdescent : baseEnd_4151909 < baseStart_4151909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151931 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 1, 7]
def baseStart_4151931 : Nat := 118140960795 + 4151931 * 2 ^ 59
def prefixEnd_4151931 : Nat := 4983230072969 + 3 ^ 40 * 4151931 * 2
def baseEnd_4151931 : Nat := 1421290831535133523045415

theorem tailTrace_4151931 : CollatzResearch.WordTrace tailWord_4151931 prefixEnd_4151931 1421290831535133523045415 := by
  unfold tailWord_4151931
  simp only [CollatzResearch.WordTrace]
  refine ⟨151433364321270555206103647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100955576214180370137402431 151433364321270555206103647)
  ·
    refine ⟨227150046481905832809155471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151433364321270555206103647 227150046481905832809155471)
    ·
      refine ⟨340725069722858749213733207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227150046481905832809155471 340725069722858749213733207)
      ·
        refine ⟨511087604584288123820599811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340725069722858749213733207 511087604584288123820599811)
        ·
          refine ⟨766631406876432185730899717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511087604584288123820599811 766631406876432185730899717)
          ·
            refine ⟨143743388789331034824543697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 766631406876432185730899717 143743388789331034824543697)
            ·
              refine ⟨107807541591998276118407773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143743388789331034824543697 107807541591998276118407773)
              ·
                refine ⟨40427828096999353544402915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107807541591998276118407773 40427828096999353544402915)
                ·
                  refine ⟨60641742145499030316604373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40427828096999353544402915 60641742145499030316604373)
                  ·
                    refine ⟨1421290831535133523045415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60641742145499030316604373 1421290831535133523045415)
                    ·
                      rfl

theorem cell22_4151931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_4151931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151931 prefixEnd_4151931 := by exact prefixLift 4151931
  have htrace : WordTrace (prefixWord ++ tailWord_4151931) baseStart_4151931 baseEnd_4151931 := by
    simpa [prefixWord, tailWord_4151931, baseEnd_4151931] using wordTrace_append hprefix tailTrace_4151931
  have hstable : (prefixWord ++ tailWord_4151931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151931).length < 2 ^ (prefixWord ++ tailWord_4151931).sum := by decide
  have hdescent : baseEnd_4151931 < baseStart_4151931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151954 : List Nat := [3, 2, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_4151954 : Nat := 118140960795 + 4151954 * 2 ^ 59
def prefixEnd_4151954 : Nat := 4983230072969 + 3 ^ 40 * 4151954 * 2
def baseEnd_4151954 : Nat := 1421298704905169129720345

theorem tailTrace_4151954 : CollatzResearch.WordTrace tailWord_4151954 prefixEnd_4151954 1421298704905169129720345 := by
  unfold tailWord_4151954
  simp only [CollatzResearch.WordTrace]
  refine ⟨37858550800046807533547729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100956135466791486756127277 37858550800046807533547729)
  ·
    refine ⟨28393913100035105650160797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37858550800046807533547729 28393913100035105650160797)
    ·
      refine ⟨10647717412513164618810299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28393913100035105650160797 10647717412513164618810299)
      ·
        refine ⟨15971576118769746928215449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10647717412513164618810299 15971576118769746928215449)
        ·
          refine ⟨11978682089077310196161587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15971576118769746928215449 11978682089077310196161587)
          ·
            refine ⟨17968023133615965294242381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11978682089077310196161587 17968023133615965294242381)
            ·
              refine ⟨6738008675105986985340893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17968023133615965294242381 6738008675105986985340893)
              ·
                refine ⟨2526753253164745119502835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6738008675105986985340893 2526753253164745119502835)
                ·
                  refine ⟨3790129879747117679254253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526753253164745119502835 3790129879747117679254253)
                  ·
                    refine ⟨1421298704905169129720345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3790129879747117679254253 1421298704905169129720345)
                    ·
                      rfl

theorem cell22_4151954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_4151954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151954 prefixEnd_4151954 := by exact prefixLift 4151954
  have htrace : WordTrace (prefixWord ++ tailWord_4151954) baseStart_4151954 baseEnd_4151954 := by
    simpa [prefixWord, tailWord_4151954, baseEnd_4151954] using wordTrace_append hprefix tailTrace_4151954
  have hstable : (prefixWord ++ tailWord_4151954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151954).length < 2 ^ (prefixWord ++ tailWord_4151954).sum := by decide
  have hdescent : baseEnd_4151954 < baseStart_4151954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151993 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_4151993 : Nat := 118140960795 + 4151993 * 2 ^ 59
def prefixEnd_4151993 : Nat := 4983230072969 + 3 ^ 40 * 4151993 * 2
def baseEnd_4151993 : Nat := 1421312055402186027995225

theorem tailTrace_4151993 : CollatzResearch.WordTrace tailWord_4151993 prefixEnd_4151993 1421312055402186027995225 := by
  unfold tailWord_4151993
  simp only [CollatzResearch.WordTrace]
  refine ⟨151435625647045939794860633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100957083764697293196573755 151435625647045939794860633)
  ·
    refine ⟨113576719235284454846145475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151435625647045939794860633 113576719235284454846145475)
    ·
      refine ⟨170365078852926682269218213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113576719235284454846145475 170365078852926682269218213)
      ·
        refine ⟨31943452284923752925478415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170365078852926682269218213 31943452284923752925478415)
        ·
          refine ⟨47915178427385629388217623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31943452284923752925478415 47915178427385629388217623)
          ·
            refine ⟨71872767641078444082326435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47915178427385629388217623 71872767641078444082326435)
            ·
              refine ⟨107809151461617666123489653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71872767641078444082326435 107809151461617666123489653)
              ·
                refine ⟨10107107949526656199077155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107809151461617666123489653 10107107949526656199077155)
                ·
                  refine ⟨15160661924289984298615733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10107107949526656199077155 15160661924289984298615733)
                  ·
                    refine ⟨1421312055402186027995225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15160661924289984298615733 1421312055402186027995225)
                    ·
                      rfl

theorem cell22_4151993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_4151993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151993 prefixEnd_4151993 := by exact prefixLift 4151993
  have htrace : WordTrace (prefixWord ++ tailWord_4151993) baseStart_4151993 baseEnd_4151993 := by
    simpa [prefixWord, tailWord_4151993, baseEnd_4151993] using wordTrace_append hprefix tailTrace_4151993
  have hstable : (prefixWord ++ tailWord_4151993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151993).length < 2 ^ (prefixWord ++ tailWord_4151993).sum := by decide
  have hdescent : baseEnd_4151993 < baseStart_4151993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151997 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_4151997 : Nat := 118140960795 + 4151997 * 2 ^ 59
def prefixEnd_4151997 : Nat := 4983230072969 + 3 ^ 40 * 4151997 * 2
def baseEnd_4151997 : Nat := 1421313424683931350895213

theorem tailTrace_4151997 : CollatzResearch.WordTrace tailWord_4151997 prefixEnd_4151997 1421313424683931350895213 := by
  unfold tailWord_4151997
  simp only [CollatzResearch.WordTrace]
  refine ⟨151435771539031448478006245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100957181026020965652004163 151435771539031448478006245)
  ·
    refine ⟨28394207163568396589626171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151435771539031448478006245 28394207163568396589626171)
    ·
      refine ⟨42591310745352594884439257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28394207163568396589626171 42591310745352594884439257)
      ·
        refine ⟨31943483059014446163329443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42591310745352594884439257 31943483059014446163329443)
        ·
          refine ⟨47915224588521669244994165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31943483059014446163329443 47915224588521669244994165)
          ·
            refine ⟨4492052305173906491718203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47915224588521669244994165 4492052305173906491718203)
            ·
              refine ⟨6738078457760859737577305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492052305173906491718203 6738078457760859737577305)
              ·
                refine ⟨5053558843320644803182979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6738078457760859737577305 5053558843320644803182979)
                ·
                  refine ⟨7580338264980967204774469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053558843320644803182979 7580338264980967204774469)
                  ·
                    refine ⟨1421313424683931350895213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7580338264980967204774469 1421313424683931350895213)
                    ·
                      rfl

theorem cell22_4151997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_4151997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4151997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4151997 prefixEnd_4151997 := by exact prefixLift 4151997
  have htrace : WordTrace (prefixWord ++ tailWord_4151997) baseStart_4151997 baseEnd_4151997 := by
    simpa [prefixWord, tailWord_4151997, baseEnd_4151997] using wordTrace_append hprefix tailTrace_4151997
  have hstable : (prefixWord ++ tailWord_4151997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151997).length < 2 ^ (prefixWord ++ tailWord_4151997).sum := by decide
  have hdescent : baseEnd_4151997 < baseStart_4151997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152010 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_4152010 : Nat := 118140960795 + 4152010 * 2 ^ 59
def prefixEnd_4152010 : Nat := 4983230072969 + 3 ^ 40 * 4152010 * 2
def baseEnd_4152010 : Nat := 1421317874849603650320173

theorem tailTrace_4152010 : CollatzResearch.WordTrace tailWord_4152010 prefixEnd_4152010 1421317874849603650320173 := by
  unfold tailWord_4152010
  simp only [CollatzResearch.WordTrace]
  refine ⟨37859061421996087924557371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100957497125322901132152989 37859061421996087924557371)
  ·
    refine ⟨56788592132994131886836057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37859061421996087924557371 56788592132994131886836057)
    ·
      refine ⟨42591444099745598915127043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56788592132994131886836057 42591444099745598915127043)
      ·
        refine ⟨63887166149618398372690565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42591444099745598915127043 63887166149618398372690565)
        ·
          refine ⟨11978843653053449694879481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63887166149618398372690565 11978843653053449694879481)
          ·
            refine ⟨8984132739790087271159611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11978843653053449694879481 8984132739790087271159611)
            ·
              refine ⟨13476199109685130906739417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984132739790087271159611 13476199109685130906739417)
              ·
                refine ⟨10107149332263848180054563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13476199109685130906739417 10107149332263848180054563)
                ·
                  refine ⟨15160723998395772270081845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10107149332263848180054563 15160723998395772270081845)
                  ·
                    refine ⟨1421317874849603650320173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15160723998395772270081845 1421317874849603650320173)
                    ·
                      rfl

theorem cell22_4152010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_4152010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152010 prefixEnd_4152010 := by exact prefixLift 4152010
  have htrace : WordTrace (prefixWord ++ tailWord_4152010) baseStart_4152010 baseEnd_4152010 := by
    simpa [prefixWord, tailWord_4152010, baseEnd_4152010] using wordTrace_append hprefix tailTrace_4152010
  have hstable : (prefixWord ++ tailWord_4152010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152010).length < 2 ^ (prefixWord ++ tailWord_4152010).sum := by decide
  have hdescent : baseEnd_4152010 < baseStart_4152010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152083 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 4, 5]
def baseStart_4152083 : Nat := 118140960795 + 4152083 * 2 ^ 59
def prefixEnd_4152083 : Nat := 4983230072969 + 3 ^ 40 * 4152083 * 2
def baseEnd_4152083 : Nat := 1421342864241455793244949

theorem tailTrace_4152083 : CollatzResearch.WordTrace tailWord_4152083 prefixEnd_4152083 1421342864241455793244949 := by
  unfold tailWord_4152083
  simp only [CollatzResearch.WordTrace]
  refine ⟨151438908216719885165636903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100959272144479923443757935 151438908216719885165636903)
  ·
    refine ⟨227158362325079827748455355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151438908216719885165636903 227158362325079827748455355)
    ·
      refine ⟨340737543487619741622683033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227158362325079827748455355 340737543487619741622683033)
      ·
        refine ⟨255553157615714806217012275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340737543487619741622683033 255553157615714806217012275)
        ·
          refine ⟨383329736423572209325518413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255553157615714806217012275 383329736423572209325518413)
          ·
            refine ⟨143748651158839578497069405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383329736423572209325518413 143748651158839578497069405)
            ·
              refine ⟨53905744184564841936401027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143748651158839578497069405 53905744184564841936401027)
              ·
                refine ⟨80858616276847262904601541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53905744184564841936401027 80858616276847262904601541)
                ·
                  refine ⟨15160990551908861794612789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80858616276847262904601541 15160990551908861794612789)
                  ·
                    refine ⟨1421342864241455793244949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15160990551908861794612789 1421342864241455793244949)
                    ·
                      rfl

theorem cell22_4152083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_4152083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152083 prefixEnd_4152083 := by exact prefixLift 4152083
  have htrace : WordTrace (prefixWord ++ tailWord_4152083) baseStart_4152083 baseEnd_4152083 := by
    simpa [prefixWord, tailWord_4152083, baseEnd_4152083] using wordTrace_append hprefix tailTrace_4152083
  have hstable : (prefixWord ++ tailWord_4152083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152083).length < 2 ^ (prefixWord ++ tailWord_4152083).sum := by decide
  have hdescent : baseEnd_4152083 < baseStart_4152083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152143 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 2, 10]
def baseStart_4152143 : Nat := 118140960795 + 4152143 * 2 ^ 59
def prefixEnd_4152143 : Nat := 4983230072969 + 3 ^ 40 * 4152143 * 2
def baseEnd_4152143 : Nat := 1421363403467635636744765

theorem tailTrace_4152143 : CollatzResearch.WordTrace tailWord_4152143 prefixEnd_4152143 1421363403467635636744765 := by
  unfold tailWord_4152143
  simp only [CollatzResearch.WordTrace]
  refine ⟨151441096596502515412821083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100960731064335010275214055 151441096596502515412821083)
  ·
    refine ⟨227161644894753773119231625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151441096596502515412821083 227161644894753773119231625)
    ·
      refine ⟨170371233671065329839423719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227161644894753773119231625 170371233671065329839423719)
      ·
        refine ⟨255556850506597994759135579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170371233671065329839423719 255556850506597994759135579)
        ·
          refine ⟨383335275759896992138703369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255556850506597994759135579 383335275759896992138703369)
          ·
            refine ⟨287501456819922744104027527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383335275759896992138703369 287501456819922744104027527)
            ·
              refine ⟨431252185229884116156041291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287501456819922744104027527 431252185229884116156041291)
              ·
                refine ⟨646878277844826174234061937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431252185229884116156041291 646878277844826174234061937)
                ·
                  refine ⟨485158708383619630675546453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646878277844826174234061937 485158708383619630675546453)
                  ·
                    refine ⟨1421363403467635636744765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 485158708383619630675546453 1421363403467635636744765)
                    ·
                      rfl

theorem cell22_4152143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_4152143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152143 prefixEnd_4152143 := by exact prefixLift 4152143
  have htrace : WordTrace (prefixWord ++ tailWord_4152143) baseStart_4152143 baseEnd_4152143 := by
    simpa [prefixWord, tailWord_4152143, baseEnd_4152143] using wordTrace_append hprefix tailTrace_4152143
  have hstable : (prefixWord ++ tailWord_4152143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152143).length < 2 ^ (prefixWord ++ tailWord_4152143).sum := by decide
  have hdescent : baseEnd_4152143 < baseStart_4152143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152160 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_4152160 : Nat := 118140960795 + 4152160 * 2 ^ 59
def prefixEnd_4152160 : Nat := 4983230072969 + 3 ^ 40 * 4152160 * 2
def baseEnd_4152160 : Nat := 1421369222915053259069713

theorem tailTrace_4152160 : CollatzResearch.WordTrace tailWord_4152160 prefixEnd_4152160 1421369222915053259069713 := by
  unfold tailWord_4152160
  simp only [CollatzResearch.WordTrace]
  refine ⟨75720858318720463658094967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100961144424960618210793289 75720858318720463658094967)
  ·
    refine ⟨113581287478080695487142451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75720858318720463658094967 113581287478080695487142451)
    ·
      refine ⟨170371931217121043230713677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113581287478080695487142451 170371931217121043230713677)
      ·
        refine ⟨63889474206420391211517629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170371931217121043230713677 63889474206420391211517629)
        ·
          refine ⟨23958552827407646704319111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63889474206420391211517629 23958552827407646704319111)
          ·
            refine ⟨35937829241111470056478667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23958552827407646704319111 35937829241111470056478667)
            ·
              refine ⟨53906743861667205084718001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35937829241111470056478667 53906743861667205084718001)
              ·
                refine ⟨40430057896250403813538501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53906743861667205084718001 40430057896250403813538501)
                ·
                  refine ⟨7580635855546950715038469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40430057896250403813538501 7580635855546950715038469)
                  ·
                    refine ⟨1421369222915053259069713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7580635855546950715038469 1421369222915053259069713)
                    ·
                      rfl

theorem cell22_4152160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_4152160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152160 prefixEnd_4152160 := by exact prefixLift 4152160
  have htrace : WordTrace (prefixWord ++ tailWord_4152160) baseStart_4152160 baseEnd_4152160 := by
    simpa [prefixWord, tailWord_4152160, baseEnd_4152160] using wordTrace_append hprefix tailTrace_4152160
  have hstable : (prefixWord ++ tailWord_4152160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152160).length < 2 ^ (prefixWord ++ tailWord_4152160).sum := by decide
  have hdescent : baseEnd_4152160 < baseStart_4152160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152177 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 2, 4]
def baseStart_4152177 : Nat := 118140960795 + 4152177 * 2 ^ 59
def prefixEnd_4152177 : Nat := 4983230072969 + 3 ^ 40 * 4152177 * 2
def baseEnd_4152177 : Nat := 1421375042362470881394661

theorem tailTrace_4152177 : CollatzResearch.WordTrace tailWord_4152177 prefixEnd_4152177 1421375042362470881394661 := by
  unfold tailWord_4152177
  simp only [CollatzResearch.WordTrace]
  refine ⟨151442336678379339219558785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100961557785586226146372523 151442336678379339219558785)
  ·
    refine ⟨113581752508784504414669089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151442336678379339219558785 113581752508784504414669089)
    ·
      refine ⟨85186314381588378311001817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113581752508784504414669089 85186314381588378311001817)
      ·
        refine ⟨63889735786191283733251363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85186314381588378311001817 63889735786191283733251363)
        ·
          refine ⟨95834603679286925599877045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63889735786191283733251363 95834603679286925599877045)
          ·
            refine ⟨8984494094933149274988473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95834603679286925599877045 8984494094933149274988473)
            ·
              refine ⟨6738370571199861956241355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8984494094933149274988473 6738370571199861956241355)
              ·
                refine ⟨10107555856799792934362033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6738370571199861956241355 10107555856799792934362033)
                ·
                  refine ⟨7580666892599844700771525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10107555856799792934362033 7580666892599844700771525)
                  ·
                    refine ⟨1421375042362470881394661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7580666892599844700771525 1421375042362470881394661)
                    ·
                      rfl

theorem cell22_4152177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_4152177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152177 prefixEnd_4152177 := by exact prefixLift 4152177
  have htrace : WordTrace (prefixWord ++ tailWord_4152177) baseStart_4152177 baseEnd_4152177 := by
    simpa [prefixWord, tailWord_4152177, baseEnd_4152177] using wordTrace_append hprefix tailTrace_4152177
  have hstable : (prefixWord ++ tailWord_4152177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152177).length < 2 ^ (prefixWord ++ tailWord_4152177).sum := by decide
  have hdescent : baseEnd_4152177 < baseStart_4152177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152282 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_4152282 : Nat := 118140960795 + 4152282 * 2 ^ 59
def prefixEnd_4152282 : Nat := 4983230072969 + 3 ^ 40 * 4152282 * 2
def baseEnd_4152282 : Nat := 473803662002761869173113

theorem tailTrace_4152282 : CollatzResearch.WordTrace tailWord_4152282 prefixEnd_4152282 473803662002761869173113 := by
  unfold tailWord_4152282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37861541585749735538032775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100964110895332628101420733 37861541585749735538032775)
  ·
    refine ⟨56792312378624603307049163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37861541585749735538032775 56792312378624603307049163)
    ·
      refine ⟨85188468567936904960573745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56792312378624603307049163 85188468567936904960573745)
      ·
        refine ⟨63891351425952678720430309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85188468567936904960573745 63891351425952678720430309)
        ·
          refine ⟨11979628392366127260080683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63891351425952678720430309 11979628392366127260080683)
          ·
            refine ⟨17969442588549190890121025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11979628392366127260080683 17969442588549190890121025)
            ·
              refine ⟨13477081941411893167590769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17969442588549190890121025 13477081941411893167590769)
              ·
                refine ⟨10107811456058919875693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13477081941411893167590769 10107811456058919875693077)
                ·
                  refine ⟨473803662002761869173113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10107811456058919875693077 473803662002761869173113)
                  ·
                    rfl

theorem cell22_4152282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_4152282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152282 prefixEnd_4152282 := by exact prefixLift 4152282
  have htrace : WordTrace (prefixWord ++ tailWord_4152282) baseStart_4152282 baseEnd_4152282 := by
    simpa [prefixWord, tailWord_4152282, baseEnd_4152282] using wordTrace_append hprefix tailTrace_4152282
  have hstable : (prefixWord ++ tailWord_4152282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152282).length < 2 ^ (prefixWord ++ tailWord_4152282).sum := by decide
  have hdescent : baseEnd_4152282 < baseStart_4152282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152316 : List Nat := [2, 2, 2, 1, 2, 4, 3, 2, 4]
def baseStart_4152316 : Nat := 118140960795 + 4152316 * 2 ^ 59
def prefixEnd_4152316 : Nat := 4983230072969 + 3 ^ 40 * 4152316 * 2
def baseEnd_4152316 : Nat := 473807541634373617389745

theorem tailTrace_4152316 : CollatzResearch.WordTrace tailWord_4152316 prefixEnd_4152316 473807541634373617389745 := by
  unfold tailWord_4152316
  simp only [CollatzResearch.WordTrace]
  refine ⟨75723703212437882979434401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100964937616583843972579201 75723703212437882979434401)
  ·
    refine ⟨56792777409328412234575801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75723703212437882979434401 56792777409328412234575801)
    ·
      refine ⟨42594583056996309175931851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56792777409328412234575801 42594583056996309175931851)
      ·
        refine ⟨63891874585494463763897777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42594583056996309175931851 63891874585494463763897777)
        ·
          refine ⟨47918905939120847822923333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63891874585494463763897777 47918905939120847822923333)
          ·
            refine ⟨8984794863585158966798125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47918905939120847822923333 8984794863585158966798125)
            ·
              refine ⟨3369298073844434612549297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8984794863585158966798125 3369298073844434612549297)
              ·
                refine ⟨2526973555383325959411973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3369298073844434612549297 2526973555383325959411973)
                ·
                  refine ⟨473807541634373617389745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526973555383325959411973 473807541634373617389745)
                  ·
                    rfl

theorem cell22_4152316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_4152316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152316 prefixEnd_4152316 := by exact prefixLift 4152316
  have htrace : WordTrace (prefixWord ++ tailWord_4152316) baseStart_4152316 baseEnd_4152316 := by
    simpa [prefixWord, tailWord_4152316, baseEnd_4152316] using wordTrace_append hprefix tailTrace_4152316
  have hstable : (prefixWord ++ tailWord_4152316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152316).length < 2 ^ (prefixWord ++ tailWord_4152316).sum := by decide
  have hdescent : baseEnd_4152316 < baseStart_4152316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152327 : List Nat := [1, 1, 4, 3, 1, 1, 4, 7]
def baseStart_4152327 : Nat := 118140960795 + 4152327 * 2 ^ 59
def prefixEnd_4152327 : Nat := 4983230072969 + 3 ^ 40 * 4152327 * 2
def baseEnd_4152327 : Nat := 157936265603102276682689

theorem tailTrace_4152327 : CollatzResearch.WordTrace tailWord_4152327 prefixEnd_4152327 157936265603102276682689 := by
  unfold tailWord_4152327
  simp only [CollatzResearch.WordTrace]
  refine ⟨151447807627835914837519235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100965205085223943225012823 151447807627835914837519235)
  ·
    refine ⟨227171711441753872256278853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151447807627835914837519235 227171711441753872256278853)
    ·
      refine ⟨42594695895328851048052285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227171711441753872256278853 42594695895328851048052285)
      ·
        refine ⟨15973010960748319143019607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42594695895328851048052285 15973010960748319143019607)
        ·
          refine ⟨23959516441122478714529411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15973010960748319143019607 23959516441122478714529411)
          ·
            refine ⟨35939274661683718071794117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23959516441122478714529411 35939274661683718071794117)
            ·
              refine ⟨6738613999065697138461397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35939274661683718071794117 6738613999065697138461397)
              ·
                refine ⟨157936265603102276682689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6738613999065697138461397 157936265603102276682689)
                ·
                  rfl

theorem cell22_4152327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 7].length) (baseStart_4152327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152327 prefixEnd_4152327 := by exact prefixLift 4152327
  have htrace : WordTrace (prefixWord ++ tailWord_4152327) baseStart_4152327 baseEnd_4152327 := by
    simpa [prefixWord, tailWord_4152327, baseEnd_4152327] using wordTrace_append hprefix tailTrace_4152327
  have hstable : (prefixWord ++ tailWord_4152327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152327).length < 2 ^ (prefixWord ++ tailWord_4152327).sum := by decide
  have hdescent : baseEnd_4152327 < baseStart_4152327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152331 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 2, 3]
def baseStart_4152331 : Nat := 118140960795 + 4152331 * 2 ^ 59
def prefixEnd_4152331 : Nat := 4983230072969 + 3 ^ 40 * 4152331 * 2
def baseEnd_4152331 : Nat := 1421427759709665813044189

theorem tailTrace_4152331 : CollatzResearch.WordTrace tailWord_4152331 prefixEnd_4152331 1421427759709665813044189 := by
  unfold tailWord_4152331
  simp only [CollatzResearch.WordTrace]
  refine ⟨151447953519821423520664847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100965302346547615680443231 151447953519821423520664847)
  ·
    refine ⟨227171930279732135280997271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151447953519821423520664847 227171930279732135280997271)
    ·
      refine ⟨340757895419598202921495907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227171930279732135280997271 340757895419598202921495907)
      ·
        refine ⟨511136843129397304382243861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340757895419598202921495907 511136843129397304382243861)
        ·
          refine ⟨23959539521690498642917681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 511136843129397304382243861 23959539521690498642917681)
          ·
            refine ⟨17969654641267873982188261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23959539521690498642917681 17969654641267873982188261)
            ·
              refine ⟨3369310245237726371660299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17969654641267873982188261 3369310245237726371660299)
              ·
                refine ⟨5053965367856589557490449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369310245237726371660299 5053965367856589557490449)
                ·
                  refine ⟨3790474025892442168117837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5053965367856589557490449 3790474025892442168117837)
                  ·
                    refine ⟨1421427759709665813044189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3790474025892442168117837 1421427759709665813044189)
                    ·
                      rfl

theorem cell22_4152331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 2, 3].length) (baseStart_4152331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152331 prefixEnd_4152331 := by exact prefixLift 4152331
  have htrace : WordTrace (prefixWord ++ tailWord_4152331) baseStart_4152331 baseEnd_4152331 := by
    simpa [prefixWord, tailWord_4152331, baseEnd_4152331] using wordTrace_append hprefix tailTrace_4152331
  have hstable : (prefixWord ++ tailWord_4152331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152331).length < 2 ^ (prefixWord ++ tailWord_4152331).sum := by decide
  have hdescent : baseEnd_4152331 < baseStart_4152331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152374 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4152374 : Nat := 118140960795 + 4152374 * 2 ^ 59
def prefixEnd_4152374 : Nat := 4983230072969 + 3 ^ 40 * 4152374 * 2
def baseEnd_4152374 : Nat := 1421442479488428034219057

theorem tailTrace_4152374 : CollatzResearch.WordTrace tailWord_4152374 prefixEnd_4152374 1421442479488428034219057 := by
  unfold tailWord_4152374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9465595116166602616530011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100966347905777094576320117 9465595116166602616530011)
  ·
    refine ⟨14198392674249903924795017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9465595116166602616530011 14198392674249903924795017)
    ·
      refine ⟨10648794505687427943596263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14198392674249903924795017 10648794505687427943596263)
      ·
        refine ⟨15973191758531141915394395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10648794505687427943596263 15973191758531141915394395)
        ·
          refine ⟨23959787637796712873091593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15973191758531141915394395 23959787637796712873091593)
          ·
            refine ⟨17969840728347534654818695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23959787637796712873091593 17969840728347534654818695)
            ·
              refine ⟨26954761092521301982228043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17969840728347534654818695 26954761092521301982228043)
              ·
                refine ⟨40432141638781952973342065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26954761092521301982228043 40432141638781952973342065)
                ·
                  refine ⟨30324106229086464730006549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40432141638781952973342065 30324106229086464730006549)
                  ·
                    refine ⟨1421442479488428034219057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30324106229086464730006549 1421442479488428034219057)
                    ·
                      rfl

theorem cell22_4152374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4152374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152374 prefixEnd_4152374 := by exact prefixLift 4152374
  have htrace : WordTrace (prefixWord ++ tailWord_4152374) baseStart_4152374 baseEnd_4152374 := by
    simpa [prefixWord, tailWord_4152374, baseEnd_4152374] using wordTrace_append hprefix tailTrace_4152374
  have hstable : (prefixWord ++ tailWord_4152374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152374).length < 2 ^ (prefixWord ++ tailWord_4152374).sum := by decide
  have hdescent : baseEnd_4152374 < baseStart_4152374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152387 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 2, 5]
def baseStart_4152387 : Nat := 118140960795 + 4152387 * 2 ^ 59
def prefixEnd_4152387 : Nat := 4983230072969 + 3 ^ 40 * 4152387 * 2
def baseEnd_4152387 : Nat := 1421446929654100333644017

theorem tailTrace_4152387 : CollatzResearch.WordTrace tailWord_4152387 prefixEnd_4152387 1421446929654100333644017 := by
  unfold tailWord_4152387
  simp only [CollatzResearch.WordTrace]
  refine ⟨151449996007618545084703415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100966664005079030056468943 151449996007618545084703415)
  ·
    refine ⟨227174994011427817627055123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151449996007618545084703415 227174994011427817627055123)
    ·
      refine ⟨340762491017141726440582685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227174994011427817627055123 340762491017141726440582685)
      ·
        refine ⟨127785934131428147415218507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340762491017141726440582685 127785934131428147415218507)
        ·
          refine ⟨191678901197142221122827761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127785934131428147415218507 191678901197142221122827761)
          ·
            refine ⟨143759175897856665842120821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191678901197142221122827761 143759175897856665842120821)
            ·
              refine ⟨13477422740424062422698827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143759175897856665842120821 13477422740424062422698827)
              ·
                refine ⟨20216134110636093634048241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13477422740424062422698827 20216134110636093634048241)
                ·
                  refine ⟨15162100582977070225536181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20216134110636093634048241 15162100582977070225536181)
                  ·
                    refine ⟨1421446929654100333644017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15162100582977070225536181 1421446929654100333644017)
                    ·
                      rfl

theorem cell22_4152387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 5].length) (baseStart_4152387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152387 prefixEnd_4152387 := by exact prefixLift 4152387
  have htrace : WordTrace (prefixWord ++ tailWord_4152387) baseStart_4152387 baseEnd_4152387 := by
    simpa [prefixWord, tailWord_4152387, baseEnd_4152387] using wordTrace_append hprefix tailTrace_4152387
  have hstable : (prefixWord ++ tailWord_4152387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152387).length < 2 ^ (prefixWord ++ tailWord_4152387).sum := by decide
  have hdescent : baseEnd_4152387 < baseStart_4152387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152434 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_4152434 : Nat := 118140960795 + 4152434 * 2 ^ 59
def prefixEnd_4152434 : Nat := 4983230072969 + 3 ^ 40 * 4152434 * 2
def baseEnd_4152434 : Nat := 473821006238202625906291

theorem tailTrace_4152434 : CollatzResearch.WordTrace tailWord_4152434 prefixEnd_4152434 473821006238202625906291 := by
  unfold tailWord_4152434
  simp only [CollatzResearch.WordTrace]
  refine ⟨37862927559612068027916089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100967806825632181407776237 37862927559612068027916089)
  ·
    refine ⟨28397195669709051020937067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37862927559612068027916089 28397195669709051020937067)
    ·
      refine ⟨42595793504563576531405601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28397195669709051020937067 42595793504563576531405601)
      ·
        refine ⟨31946845128422682398554201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42595793504563576531405601 31946845128422682398554201)
        ·
          refine ⟨23960133846317011798915651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31946845128422682398554201 23960133846317011798915651)
          ·
            refine ⟨35940200769475517698373477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23960133846317011798915651 35940200769475517698373477)
            ·
              refine ⟨6738787644276659568445027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35940200769475517698373477 6738787644276659568445027)
              ·
                refine ⟨10108181466414989352667541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6738787644276659568445027 10108181466414989352667541)
                ·
                  refine ⟨473821006238202625906291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10108181466414989352667541 473821006238202625906291)
                  ·
                    rfl

theorem cell22_4152434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_4152434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152434 prefixEnd_4152434 := by exact prefixLift 4152434
  have htrace : WordTrace (prefixWord ++ tailWord_4152434) baseStart_4152434 baseEnd_4152434 := by
    simpa [prefixWord, tailWord_4152434, baseEnd_4152434] using wordTrace_append hprefix tailTrace_4152434
  have hstable : (prefixWord ++ tailWord_4152434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152434).length < 2 ^ (prefixWord ++ tailWord_4152434).sum := by decide
  have hdescent : baseEnd_4152434 < baseStart_4152434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152466 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_4152466 : Nat := 118140960795 + 4152466 * 2 ^ 59
def prefixEnd_4152466 : Nat := 4983230072969 + 3 ^ 40 * 4152466 * 2
def baseEnd_4152466 : Nat := 1421473972968570460918775

theorem tailTrace_4152466 : CollatzResearch.WordTrace tailWord_4152466 prefixEnd_4152466 1421473972968570460918775 := by
  unfold tailWord_4152466
  simp only [CollatzResearch.WordTrace]
  refine ⟨37863219343583085394207313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100968584916221561051219501 37863219343583085394207313)
  ·
    refine ⟨28397414507687314045655485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37863219343583085394207313 28397414507687314045655485)
    ·
      refine ⟨10649030440382742767120807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28397414507687314045655485 10649030440382742767120807)
      ·
        refine ⟨15973545660574114150681211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10649030440382742767120807 15973545660574114150681211)
        ·
          refine ⟨23960318490861171226021817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15973545660574114150681211 23960318490861171226021817)
          ·
            refine ⟨17970238868145878419516363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23960318490861171226021817 17970238868145878419516363)
            ·
              refine ⟨26955358302218817629274545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17970238868145878419516363 26955358302218817629274545)
              ·
                refine ⟨20216518726664113221955909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26955358302218817629274545 20216518726664113221955909)
                ·
                  refine ⟨3790597261249521229116733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20216518726664113221955909 3790597261249521229116733)
                  ·
                    refine ⟨1421473972968570460918775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3790597261249521229116733 1421473972968570460918775)
                    ·
                      rfl

theorem cell22_4152466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_4152466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152466 prefixEnd_4152466 := by exact prefixLift 4152466
  have htrace : WordTrace (prefixWord ++ tailWord_4152466) baseStart_4152466 baseEnd_4152466 := by
    simpa [prefixWord, tailWord_4152466, baseEnd_4152466] using wordTrace_append hprefix tailTrace_4152466
  have hstable : (prefixWord ++ tailWord_4152466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152466).length < 2 ^ (prefixWord ++ tailWord_4152466).sum := by decide
  have hdescent : baseEnd_4152466 < baseStart_4152466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152507 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 9]
def baseStart_4152507 : Nat := 118140960795 + 4152507 * 2 ^ 59
def prefixEnd_4152507 : Nat := 4983230072969 + 3 ^ 40 * 4152507 * 2
def baseEnd_4152507 : Nat := 473829336035486673547883

theorem tailTrace_4152507 : CollatzResearch.WordTrace tailWord_4152507 prefixEnd_4152507 473829336035486673547883 := by
  unfold tailWord_4152507
  simp only [CollatzResearch.WordTrace]
  refine ⟨151454372767183805579071775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100969581844789203719381183 151454372767183805579071775)
  ·
    refine ⟨227181559150775708368607663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151454372767183805579071775 227181559150775708368607663)
    ·
      refine ⟨340772338726163562552911495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227181559150775708368607663 340772338726163562552911495)
      ·
        refine ⟨511158508089245343829367243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340772338726163562552911495 511158508089245343829367243)
        ·
          refine ⟨766737762133868015744050865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511158508089245343829367243 766737762133868015744050865)
          ·
            refine ⟨575053321600401011808038149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766737762133868015744050865 575053321600401011808038149)
            ·
              refine ⟨107822497800075189714007153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 575053321600401011808038149 107822497800075189714007153)
              ·
                refine ⟨80866873350056392285505365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107822497800075189714007153 80866873350056392285505365)
                ·
                  refine ⟨473829336035486673547883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80866873350056392285505365 473829336035486673547883)
                  ·
                    rfl

theorem cell22_4152507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 9].length) (baseStart_4152507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152507 prefixEnd_4152507 := by exact prefixLift 4152507
  have htrace : WordTrace (prefixWord ++ tailWord_4152507) baseStart_4152507 baseEnd_4152507 := by
    simpa [prefixWord, tailWord_4152507, baseEnd_4152507] using wordTrace_append hprefix tailTrace_4152507
  have hstable : (prefixWord ++ tailWord_4152507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152507).length < 2 ^ (prefixWord ++ tailWord_4152507).sum := by decide
  have hdescent : baseEnd_4152507 < baseStart_4152507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152545 : List Nat := [1, 2, 3, 1, 3, 2, 4, 2, 1, 3]
def baseStart_4152545 : Nat := 118140960795 + 4152545 * 2 ^ 59
def prefixEnd_4152545 : Nat := 4983230072969 + 3 ^ 40 * 4152545 * 2
def baseEnd_4152545 : Nat := 1421501016283040588193533

theorem tailTrace_4152545 : CollatzResearch.WordTrace tailWord_4152545 prefixEnd_4152545 1421501016283040588193533 := by
  unfold tailWord_4152545
  simp only [CollatzResearch.WordTrace]
  refine ⟨151455758741046138068955089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100970505827364092045970059 151455758741046138068955089)
  ·
    refine ⟨113591819055784603551716317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151455758741046138068955089 113591819055784603551716317)
    ·
      refine ⟨42596932145919226331893619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113591819055784603551716317 42596932145919226331893619)
      ·
        refine ⟨63895398218878839497840429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42596932145919226331893619 63895398218878839497840429)
        ·
          refine ⟨23960774332079564811690161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63895398218878839497840429 23960774332079564811690161)
          ·
            refine ⟨17970580749059673608767621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23960774332079564811690161 17970580749059673608767621)
            ·
              refine ⟨3369483890448688801643929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17970580749059673608767621 3369483890448688801643929)
              ·
                refine ⟨2527112917836516601232947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3369483890448688801643929 2527112917836516601232947)
                ·
                  refine ⟨3790669376754774901849421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527112917836516601232947 3790669376754774901849421)
                  ·
                    refine ⟨1421501016283040588193533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3790669376754774901849421 1421501016283040588193533)
                    ·
                      rfl

theorem cell22_4152545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_4152545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152545 prefixEnd_4152545 := by exact prefixLift 4152545
  have htrace : WordTrace (prefixWord ++ tailWord_4152545) baseStart_4152545 baseEnd_4152545 := by
    simpa [prefixWord, tailWord_4152545, baseEnd_4152545] using wordTrace_append hprefix tailTrace_4152545
  have hstable : (prefixWord ++ tailWord_4152545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152545).length < 2 ^ (prefixWord ++ tailWord_4152545).sum := by decide
  have hdescent : baseEnd_4152545 < baseStart_4152545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152569 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 6]
def baseStart_4152569 : Nat := 118140960795 + 4152569 * 2 ^ 59
def prefixEnd_4152569 : Nat := 4983230072969 + 3 ^ 40 * 4152569 * 2
def baseEnd_4152569 : Nat := 473836410657837508531153

theorem tailTrace_4152569 : CollatzResearch.WordTrace tailWord_4152569 prefixEnd_4152569 473836410657837508531153 := by
  unfold tailWord_4152569
  simp only [CollatzResearch.WordTrace]
  refine ⟨151456634092959190167828761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100971089395306126778552507 151456634092959190167828761)
  ·
    refine ⟨113592475569719392625871571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151456634092959190167828761 113592475569719392625871571)
    ·
      refine ⟨170388713354579088938807357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113592475569719392625871571 170388713354579088938807357)
      ·
        refine ⟨63895767507967158352052759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170388713354579088938807357 63895767507967158352052759)
        ·
          refine ⟨95843651261950737528079139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63895767507967158352052759 95843651261950737528079139)
          ·
            refine ⟨143765476892926106292118709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95843651261950737528079139 143765476892926106292118709)
            ·
              refine ⟨13478013458711822464886129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143765476892926106292118709 13478013458711822464886129)
              ·
                refine ⟨10108510094033866848664597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13478013458711822464886129 10108510094033866848664597)
                ·
                  refine ⟨473836410657837508531153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10108510094033866848664597 473836410657837508531153)
                  ·
                    rfl

theorem cell22_4152569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_4152569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152569 prefixEnd_4152569 := by exact prefixLift 4152569
  have htrace : WordTrace (prefixWord ++ tailWord_4152569) baseStart_4152569 baseEnd_4152569 := by
    simpa [prefixWord, tailWord_4152569, baseEnd_4152569] using wordTrace_append hprefix tailTrace_4152569
  have hstable : (prefixWord ++ tailWord_4152569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152569).length < 2 ^ (prefixWord ++ tailWord_4152569).sum := by decide
  have hdescent : baseEnd_4152569 < baseStart_4152569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152588 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 1, 4]
def baseStart_4152588 : Nat := 118140960795 + 4152588 * 2 ^ 59
def prefixEnd_4152588 : Nat := 4983230072969 + 3 ^ 40 * 4152588 * 2
def baseEnd_4152588 : Nat := 1421515736061802809368401

theorem tailTrace_4152588 : CollatzResearch.WordTrace tailWord_4152588 prefixEnd_4152588 1421515736061802809368401 := by
  unfold tailWord_4152588
  simp only [CollatzResearch.WordTrace]
  refine ⟨75728663539945178206385209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100971551386593570941846945 75728663539945178206385209)
  ·
    refine ⟨56796497654958883654788907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75728663539945178206385209 56796497654958883654788907)
    ·
      refine ⟨85194746482438325482183361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56796497654958883654788907 85194746482438325482183361)
      ·
        refine ⟨63896059861828744111637521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85194746482438325482183361 63896059861828744111637521)
        ·
          refine ⟨47922044896371558083728141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63896059861828744111637521 47922044896371558083728141)
          ·
            refine ⟨17970766836139334281398053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47922044896371558083728141 17970766836139334281398053)
            ·
              refine ⟨3369518781776125177762135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17970766836139334281398053 3369518781776125177762135)
              ·
                refine ⟨5054278172664187766643203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369518781776125177762135 5054278172664187766643203)
                ·
                  refine ⟨7581417258996281649964805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054278172664187766643203 7581417258996281649964805)
                  ·
                    refine ⟨1421515736061802809368401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7581417258996281649964805 1421515736061802809368401)
                    ·
                      rfl

theorem cell22_4152588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_4152588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152588 prefixEnd_4152588 := by exact prefixLift 4152588
  have htrace : WordTrace (prefixWord ++ tailWord_4152588) baseStart_4152588 baseEnd_4152588 := by
    simpa [prefixWord, tailWord_4152588, baseEnd_4152588] using wordTrace_append hprefix tailTrace_4152588
  have hstable : (prefixWord ++ tailWord_4152588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152588).length < 2 ^ (prefixWord ++ tailWord_4152588).sum := by decide
  have hdescent : baseEnd_4152588 < baseStart_4152588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152616 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_4152616 : Nat := 118140960795 + 4152616 * 2 ^ 59
def prefixEnd_4152616 : Nat := 4983230072969 + 3 ^ 40 * 4152616 * 2
def baseEnd_4152616 : Nat := 1421525321034020069668315

theorem tailTrace_4152616 : CollatzResearch.WordTrace tailWord_4152616 prefixEnd_4152616 1421525321034020069668315 := by
  unfold tailWord_4152616
  simp only [CollatzResearch.WordTrace]
  refine ⟨75729174161894458597394851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100972232215859278129859801 75729174161894458597394851)
  ·
    refine ⟨113593761242841687896092277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75729174161894458597394851 113593761242841687896092277)
    ·
      refine ⟨10649415116516408240258651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113593761242841687896092277 10649415116516408240258651)
      ·
        refine ⟨15974122674774612360387977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10649415116516408240258651 15974122674774612360387977)
        ·
          refine ⟨11980592006080959270290983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15974122674774612360387977 11980592006080959270290983)
          ·
            refine ⟨17970888009121438905436475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11980592006080959270290983 17970888009121438905436475)
            ·
              refine ⟨26956332013682158358154713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17970888009121438905436475 26956332013682158358154713)
              ·
                refine ⟨20217249010261618768616035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26956332013682158358154713 20217249010261618768616035)
                ·
                  refine ⟨30325873515392428152924053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20217249010261618768616035 30325873515392428152924053)
                  ·
                    refine ⟨1421525321034020069668315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30325873515392428152924053 1421525321034020069668315)
                    ·
                      rfl

theorem cell22_4152616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_4152616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152616 prefixEnd_4152616 := by exact prefixLift 4152616
  have htrace : WordTrace (prefixWord ++ tailWord_4152616) baseStart_4152616 baseEnd_4152616 := by
    simpa [prefixWord, tailWord_4152616, baseEnd_4152616] using wordTrace_append hprefix tailTrace_4152616
  have hstable : (prefixWord ++ tailWord_4152616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152616).length < 2 ^ (prefixWord ++ tailWord_4152616).sum := by decide
  have hdescent : baseEnd_4152616 < baseStart_4152616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152618 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_4152618 : Nat := 118140960795 + 4152618 * 2 ^ 59
def prefixEnd_4152618 : Nat := 4983230072969 + 3 ^ 40 * 4152618 * 2
def baseEnd_4152618 : Nat := 1421526005674892731118309

theorem tailTrace_4152618 : CollatzResearch.WordTrace tailWord_4152618 prefixEnd_4152618 1421526005674892731118309 := by
  unfold tailWord_4152618
  simp only [CollatzResearch.WordTrace]
  refine ⟨37864605317445417884090627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100972280846521114357575005 37864605317445417884090627)
  ·
    refine ⟨56796907976168126826135941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37864605317445417884090627 56796907976168126826135941)
    ·
      refine ⟨10649420245531523779900489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56796907976168126826135941 10649420245531523779900489)
      ·
        refine ⟨7987065184148642834925367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10649420245531523779900489 7987065184148642834925367)
        ·
          refine ⟨11980597776222964252388051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7987065184148642834925367 11980597776222964252388051)
          ·
            refine ⟨17970896664334446378582077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11980597776222964252388051 17970896664334446378582077)
            ·
              refine ⟨6739086249125417391968279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17970896664334446378582077 6739086249125417391968279)
              ·
                refine ⟨10108629373688126087952419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6739086249125417391968279 10108629373688126087952419)
                ·
                  refine ⟨15162944060532189131928629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10108629373688126087952419 15162944060532189131928629)
                  ·
                    refine ⟨1421526005674892731118309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15162944060532189131928629 1421526005674892731118309)
                    ·
                      rfl

theorem cell22_4152618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_4152618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152618 prefixEnd_4152618 := by exact prefixLift 4152618
  have htrace : WordTrace (prefixWord ++ tailWord_4152618) baseStart_4152618 baseEnd_4152618 := by
    simpa [prefixWord, tailWord_4152618, baseEnd_4152618] using wordTrace_append hprefix tailTrace_4152618
  have hstable : (prefixWord ++ tailWord_4152618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152618).length < 2 ^ (prefixWord ++ tailWord_4152618).sum := by decide
  have hdescent : baseEnd_4152618 < baseStart_4152618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152637 : List Nat := [1, 4, 1, 5, 1, 2, 1, 3, 4]
def baseStart_4152637 : Nat := 118140960795 + 4152637 * 2 ^ 59
def prefixEnd_4152637 : Nat := 4983230072969 + 3 ^ 40 * 4152637 * 2
def baseEnd_4152637 : Nat := 473844169921061004964417

theorem tailTrace_4152637 : CollatzResearch.WordTrace tailWord_4152637 prefixEnd_4152637 473844169921061004964417 := by
  unfold tailWord_4152637
  simp only [CollatzResearch.WordTrace]
  refine ⟨151459114256712837781304165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100972742837808558520869443 151459114256712837781304165)
  ·
    refine ⟨28398583923133657083994531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151459114256712837781304165 28398583923133657083994531)
    ·
      refine ⟨42597875884700485625991797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28398583923133657083994531 42597875884700485625991797)
      ·
        refine ⟨3993550864190670527436731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42597875884700485625991797 3993550864190670527436731)
        ·
          refine ⟨5990326296286005791155097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993550864190670527436731 5990326296286005791155097)
          ·
            refine ⟨4492744722214504343366323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5990326296286005791155097 4492744722214504343366323)
            ·
              refine ⟨6739117083321756515049485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492744722214504343366323 6739117083321756515049485)
              ·
                refine ⟨2527168906245658693143557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6739117083321756515049485 2527168906245658693143557)
                ·
                  refine ⟨473844169921061004964417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527168906245658693143557 473844169921061004964417)
                  ·
                    rfl

theorem cell22_4152637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_4152637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152637 prefixEnd_4152637 := by exact prefixLift 4152637
  have htrace : WordTrace (prefixWord ++ tailWord_4152637) baseStart_4152637 baseEnd_4152637 := by
    simpa [prefixWord, tailWord_4152637, baseEnd_4152637] using wordTrace_append hprefix tailTrace_4152637
  have hstable : (prefixWord ++ tailWord_4152637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152637).length < 2 ^ (prefixWord ++ tailWord_4152637).sum := by decide
  have hdescent : baseEnd_4152637 < baseStart_4152637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152659 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 7]
def baseStart_4152659 : Nat := 118140960795 + 4152659 * 2 ^ 59
def prefixEnd_4152659 : Nat := 4983230072969 + 3 ^ 40 * 4152659 * 2
def baseEnd_4152659 : Nat := 473846680270927430281061

theorem tailTrace_4152659 : CollatzResearch.WordTrace tailWord_4152659 prefixEnd_4152659 473846680270927430281061 := by
  unfold tailWord_4152659
  simp only [CollatzResearch.WordTrace]
  refine ⟨151459916662633135538605031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100973277775088757025736687 151459916662633135538605031)
  ·
    refine ⟨227189874993949703307907547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151459916662633135538605031 227189874993949703307907547)
    ·
      refine ⟨340784812490924554961861321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227189874993949703307907547 340784812490924554961861321)
      ·
        refine ⟨255588609368193416221395991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340784812490924554961861321 255588609368193416221395991)
        ·
          refine ⟨383382914052290124332093987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255588609368193416221395991 383382914052290124332093987)
          ·
            refine ⟨575074371078435186498140981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383382914052290124332093987 575074371078435186498140981)
            ·
              refine ⟨53913222288603298734200717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 575074371078435186498140981 53913222288603298734200717)
              ·
                refine ⟨20217458358226237025325269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53913222288603298734200717 20217458358226237025325269)
                ·
                  refine ⟨473846680270927430281061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20217458358226237025325269 473846680270927430281061)
                  ·
                    rfl

theorem cell22_4152659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 7].length) (baseStart_4152659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152659 prefixEnd_4152659 := by exact prefixLift 4152659
  have htrace : WordTrace (prefixWord ++ tailWord_4152659) baseStart_4152659 baseEnd_4152659 := by
    simpa [prefixWord, tailWord_4152659, baseEnd_4152659] using wordTrace_append hprefix tailTrace_4152659
  have hstable : (prefixWord ++ tailWord_4152659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152659).length < 2 ^ (prefixWord ++ tailWord_4152659).sum := by decide
  have hdescent : baseEnd_4152659 < baseStart_4152659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152663 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 3, 3]
def baseStart_4152663 : Nat := 118140960795 + 4152663 * 2 ^ 59
def prefixEnd_4152663 : Nat := 4983230072969 + 3 ^ 40 * 4152663 * 2
def baseEnd_4152663 : Nat := 1421541410094527613743171

theorem tailTrace_4152663 : CollatzResearch.WordTrace tailWord_4152663 prefixEnd_4152663 1421541410094527613743171 := by
  unfold tailWord_4152663
  simp only [CollatzResearch.WordTrace]
  refine ⟨151460062554618644221750643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100973375036412429481167095 151460062554618644221750643)
  ·
    refine ⟨227190093831927966332625965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151460062554618644221750643 227190093831927966332625965)
    ·
      refine ⟨85196285186972987374734737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227190093831927966332625965 85196285186972987374734737)
      ·
        refine ⟨63897213890229740531051053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85196285186972987374734737 63897213890229740531051053)
        ·
          refine ⟨23961455208836152699144145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63897213890229740531051053 23961455208836152699144145)
          ·
            refine ⟨17971091406627114524358109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23961455208836152699144145 17971091406627114524358109)
            ·
              refine ⟨6739159277485167946634291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17971091406627114524358109 6739159277485167946634291)
              ·
                refine ⟨10108738916227751919951437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6739159277485167946634291 10108738916227751919951437)
                ·
                  refine ⟨3790777093585406969981789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10108738916227751919951437 3790777093585406969981789)
                  ·
                    refine ⟨1421541410094527613743171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3790777093585406969981789 1421541410094527613743171)
                    ·
                      rfl

theorem cell22_4152663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_4152663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152663 prefixEnd_4152663 := by exact prefixLift 4152663
  have htrace : WordTrace (prefixWord ++ tailWord_4152663) baseStart_4152663 baseEnd_4152663 := by
    simpa [prefixWord, tailWord_4152663, baseEnd_4152663] using wordTrace_append hprefix tailTrace_4152663
  have hstable : (prefixWord ++ tailWord_4152663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152663).length < 2 ^ (prefixWord ++ tailWord_4152663).sum := by decide
  have hdescent : baseEnd_4152663 < baseStart_4152663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152669 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4152669 : Nat := 118140960795 + 4152669 * 2 ^ 59
def prefixEnd_4152669 : Nat := 4983230072969 + 3 ^ 40 * 4152669 * 2
def baseEnd_4152669 : Nat := 1421543464017145598093153

theorem tailTrace_4152669 : CollatzResearch.WordTrace tailWord_4152669 prefixEnd_4152669 1421543464017145598093153 := by
  unfold tailWord_4152669
  simp only [CollatzResearch.WordTrace]
  refine ⟨151460281392596907246469061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100973520928397938164312707 151460281392596907246469061)
  ·
    refine ⟨28398802761111920108712949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151460281392596907246469061 28398802761111920108712949)
    ·
      refine ⟨2662387758854242510191839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28398802761111920108712949 2662387758854242510191839)
      ·
        refine ⟨3993581638281363765287759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662387758854242510191839 3993581638281363765287759)
        ·
          refine ⟨5990372457422045647931639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993581638281363765287759 5990372457422045647931639)
          ·
            refine ⟨8985558686133068471897459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5990372457422045647931639 8985558686133068471897459)
            ·
              refine ⟨13478338029199602707846189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8985558686133068471897459 13478338029199602707846189)
              ·
                refine ⟨5054376760949851015442321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13478338029199602707846189 5054376760949851015442321)
                ·
                  refine ⟨3790782570712388261581741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5054376760949851015442321 3790782570712388261581741)
                  ·
                    refine ⟨1421543464017145598093153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3790782570712388261581741 1421543464017145598093153)
                    ·
                      rfl

theorem cell22_4152669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4152669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152669 prefixEnd_4152669 := by exact prefixLift 4152669
  have htrace : WordTrace (prefixWord ++ tailWord_4152669) baseStart_4152669 baseEnd_4152669 := by
    simpa [prefixWord, tailWord_4152669, baseEnd_4152669] using wordTrace_append hprefix tailTrace_4152669
  have hstable : (prefixWord ++ tailWord_4152669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152669).length < 2 ^ (prefixWord ++ tailWord_4152669).sum := by decide
  have hdescent : baseEnd_4152669 < baseStart_4152669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152738 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_4152738 : Nat := 118140960795 + 4152738 * 2 ^ 59
def prefixEnd_4152738 : Nat := 4983230072969 + 3 ^ 40 * 4152738 * 2
def baseEnd_4152738 : Nat := 473855694709084139372647

theorem tailTrace_4152738 : CollatzResearch.WordTrace tailWord_4152738 prefixEnd_4152738 473855694709084139372647 := by
  unfold tailWord_4152738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37865699507336733007682717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100975198686231288020487245 37865699507336733007682717)
  ·
    refine ⟨14199637315251274877881019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37865699507336733007682717 14199637315251274877881019)
    ·
      refine ⟨21299455972876912316821529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14199637315251274877881019 21299455972876912316821529)
      ·
        refine ⟨15974591979657684237616147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21299455972876912316821529 15974591979657684237616147)
        ·
          refine ⟨23961887969486526356424221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15974591979657684237616147 23961887969486526356424221)
          ·
            refine ⟨8985707988557447383659083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23961887969486526356424221 8985707988557447383659083)
            ·
              refine ⟨13478561982836171075488625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8985707988557447383659083 13478561982836171075488625)
              ·
                refine ⟨10108921487127128306616469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13478561982836171075488625 10108921487127128306616469)
                ·
                  refine ⟨473855694709084139372647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10108921487127128306616469 473855694709084139372647)
                  ·
                    rfl

theorem cell22_4152738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_4152738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152738 prefixEnd_4152738 := by exact prefixLift 4152738
  have htrace : WordTrace (prefixWord ++ tailWord_4152738) baseStart_4152738 baseEnd_4152738 := by
    simpa [prefixWord, tailWord_4152738, baseEnd_4152738] using wordTrace_append hprefix tailTrace_4152738
  have hstable : (prefixWord ++ tailWord_4152738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152738).length < 2 ^ (prefixWord ++ tailWord_4152738).sum := by decide
  have hdescent : baseEnd_4152738 < baseStart_4152738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152753 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 4, 3]
def baseStart_4152753 : Nat := 118140960795 + 4152753 * 2 ^ 59
def prefixEnd_4152753 : Nat := 4983230072969 + 3 ^ 40 * 4152753 * 2
def baseEnd_4152753 : Nat := 1421572218933797378992895

theorem tailTrace_4152753 : CollatzResearch.WordTrace tailWord_4152753 prefixEnd_4152753 1421572218933797378992895 := by
  unfold tailWord_4152753
  simp only [CollatzResearch.WordTrace]
  refine ⟨151463345124292589592526913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100975563416195059728351275 151463345124292589592526913)
  ·
    refine ⟨113597508843219442194395185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151463345124292589592526913 113597508843219442194395185)
    ·
      refine ⟨85198131632414581645796389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113597508843219442194395185 85198131632414581645796389)
      ·
        refine ⟨15974649681077734058586823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85198131632414581645796389 15974649681077734058586823)
        ·
          refine ⟨23961974521616601087880235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15974649681077734058586823 23961974521616601087880235)
          ·
            refine ⟨35942961782424901631820353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23961974521616601087880235 35942961782424901631820353)
            ·
              refine ⟨26957221336818676223865265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35942961782424901631820353 26957221336818676223865265)
              ·
                refine ⟨20217916002614007167898949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26957221336818676223865265 20217916002614007167898949)
                ·
                  refine ⟨3790859250490126343981053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20217916002614007167898949 3790859250490126343981053)
                  ·
                    refine ⟨1421572218933797378992895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3790859250490126343981053 1421572218933797378992895)
                    ·
                      rfl

theorem cell22_4152753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_4152753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152753 prefixEnd_4152753 := by exact prefixLift 4152753
  have htrace : WordTrace (prefixWord ++ tailWord_4152753) baseStart_4152753 baseEnd_4152753 := by
    simpa [prefixWord, tailWord_4152753, baseEnd_4152753] using wordTrace_append hprefix tailTrace_4152753
  have hstable : (prefixWord ++ tailWord_4152753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152753).length < 2 ^ (prefixWord ++ tailWord_4152753).sum := by decide
  have hdescent : baseEnd_4152753 < baseStart_4152753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152757 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 1, 4]
def baseStart_4152757 : Nat := 118140960795 + 4152757 * 2 ^ 59
def prefixEnd_4152757 : Nat := 4983230072969 + 3 ^ 40 * 4152757 * 2
def baseEnd_4152757 : Nat := 1421573588215542701892883

theorem tailTrace_4152757 : CollatzResearch.WordTrace tailWord_4152757 prefixEnd_4152757 1421573588215542701892883 := by
  unfold tailWord_4152757
  simp only [CollatzResearch.WordTrace]
  refine ⟨151463491016278098275672525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100975660677518732183781683 151463491016278098275672525)
  ·
    refine ⟨56798809131104286853377197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151463491016278098275672525 56798809131104286853377197)
    ·
      refine ⟨21299553424164107570016449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56798809131104286853377197 21299553424164107570016449)
      ·
        refine ⟨15974665068123080677512337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21299553424164107570016449 15974665068123080677512337)
        ·
          refine ⟨11980998801092310508134253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15974665068123080677512337 11980998801092310508134253)
          ·
            refine ⟨4492874550409616440550345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11980998801092310508134253 4492874550409616440550345)
            ·
              refine ⟨3369655912807212330412759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4492874550409616440550345 3369655912807212330412759)
              ·
                refine ⟨5054483869210818495619139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369655912807212330412759 5054483869210818495619139)
                ·
                  refine ⟨7581725803816227743428709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054483869210818495619139 7581725803816227743428709)
                  ·
                    refine ⟨1421573588215542701892883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7581725803816227743428709 1421573588215542701892883)
                    ·
                      rfl

theorem cell22_4152757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_4152757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152757 prefixEnd_4152757 := by exact prefixLift 4152757
  have htrace : WordTrace (prefixWord ++ tailWord_4152757) baseStart_4152757 baseEnd_4152757 := by
    simpa [prefixWord, tailWord_4152757, baseEnd_4152757] using wordTrace_append hprefix tailTrace_4152757
  have hstable : (prefixWord ++ tailWord_4152757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152757).length < 2 ^ (prefixWord ++ tailWord_4152757).sum := by decide
  have hdescent : baseEnd_4152757 < baseStart_4152757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152890 : List Nat := [3, 1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_4152890 : Nat := 118140960795 + 4152890 * 2 ^ 59
def prefixEnd_4152890 : Nat := 4983230072969 + 3 ^ 40 * 4152890 * 2
def baseEnd_4152890 : Nat := 473873038944524896105825

theorem tailTrace_4152890 : CollatzResearch.WordTrace tailWord_4152890 prefixEnd_4152890 473873038944524896105825 := by
  unfold tailWord_4152890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37867085481199065497566031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100978894616530841326842749 37867085481199065497566031)
  ·
    refine ⟨56800628221798598246349047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37867085481199065497566031 56800628221798598246349047)
    ·
      refine ⟨85200942332697897369523571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56800628221798598246349047 85200942332697897369523571)
      ·
        refine ⟨127801413499046846054285357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85200942332697897369523571 127801413499046846054285357)
        ·
          refine ⟨47925530062142567270357009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127801413499046846054285357 47925530062142567270357009)
          ·
            refine ⟨35944147546606925452767757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47925530062142567270357009 35944147546606925452767757)
            ·
              refine ⟨13479055329977597044787909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35944147546606925452767757 13479055329977597044787909)
              ·
                refine ⟨2527322874370799445897733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13479055329977597044787909 2527322874370799445897733)
                ·
                  refine ⟨473873038944524896105825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527322874370799445897733 473873038944524896105825)
                  ·
                    rfl

theorem cell22_4152890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_4152890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152890 prefixEnd_4152890 := by exact prefixLift 4152890
  have htrace : WordTrace (prefixWord ++ tailWord_4152890) baseStart_4152890 baseEnd_4152890 := by
    simpa [prefixWord, tailWord_4152890, baseEnd_4152890] using wordTrace_append hprefix tailTrace_4152890
  have hstable : (prefixWord ++ tailWord_4152890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152890).length < 2 ^ (prefixWord ++ tailWord_4152890).sum := by decide
  have hdescent : baseEnd_4152890 < baseStart_4152890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152984 : List Nat := [2, 1, 2, 4, 1, 2, 3, 3, 1, 3]
def baseStart_4152984 : Nat := 118140960795 + 4152984 * 2 ^ 59
def prefixEnd_4152984 : Nat := 4983230072969 + 3 ^ 40 * 4152984 * 2
def baseEnd_4152984 : Nat := 1421651294954589776467187

theorem tailTrace_4152984 : CollatzResearch.WordTrace tailWord_4152984 prefixEnd_4152984 1421651294954589776467187 := by
  unfold tailWord_4152984
  simp only [CollatzResearch.WordTrace]
  refine ⟨75735885193227858022093003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100981180257637144029457337 75735885193227858022093003)
  ·
    refine ⟨113603827789841787033139505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75735885193227858022093003 113603827789841787033139505)
    ·
      refine ⟨85202870842381340274854629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113603827789841787033139505 85202870842381340274854629)
      ·
        refine ⟨15975538282946501301535243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85202870842381340274854629 15975538282946501301535243)
        ·
          refine ⟨23963307424419751952302865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15975538282946501301535243 23963307424419751952302865)
          ·
            refine ⟨17972480568314813964227149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23963307424419751952302865 17972480568314813964227149)
            ·
              refine ⟨6739680213118055236585181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17972480568314813964227149 6739680213118055236585181)
              ·
                refine ⟨2527380079919270713719443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6739680213118055236585181 2527380079919270713719443)
                ·
                  refine ⟨3791070119878906070579165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527380079919270713719443 3791070119878906070579165)
                  ·
                    refine ⟨1421651294954589776467187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3791070119878906070579165 1421651294954589776467187)
                    ·
                      rfl

theorem cell22_4152984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_4152984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4152984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4152984 prefixEnd_4152984 := by exact prefixLift 4152984
  have htrace : WordTrace (prefixWord ++ tailWord_4152984) baseStart_4152984 baseEnd_4152984 := by
    simpa [prefixWord, tailWord_4152984, baseEnd_4152984] using wordTrace_append hprefix tailTrace_4152984
  have hstable : (prefixWord ++ tailWord_4152984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152984).length < 2 ^ (prefixWord ++ tailWord_4152984).sum := by decide
  have hdescent : baseEnd_4152984 < baseStart_4152984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153014 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_4153014 : Nat := 118140960795 + 4153014 * 2 ^ 59
def prefixEnd_4153014 : Nat := 4983230072969 + 3 ^ 40 * 4153014 * 2
def baseEnd_4153014 : Nat := 473887188189226566072365

theorem tailTrace_4153014 : CollatzResearch.WordTrace tailWord_4153014 prefixEnd_4153014 473887188189226566072365 := by
  unfold tailWord_4153014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9467054036021689447986131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100981909717564687445185397 9467054036021689447986131)
  ·
    refine ⟨14200581054032534171979197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9467054036021689447986131 14200581054032534171979197)
    ·
      refine ⟨5325217895262200314492199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14200581054032534171979197 5325217895262200314492199)
      ·
        refine ⟨7987826842893300471738299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5325217895262200314492199 7987826842893300471738299)
        ·
          refine ⟨11981740264339950707607449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7987826842893300471738299 11981740264339950707607449)
          ·
            refine ⟨8986305198254963030705587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11981740264339950707607449 8986305198254963030705587)
            ·
              refine ⟨13479457797382444546058381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986305198254963030705587 13479457797382444546058381)
              ·
                refine ⟨5054796674018416704771893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13479457797382444546058381 5054796674018416704771893)
                ·
                  refine ⟨473887188189226566072365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5054796674018416704771893 473887188189226566072365)
                  ·
                    rfl

theorem cell22_4153014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_4153014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153014 prefixEnd_4153014 := by exact prefixLift 4153014
  have htrace : WordTrace (prefixWord ++ tailWord_4153014) baseStart_4153014 baseEnd_4153014 := by
    simpa [prefixWord, tailWord_4153014, baseEnd_4153014] using wordTrace_append hprefix tailTrace_4153014
  have hstable : (prefixWord ++ tailWord_4153014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153014).length < 2 ^ (prefixWord ++ tailWord_4153014).sum := by decide
  have hdescent : baseEnd_4153014 < baseStart_4153014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153040 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 4, 3]
def baseStart_4153040 : Nat := 118140960795 + 4153040 * 2 ^ 59
def prefixEnd_4153040 : Nat := 4983230072969 + 3 ^ 40 * 4153040 * 2
def baseEnd_4153040 : Nat := 1421670464899024297067015

theorem tailTrace_4153040 : CollatzResearch.WordTrace tailWord_4153040 prefixEnd_4153040 1421670464899024297067015 := by
  unfold tailWord_4153040
  simp only [CollatzResearch.WordTrace]
  refine ⟨75736906437126418804112287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100982541916168558405483049 75736906437126418804112287)
  ·
    refine ⟨113605359655689628206168431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75736906437126418804112287 113605359655689628206168431)
    ·
      refine ⟨170408039483534442309252647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113605359655689628206168431 170408039483534442309252647)
      ·
        refine ⟨255612059225301663463878971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170408039483534442309252647 255612059225301663463878971)
        ·
          refine ⟨383418088837952495195818457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255612059225301663463878971 383418088837952495195818457)
          ·
            refine ⟨287563566628464371396863843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383418088837952495195818457 287563566628464371396863843)
            ·
              refine ⟨431345349942696557095295765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287563566628464371396863843 431345349942696557095295765)
              ·
                refine ⟨20219313278563901113841989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 431345349942696557095295765 20219313278563901113841989)
                ·
                  refine ⟨3791121239730731458845373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20219313278563901113841989 3791121239730731458845373)
                  ·
                    refine ⟨1421670464899024297067015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3791121239730731458845373 1421670464899024297067015)
                    ·
                      rfl

theorem cell22_4153040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4, 3].length) (baseStart_4153040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153040 prefixEnd_4153040 := by exact prefixLift 4153040
  have htrace : WordTrace (prefixWord ++ tailWord_4153040) baseStart_4153040 baseEnd_4153040 := by
    simpa [prefixWord, tailWord_4153040, baseEnd_4153040] using wordTrace_append hprefix tailTrace_4153040
  have hstable : (prefixWord ++ tailWord_4153040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153040).length < 2 ^ (prefixWord ++ tailWord_4153040).sum := by decide
  have hdescent : baseEnd_4153040 < baseStart_4153040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153055 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 2, 4]
def baseStart_4153055 : Nat := 118140960795 + 4153055 * 2 ^ 59
def prefixEnd_4153055 : Nat := 4983230072969 + 3 ^ 40 * 4153055 * 2
def baseEnd_4153055 : Nat := 1421675599705569257941969

theorem tailTrace_4153055 : CollatzResearch.WordTrace tailWord_4153055 prefixEnd_4153055 1421675599705569257941969 := by
  unfold tailWord_4153055
  simp only [CollatzResearch.WordTrace]
  refine ⟨151474359969198495170020619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100982906646132330113347079 151474359969198495170020619)
  ·
    refine ⟨227211539953797742755030929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151474359969198495170020619 227211539953797742755030929)
    ·
      refine ⟨170408654965348307066273197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227211539953797742755030929 170408654965348307066273197)
      ·
        refine ⟨63903245612005615149852449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170408654965348307066273197 63903245612005615149852449)
        ·
          refine ⟨47927434209004211362389337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63903245612005615149852449 47927434209004211362389337)
          ·
            refine ⟨35945575656753158521792003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47927434209004211362389337 35945575656753158521792003)
            ·
              refine ⟨53918363485129737782688005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35945575656753158521792003 53918363485129737782688005)
              ·
                refine ⟨10109693153461825834254001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53918363485129737782688005 10109693153461825834254001)
                ·
                  refine ⟨7582269865096369375690501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10109693153461825834254001 7582269865096369375690501)
                  ·
                    refine ⟨1421675599705569257941969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7582269865096369375690501 1421675599705569257941969)
                    ·
                      rfl

theorem cell22_4153055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_4153055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153055 prefixEnd_4153055 := by exact prefixLift 4153055
  have htrace : WordTrace (prefixWord ++ tailWord_4153055) baseStart_4153055 baseEnd_4153055 := by
    simpa [prefixWord, tailWord_4153055, baseEnd_4153055] using wordTrace_append hprefix tailTrace_4153055
  have hstable : (prefixWord ++ tailWord_4153055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153055).length < 2 ^ (prefixWord ++ tailWord_4153055).sum := by decide
  have hdescent : baseEnd_4153055 < baseStart_4153055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153059 : List Nat := [1, 1, 1, 7, 2, 1, 1, 4, 4]
def baseStart_4153059 : Nat := 118140960795 + 4153059 * 2 ^ 59
def prefixEnd_4153059 : Nat := 4983230072969 + 3 ^ 40 * 4153059 * 2
def baseEnd_4153059 : Nat := 473892322995771526947319

theorem tailTrace_4153059 : CollatzResearch.WordTrace tailWord_4153059 prefixEnd_4153059 473892322995771526947319 := by
  unfold tailWord_4153059
  simp only [CollatzResearch.WordTrace]
  refine ⟨151474505861184003853166231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100983003907456002568777487 151474505861184003853166231)
  ·
    refine ⟨227211758791776005779749347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151474505861184003853166231 227211758791776005779749347)
    ·
      refine ⟨340817638187664008669624021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227211758791776005779749347 340817638187664008669624021)
      ·
        refine ⟨7987913395023375203194313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 340817638187664008669624021 7987913395023375203194313)
        ·
          refine ⟨5990935046267531402395735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7987913395023375203194313 5990935046267531402395735)
          ·
            refine ⟨8986402569401297103593603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5990935046267531402395735 8986402569401297103593603)
            ·
              refine ⟨13479603854101945655390405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986402569401297103593603 13479603854101945655390405)
              ·
                refine ⟨2527425722644114810385701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13479603854101945655390405 2527425722644114810385701)
                ·
                  refine ⟨473892322995771526947319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527425722644114810385701 473892322995771526947319)
                  ·
                    rfl

theorem cell22_4153059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 4].length) (baseStart_4153059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153059 prefixEnd_4153059 := by exact prefixLift 4153059
  have htrace : WordTrace (prefixWord ++ tailWord_4153059) baseStart_4153059 baseEnd_4153059 := by
    simpa [prefixWord, tailWord_4153059, baseEnd_4153059] using wordTrace_append hprefix tailTrace_4153059
  have hstable : (prefixWord ++ tailWord_4153059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153059).length < 2 ^ (prefixWord ++ tailWord_4153059).sum := by decide
  have hdescent : baseEnd_4153059 < baseStart_4153059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153108 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4153108 : Nat := 118140960795 + 4153108 * 2 ^ 59
def prefixEnd_4153108 : Nat := 4983230072969 + 3 ^ 40 * 4153108 * 2
def baseEnd_4153108 : Nat := 1421693742688694786366807

theorem tailTrace_4153108 : CollatzResearch.WordTrace tailWord_4153108 prefixEnd_4153108 1421693742688694786366807 := by
  unfold tailWord_4153108
  simp only [CollatzResearch.WordTrace]
  refine ⟨75738146519003242610849989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100984195358670990147799985 75738146519003242610849989)
  ·
    refine ⟨14200902472313107989534373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75738146519003242610849989 14200902472313107989534373)
    ·
      refine ⟨2662669213558707748037695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14200902472313107989534373 2662669213558707748037695)
      ·
        refine ⟨3994003820338061622056543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662669213558707748037695 3994003820338061622056543)
        ·
          refine ⟨5991005730507092433084815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3994003820338061622056543 5991005730507092433084815)
          ·
            refine ⟨8986508595760638649627223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991005730507092433084815 8986508595760638649627223)
            ·
              refine ⟨13479762893640957974440835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986508595760638649627223 13479762893640957974440835)
              ·
                refine ⟨20219644340461436961661253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13479762893640957974440835 20219644340461436961661253)
                ·
                  refine ⟨3791183313836519430311485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20219644340461436961661253 3791183313836519430311485)
                  ·
                    refine ⟨1421693742688694786366807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3791183313836519430311485 1421693742688694786366807)
                    ·
                      rfl

theorem cell22_4153108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4153108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153108 prefixEnd_4153108 := by exact prefixLift 4153108
  have htrace : WordTrace (prefixWord ++ tailWord_4153108) baseStart_4153108 baseEnd_4153108 := by
    simpa [prefixWord, tailWord_4153108, baseEnd_4153108] using wordTrace_append hprefix tailTrace_4153108
  have hstable : (prefixWord ++ tailWord_4153108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153108).length < 2 ^ (prefixWord ++ tailWord_4153108).sum := by decide
  have hdescent : baseEnd_4153108 < baseStart_4153108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153119 : List Nat := [1, 1, 2, 4, 2, 1, 1, 6, 1, 3]
def baseStart_4153119 : Nat := 118140960795 + 4153119 * 2 ^ 59
def prefixEnd_4153119 : Nat := 4983230072969 + 3 ^ 40 * 4153119 * 2
def baseEnd_4153119 : Nat := 1421697508213494424341773

theorem tailTrace_4153119 : CollatzResearch.WordTrace tailWord_4153119 prefixEnd_4153119 1421697508213494424341773 := by
  unfold tailWord_4153119
  simp only [CollatzResearch.WordTrace]
  refine ⟨151476694240966634100350411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100984462827311089400233607 151476694240966634100350411)
  ·
    refine ⟨227215041361449951150525617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151476694240966634100350411 227215041361449951150525617)
    ·
      refine ⟨170411281021087463362894213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227215041361449951150525617 170411281021087463362894213)
      ·
        refine ⟨31952115191453899380542665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170411281021087463362894213 31952115191453899380542665)
        ·
          refine ⟨23964086393590424535406999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31952115191453899380542665 23964086393590424535406999)
          ·
            refine ⟨35946129590385636803110499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23964086393590424535406999 35946129590385636803110499)
            ·
              refine ⟨53919194385578455204665749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35946129590385636803110499 53919194385578455204665749)
              ·
                refine ⟨2527462236823990087718707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53919194385578455204665749 2527462236823990087718707)
                ·
                  refine ⟨3791193355235985131578061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527462236823990087718707 3791193355235985131578061)
                  ·
                    refine ⟨1421697508213494424341773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3791193355235985131578061 1421697508213494424341773)
                    ·
                      rfl

theorem cell22_4153119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 1, 3].length) (baseStart_4153119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153119 prefixEnd_4153119 := by exact prefixLift 4153119
  have htrace : WordTrace (prefixWord ++ tailWord_4153119) baseStart_4153119 baseEnd_4153119 := by
    simpa [prefixWord, tailWord_4153119, baseEnd_4153119] using wordTrace_append hprefix tailTrace_4153119
  have hstable : (prefixWord ++ tailWord_4153119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153119).length < 2 ^ (prefixWord ++ tailWord_4153119).sum := by decide
  have hdescent : baseEnd_4153119 < baseStart_4153119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153162 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_4153162 : Nat := 118140960795 + 4153162 * 2 ^ 59
def prefixEnd_4153162 : Nat := 4983230072969 + 3 ^ 40 * 4153162 * 2
def baseEnd_4153162 : Nat := 1421712227992256645516641

theorem tailTrace_4153162 : CollatzResearch.WordTrace tailWord_4153162 prefixEnd_4153162 1421712227992256645516641 := by
  unfold tailWord_4153162
  simp only [CollatzResearch.WordTrace]
  refine ⟨37869565644952713111041435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100985508386540568296110493 37869565644952713111041435)
  ·
    refine ⟨56804348467429069666562153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37869565644952713111041435 56804348467429069666562153)
    ·
      refine ⟨42603261350571802249921615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56804348467429069666562153 42603261350571802249921615)
      ·
        refine ⟨63904892025857703374882423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42603261350571802249921615 63904892025857703374882423)
        ·
          refine ⟨95857338038786555062323635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63904892025857703374882423 95857338038786555062323635)
          ·
            refine ⟨143786007058179832593485453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95857338038786555062323635 143786007058179832593485453)
            ·
              refine ⟨53919752646817437222557045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143786007058179832593485453 53919752646817437222557045)
              ·
                refine ⟨5054976810639134739614723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53919752646817437222557045 5054976810639134739614723)
                ·
                  refine ⟨7582465215958702109422085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054976810639134739614723 7582465215958702109422085)
                  ·
                    refine ⟨1421712227992256645516641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7582465215958702109422085 1421712227992256645516641)
                    ·
                      rfl

theorem cell22_4153162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_4153162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153162 prefixEnd_4153162 := by exact prefixLift 4153162
  have htrace : WordTrace (prefixWord ++ tailWord_4153162) baseStart_4153162 baseEnd_4153162 := by
    simpa [prefixWord, tailWord_4153162, baseEnd_4153162] using wordTrace_append hprefix tailTrace_4153162
  have hstable : (prefixWord ++ tailWord_4153162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153162).length < 2 ^ (prefixWord ++ tailWord_4153162).sum := by decide
  have hdescent : baseEnd_4153162 < baseStart_4153162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153192 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_4153192 : Nat := 118140960795 + 4153192 * 2 ^ 59
def prefixEnd_4153192 : Nat := 4983230072969 + 3 ^ 40 * 4153192 * 2
def baseEnd_4153192 : Nat := 1421722497605346567266549

theorem tailTrace_4153192 : CollatzResearch.WordTrace tailWord_4153192 prefixEnd_4153192 1421722497605346567266549 := by
  unfold tailWord_4153192
  simp only [CollatzResearch.WordTrace]
  refine ⟨75739678384851083783878915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100986237846468111711838553 75739678384851083783878915)
  ·
    refine ⟨113609517577276625675818373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75739678384851083783878915 113609517577276625675818373)
    ·
      refine ⟨21301784545739367314215945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113609517577276625675818373 21301784545739367314215945)
      ·
        refine ⟨15976338409304525485661959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21301784545739367314215945 15976338409304525485661959)
        ·
          refine ⟨23964507613956788228492939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15976338409304525485661959 23964507613956788228492939)
          ·
            refine ⟨35946761420935182342739409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23964507613956788228492939 35946761420935182342739409)
            ·
              refine ⟨26960071065701386757054557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35946761420935182342739409 26960071065701386757054557)
              ·
                refine ⟨10110026649638020033895459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26960071065701386757054557 10110026649638020033895459)
                ·
                  refine ⟨15165039974457030050843189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10110026649638020033895459 15165039974457030050843189)
                  ·
                    refine ⟨1421722497605346567266549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15165039974457030050843189 1421722497605346567266549)
                    ·
                      rfl

theorem cell22_4153192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_4153192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153192 prefixEnd_4153192 := by exact prefixLift 4153192
  have htrace : WordTrace (prefixWord ++ tailWord_4153192) baseStart_4153192 baseEnd_4153192 := by
    simpa [prefixWord, tailWord_4153192, baseEnd_4153192] using wordTrace_append hprefix tailTrace_4153192
  have hstable : (prefixWord ++ tailWord_4153192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153192).length < 2 ^ (prefixWord ++ tailWord_4153192).sum := by decide
  have hdescent : baseEnd_4153192 < baseStart_4153192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153297 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_4153297 : Nat := 118140960795 + 4153297 * 2 ^ 59
def prefixEnd_4153297 : Nat := 4983230072969 + 3 ^ 40 * 4153297 * 2
def baseEnd_4153297 : Nat := 1421758441251161293391227

theorem tailTrace_4153297 : CollatzResearch.WordTrace tailWord_4153297 prefixEnd_4153297 1421758441251161293391227 := by
  unfold tailWord_4153297
  simp only [CollatzResearch.WordTrace]
  refine ⟨151483186434321770500330145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100988790956214513666886763 151483186434321770500330145)
  ·
    refine ⟨113612389825741327875247609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151483186434321770500330145 113612389825741327875247609)
    ·
      refine ⟨85209292369305995906435707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113612389825741327875247609 85209292369305995906435707)
      ·
        refine ⟨127813938553958993859653561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85209292369305995906435707 127813938553958993859653561)
        ·
          refine ⟨95860453915469245394740171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127813938553958993859653561 95860453915469245394740171)
          ·
            refine ⟨143790680873203868092110257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95860453915469245394740171 143790680873203868092110257)
            ·
              refine ⟨107843010654902901069082693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143790680873203868092110257 107843010654902901069082693)
              ·
                refine ⟨20220564497794293950453005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107843010654902901069082693 20220564497794293950453005)
                ·
                  refine ⟨7582711686672860231419877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20220564497794293950453005 7582711686672860231419877)
                  ·
                    refine ⟨1421758441251161293391227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7582711686672860231419877 1421758441251161293391227)
                    ·
                      rfl

theorem cell22_4153297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_4153297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153297 prefixEnd_4153297 := by exact prefixLift 4153297
  have htrace : WordTrace (prefixWord ++ tailWord_4153297) baseStart_4153297 baseEnd_4153297 := by
    simpa [prefixWord, tailWord_4153297, baseEnd_4153297] using wordTrace_append hprefix tailTrace_4153297
  have hstable : (prefixWord ++ tailWord_4153297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153297).length < 2 ^ (prefixWord ++ tailWord_4153297).sum := by decide
  have hdescent : baseEnd_4153297 < baseStart_4153297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153301 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 5]
def baseStart_4153301 : Nat := 118140960795 + 4153301 * 2 ^ 59
def prefixEnd_4153301 : Nat := 4983230072969 + 3 ^ 40 * 4153301 * 2
def baseEnd_4153301 : Nat := 473919936844302205430405

theorem tailTrace_4153301 : CollatzResearch.WordTrace tailWord_4153301 prefixEnd_4153301 473919936844302205430405 := by
  unfold tailWord_4153301
  simp only [CollatzResearch.WordTrace]
  refine ⟨151483332326307279183475757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100988888217538186122317171 151483332326307279183475757)
  ·
    refine ⟨56806249622365229693803409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151483332326307279183475757 56806249622365229693803409)
    ·
      refine ⟨42604687216773922270352557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56806249622365229693803409 42604687216773922270352557)
      ·
        refine ⟨15976757706290220851382209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42604687216773922270352557 15976757706290220851382209)
        ·
          refine ⟨11982568279717665638536657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15976757706290220851382209 11982568279717665638536657)
          ·
            refine ⟨8986926209788249228902493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11982568279717665638536657 8986926209788249228902493)
            ·
              refine ⟨3370097328670593460838435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8986926209788249228902493 3370097328670593460838435)
              ·
                refine ⟨5055145993005890191257653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370097328670593460838435 5055145993005890191257653)
                ·
                  refine ⟨473919936844302205430405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5055145993005890191257653 473919936844302205430405)
                  ·
                    rfl

theorem cell22_4153301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_4153301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153301 prefixEnd_4153301 := by exact prefixLift 4153301
  have htrace : WordTrace (prefixWord ++ tailWord_4153301) baseStart_4153301 baseEnd_4153301 := by
    simpa [prefixWord, tailWord_4153301, baseEnd_4153301] using wordTrace_append hprefix tailTrace_4153301
  have hstable : (prefixWord ++ tailWord_4153301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153301).length < 2 ^ (prefixWord ++ tailWord_4153301).sum := by decide
  have hdescent : baseEnd_4153301 < baseStart_4153301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153327 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 3, 5]
def baseStart_4153327 : Nat := 118140960795 + 4153327 * 2 ^ 59
def prefixEnd_4153327 : Nat := 4983230072969 + 3 ^ 40 * 4153327 * 2
def baseEnd_4153327 : Nat := 1421768710864251215141135

theorem tailTrace_4153327 : CollatzResearch.WordTrace tailWord_4153327 prefixEnd_4153327 1421768710864251215141135 := by
  unfold tailWord_4153327
  simp only [CollatzResearch.WordTrace]
  refine ⟨151484280624213085623922235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100989520416142057082614823 151484280624213085623922235)
  ·
    refine ⟨227226420936319628435883353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151484280624213085623922235 227226420936319628435883353)
    ·
      refine ⟨170419815702239721326912515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227226420936319628435883353 170419815702239721326912515)
      ·
        refine ⟨255629723553359581990368773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170419815702239721326912515 255629723553359581990368773)
        ·
          refine ⟨47930573166254921623194145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255629723553359581990368773 47930573166254921623194145)
          ·
            refine ⟨35947929874691191217395609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47930573166254921623194145 35947929874691191217395609)
            ·
              refine ⟨26960947406018393413046707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35947929874691191217395609 26960947406018393413046707)
              ·
                refine ⟨40441421109027590119570061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26960947406018393413046707 40441421109027590119570061)
                ·
                  refine ⟨15165532915885346294838773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40441421109027590119570061 15165532915885346294838773)
                  ·
                    refine ⟨1421768710864251215141135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15165532915885346294838773 1421768710864251215141135)
                    ·
                      rfl

theorem cell22_4153327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_4153327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153327 prefixEnd_4153327 := by exact prefixLift 4153327
  have htrace : WordTrace (prefixWord ++ tailWord_4153327) baseStart_4153327 baseEnd_4153327 := by
    simpa [prefixWord, tailWord_4153327, baseEnd_4153327] using wordTrace_append hprefix tailTrace_4153327
  have hstable : (prefixWord ++ tailWord_4153327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153327).length < 2 ^ (prefixWord ++ tailWord_4153327).sum := by decide
  have hdescent : baseEnd_4153327 < baseStart_4153327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153541 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 3, 3]
def baseStart_4153541 : Nat := 118140960795 + 4153541 * 2 ^ 59
def prefixEnd_4153541 : Nat := 4983230072969 + 3 ^ 40 * 4153541 * 2
def baseEnd_4153541 : Nat := 1421841967437625990290479

theorem tailTrace_4153541 : CollatzResearch.WordTrace tailWord_4153541 prefixEnd_4153541 1421841967437625990290479 := by
  unfold tailWord_4153541
  simp only [CollatzResearch.WordTrace]
  refine ⟨151492085845437800172212477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100994723896958533448141651 151492085845437800172212477)
  ·
    refine ⟨56809532192039175064579679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151492085845437800172212477 56809532192039175064579679)
    ·
      refine ⟨85214298288058762596869519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56809532192039175064579679 85214298288058762596869519)
      ·
        refine ⟨127821447432088143895304279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85214298288058762596869519 127821447432088143895304279)
        ·
          refine ⟨191732171148132215842956419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127821447432088143895304279 191732171148132215842956419)
          ·
            refine ⟨287598256722198323764434629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191732171148132215842956419 287598256722198323764434629)
            ·
              refine ⟨53924673135412185705831493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287598256722198323764434629 53924673135412185705831493)
              ·
                refine ⟨10110876212889784819843405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53924673135412185705831493 10110876212889784819843405)
                ·
                  refine ⟨3791578579833669307441277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10110876212889784819843405 3791578579833669307441277)
                  ·
                    refine ⟨1421841967437625990290479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3791578579833669307441277 1421841967437625990290479)
                    ·
                      rfl

theorem cell22_4153541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_4153541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153541 prefixEnd_4153541 := by exact prefixLift 4153541
  have htrace : WordTrace (prefixWord ++ tailWord_4153541) baseStart_4153541 baseEnd_4153541 := by
    simpa [prefixWord, tailWord_4153541, baseEnd_4153541] using wordTrace_append hprefix tailTrace_4153541
  have hstable : (prefixWord ++ tailWord_4153541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153541).length < 2 ^ (prefixWord ++ tailWord_4153541).sum := by decide
  have hdescent : baseEnd_4153541 < baseStart_4153541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153586 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_4153586 : Nat := 118140960795 + 4153586 * 2 ^ 59
def prefixEnd_4153586 : Nat := 4983230072969 + 3 ^ 40 * 4153586 * 2
def baseEnd_4153586 : Nat := 1421857371857260872915341

theorem tailTrace_4153586 : CollatzResearch.WordTrace tailWord_4153586 prefixEnd_4153586 1421857371857260872915341 := by
  unfold tailWord_4153586
  simp only [CollatzResearch.WordTrace]
  refine ⟨37873431782568693214400153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100995818086849848571733741 37873431782568693214400153)
  ·
    refine ⟨28405073836926519910800115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37873431782568693214400153 28405073836926519910800115)
    ·
      refine ⟨42607610755389779866200173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28405073836926519910800115 42607610755389779866200173)
      ·
        refine ⟨15977854033271167449825065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42607610755389779866200173 15977854033271167449825065)
        ·
          refine ⟨11983390524953375587368799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15977854033271167449825065 11983390524953375587368799)
          ·
            refine ⟨17975085787430063381053199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11983390524953375587368799 17975085787430063381053199)
            ·
              refine ⟨26962628681145095071579799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17975085787430063381053199 26962628681145095071579799)
              ·
                refine ⟨40443943021717642607369699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26962628681145095071579799 40443943021717642607369699)
                ·
                  refine ⟨60665914532576463911054549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40443943021717642607369699 60665914532576463911054549)
                  ·
                    refine ⟨1421857371857260872915341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60665914532576463911054549 1421857371857260872915341)
                    ·
                      rfl

theorem cell22_4153586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_4153586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153586 prefixEnd_4153586 := by exact prefixLift 4153586
  have htrace : WordTrace (prefixWord ++ tailWord_4153586) baseStart_4153586 baseEnd_4153586 := by
    simpa [prefixWord, tailWord_4153586, baseEnd_4153586] using wordTrace_append hprefix tailTrace_4153586
  have hstable : (prefixWord ++ tailWord_4153586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153586).length < 2 ^ (prefixWord ++ tailWord_4153586).sum := by decide
  have hdescent : baseEnd_4153586 < baseStart_4153586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153601 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_4153601 : Nat := 118140960795 + 4153601 * 2 ^ 59
def prefixEnd_4153601 : Nat := 4983230072969 + 3 ^ 40 * 4153601 * 2
def baseEnd_4153601 : Nat := 1421862506663805833790295

theorem tailTrace_4153601 : CollatzResearch.WordTrace tailWord_4153601 prefixEnd_4153601 1421862506663805833790295 := by
  unfold tailWord_4153601
  simp only [CollatzResearch.WordTrace]
  refine ⟨151494274225220430419396657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100996182816813620279597771 151494274225220430419396657)
  ·
    refine ⟨113620705668915322814547493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151494274225220430419396657 113620705668915322814547493)
    ·
      refine ⟨21303882312921623027727655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113620705668915322814547493 21303882312921623027727655)
      ·
        refine ⟨31955823469382434541591483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21303882312921623027727655 31955823469382434541591483)
        ·
          refine ⟨47933735204073651812387225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31955823469382434541591483 47933735204073651812387225)
          ·
            refine ⟨35950301403055238859290419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47933735204073651812387225 35950301403055238859290419)
            ·
              refine ⟨53925452104582858288935629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35950301403055238859290419 53925452104582858288935629)
              ·
                refine ⟨20222044539218571858350861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53925452104582858288935629 20222044539218571858350861)
                ·
                  refine ⟨7583266702206964446881573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20222044539218571858350861 7583266702206964446881573)
                  ·
                    refine ⟨1421862506663805833790295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7583266702206964446881573 1421862506663805833790295)
                    ·
                      rfl

theorem cell22_4153601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_4153601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153601 prefixEnd_4153601 := by exact prefixLift 4153601
  have htrace : WordTrace (prefixWord ++ tailWord_4153601) baseStart_4153601 baseEnd_4153601 := by
    simpa [prefixWord, tailWord_4153601, baseEnd_4153601] using wordTrace_append hprefix tailTrace_4153601
  have hstable : (prefixWord ++ tailWord_4153601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153601).length < 2 ^ (prefixWord ++ tailWord_4153601).sum := by decide
  have hdescent : baseEnd_4153601 < baseStart_4153601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153633 : List Nat := [1, 2, 3, 2, 1, 1, 4, 4, 4]
def baseStart_4153633 : Nat := 118140960795 + 4153633 * 2 ^ 59
def prefixEnd_4153633 : Nat := 4983230072969 + 3 ^ 40 * 4153633 * 2
def baseEnd_4153633 : Nat := 473957820305922805663399

theorem tailTrace_4153633 : CollatzResearch.WordTrace tailWord_4153633 prefixEnd_4153633 473957820305922805663399 := by
  unfold tailWord_4153633
  simp only [CollatzResearch.WordTrace]
  refine ⟨151495441361104499884561553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100996960907402999923041035 151495441361104499884561553)
  ·
    refine ⟨113621581020828374913421165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151495441361104499884561553 113621581020828374913421165)
    ·
      refine ⟨42608092882810640592532937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113621581020828374913421165 42608092882810640592532937)
      ·
        refine ⟨31956069662107980444399703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42608092882810640592532937 31956069662107980444399703)
        ·
          refine ⟨47934104493161970666599555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31956069662107980444399703 47934104493161970666599555)
          ·
            refine ⟨71901156739742955999899333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47934104493161970666599555 71901156739742955999899333)
            ·
              refine ⟨13481466888701804249981125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71901156739742955999899333 13481466888701804249981125)
              ·
                refine ⟨2527775041631588296871461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13481466888701804249981125 2527775041631588296871461)
                ·
                  refine ⟨473957820305922805663399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527775041631588296871461 473957820305922805663399)
                  ·
                    rfl

theorem cell22_4153633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 4].length) (baseStart_4153633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153633 prefixEnd_4153633 := by exact prefixLift 4153633
  have htrace : WordTrace (prefixWord ++ tailWord_4153633) baseStart_4153633 baseEnd_4153633 := by
    simpa [prefixWord, tailWord_4153633, baseEnd_4153633] using wordTrace_append hprefix tailTrace_4153633
  have hstable : (prefixWord ++ tailWord_4153633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153633).length < 2 ^ (prefixWord ++ tailWord_4153633).sum := by decide
  have hdescent : baseEnd_4153633 < baseStart_4153633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153639 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 5]
def baseStart_4153639 : Nat := 118140960795 + 4153639 * 2 ^ 59
def prefixEnd_4153639 : Nat := 4983230072969 + 3 ^ 40 * 4153639 * 2
def baseEnd_4153639 : Nat := 473958504946795467113393

theorem tailTrace_4153639 : CollatzResearch.WordTrace tailWord_4153639 prefixEnd_4153639 473958504946795467113393 := by
  unfold tailWord_4153639
  simp only [CollatzResearch.WordTrace]
  refine ⟨151495660199082762909279971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100997106799388508606186647 151495660199082762909279971)
  ·
    refine ⟨227243490298624144363919957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151495660199082762909279971 227243490298624144363919957)
    ·
      refine ⟨2663009651937001691764687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 227243490298624144363919957 2663009651937001691764687)
      ·
        refine ⟨3994514477905502537647031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663009651937001691764687 3994514477905502537647031)
        ·
          refine ⟨5991771716858253806470547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3994514477905502537647031 5991771716858253806470547)
          ·
            refine ⟨8987657575287380709705821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991771716858253806470547 8987657575287380709705821)
            ·
              refine ⟨3370371590732767766139683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8987657575287380709705821 3370371590732767766139683)
              ·
                refine ⟨5055557386099151649209525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370371590732767766139683 5055557386099151649209525)
                ·
                  refine ⟨473958504946795467113393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5055557386099151649209525 473958504946795467113393)
                  ·
                    rfl

theorem cell22_4153639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 5].length) (baseStart_4153639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153639 prefixEnd_4153639 := by exact prefixLift 4153639
  have htrace : WordTrace (prefixWord ++ tailWord_4153639) baseStart_4153639 baseEnd_4153639 := by
    simpa [prefixWord, tailWord_4153639, baseEnd_4153639] using wordTrace_append hprefix tailTrace_4153639
  have hstable : (prefixWord ++ tailWord_4153639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153639).length < 2 ^ (prefixWord ++ tailWord_4153639).sum := by decide
  have hdescent : baseEnd_4153639 < baseStart_4153639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153721 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_4153721 : Nat := 118140960795 + 4153721 * 2 ^ 59
def prefixEnd_4153721 : Nat := 4983230072969 + 3 ^ 40 * 4153721 * 2
def baseEnd_4153721 : Nat := 1421903585116165520789927

theorem tailTrace_4153721 : CollatzResearch.WordTrace tailWord_4153721 prefixEnd_4153721 1421903585116165520789927 := by
  unfold tailWord_4153721
  simp only [CollatzResearch.WordTrace]
  refine ⟨151498650984785690913765017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100999100656523793942510011 151498650984785690913765017)
  ·
    refine ⟨113623988238589268185323763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151498650984785690913765017 113623988238589268185323763)
    ·
      refine ⟨170435982357883902277985645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113623988238589268185323763 170435982357883902277985645)
      ·
        refine ⟨63913493384206463354244617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170435982357883902277985645 63913493384206463354244617)
        ·
          refine ⟨47935120038154847515683463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63913493384206463354244617 47935120038154847515683463)
          ·
            refine ⟨71902680057232271273525195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47935120038154847515683463 71902680057232271273525195)
            ·
              refine ⟨107854020085848406910287793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71902680057232271273525195 107854020085848406910287793)
              ·
                refine ⟨80890515064386305182715845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107854020085848406910287793 80890515064386305182715845)
                ·
                  refine ⟨15166971574572432221759221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80890515064386305182715845 15166971574572432221759221)
                  ·
                    refine ⟨1421903585116165520789927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15166971574572432221759221 1421903585116165520789927)
                    ·
                      rfl

theorem cell22_4153721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_4153721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153721 prefixEnd_4153721 := by exact prefixLift 4153721
  have htrace : WordTrace (prefixWord ++ tailWord_4153721) baseStart_4153721 baseEnd_4153721 := by
    simpa [prefixWord, tailWord_4153721, baseEnd_4153721] using wordTrace_append hprefix tailTrace_4153721
  have hstable : (prefixWord ++ tailWord_4153721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153721).length < 2 ^ (prefixWord ++ tailWord_4153721).sum := by decide
  have hdescent : baseEnd_4153721 < baseStart_4153721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153783 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 1, 5]
def baseStart_4153783 : Nat := 118140960795 + 4153783 * 2 ^ 59
def prefixEnd_4153783 : Nat := 4983230072969 + 3 ^ 40 * 4153783 * 2
def baseEnd_4153783 : Nat := 1421924808983218025739737

theorem tailTrace_4153783 : CollatzResearch.WordTrace tailWord_4153783 prefixEnd_4153783 1421924808983218025739737 := by
  unfold tailWord_4153783
  simp only [CollatzResearch.WordTrace]
  refine ⟨151500912310561075502522003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101000608207040717001681335 151500912310561075502522003)
  ·
    refine ⟨227251368465841613253783005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151500912310561075502522003 227251368465841613253783005)
    ·
      refine ⟨85219263174690604970168627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227251368465841613253783005 85219263174690604970168627)
      ·
        refine ⟨127828894762035907455252941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85219263174690604970168627 127828894762035907455252941)
        ·
          refine ⟨47935835535763465295719853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127828894762035907455252941 47935835535763465295719853)
          ·
            refine ⟨17975938325911299485894945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47935835535763465295719853 17975938325911299485894945)
            ·
              refine ⟨13481953744433474614421209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17975938325911299485894945 13481953744433474614421209)
              ·
                refine ⟨10111465308325105960815907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13481953744433474614421209 10111465308325105960815907)
                ·
                  refine ⟨15167197962487658941223861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10111465308325105960815907 15167197962487658941223861)
                  ·
                    refine ⟨1421924808983218025739737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15167197962487658941223861 1421924808983218025739737)
                    ·
                      rfl

theorem cell22_4153783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_4153783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153783 prefixEnd_4153783 := by exact prefixLift 4153783
  have htrace : WordTrace (prefixWord ++ tailWord_4153783) baseStart_4153783 baseEnd_4153783 := by
    simpa [prefixWord, tailWord_4153783, baseEnd_4153783] using wordTrace_append hprefix tailTrace_4153783
  have hstable : (prefixWord ++ tailWord_4153783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153783).length < 2 ^ (prefixWord ++ tailWord_4153783).sum := by decide
  have hdescent : baseEnd_4153783 < baseStart_4153783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153785 : List Nat := [1, 2, 1, 4, 3, 1, 1, 5, 4]
def baseStart_4153785 : Nat := 118140960795 + 4153785 * 2 ^ 59
def prefixEnd_4153785 : Nat := 4983230072969 + 3 ^ 40 * 4153785 * 2
def baseEnd_4153785 : Nat := 473975164541363562396577

theorem tailTrace_4153785 : CollatzResearch.WordTrace tailWord_4153785 prefixEnd_4153785 473975164541363562396577 := by
  unfold tailWord_4153785
  simp only [CollatzResearch.WordTrace]
  refine ⟨151500985256553829844094809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101000656837702553229396539 151500985256553829844094809)
  ·
    refine ⟨113625738942415372383071107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151500985256553829844094809 113625738942415372383071107)
    ·
      refine ⟨170438608413623058574606661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113625738942415372383071107 170438608413623058574606661)
      ·
        refine ⟨31957239077554323482738749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170438608413623058574606661 31957239077554323482738749)
        ·
          refine ⟨11983964654082871306027031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31957239077554323482738749 11983964654082871306027031)
          ·
            refine ⟨17975946981124306959040547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11983964654082871306027031 17975946981124306959040547)
            ·
              refine ⟨26963920471686460438560821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17975946981124306959040547 26963920471686460438560821)
              ·
                refine ⟨2527867544220605666115077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26963920471686460438560821 2527867544220605666115077)
                ·
                  refine ⟨473975164541363562396577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527867544220605666115077 473975164541363562396577)
                  ·
                    rfl

theorem cell22_4153785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 4].length) (baseStart_4153785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153785 prefixEnd_4153785 := by exact prefixLift 4153785
  have htrace : WordTrace (prefixWord ++ tailWord_4153785) baseStart_4153785 baseEnd_4153785 := by
    simpa [prefixWord, tailWord_4153785, baseEnd_4153785] using wordTrace_append hprefix tailTrace_4153785
  have hstable : (prefixWord ++ tailWord_4153785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153785).length < 2 ^ (prefixWord ++ tailWord_4153785).sum := by decide
  have hdescent : baseEnd_4153785 < baseStart_4153785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153800 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 4, 3]
def baseStart_4153800 : Nat := 118140960795 + 4153800 * 2 ^ 59
def prefixEnd_4153800 : Nat := 4983230072969 + 3 ^ 40 * 4153800 * 2
def baseEnd_4153800 : Nat := 1421930628430635648064685

theorem tailTrace_4153800 : CollatzResearch.WordTrace tailWord_4153800 prefixEnd_4153800 1421930628430635648064685 := by
  unfold tailWord_4153800
  simp only [CollatzResearch.WordTrace]
  refine ⟨75750766175749743702945427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101001021567666324937260569 75750766175749743702945427)
  ·
    refine ⟨113626149263624615554418141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75750766175749743702945427 113626149263624615554418141)
    ·
      refine ⟨42609805973859230832906803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113626149263624615554418141 42609805973859230832906803)
      ·
        refine ⟨63914708960788846249360205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42609805973859230832906803 63914708960788846249360205)
        ·
          refine ⟨23968015860295817343510077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63914708960788846249360205 23968015860295817343510077)
          ·
            refine ⟨8988005947610931503816279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23968015860295817343510077 8988005947610931503816279)
            ·
              refine ⟨13482008921416397255724419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8988005947610931503816279 13482008921416397255724419)
              ·
                refine ⟨20223013382124595883586629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13482008921416397255724419 20223013382124595883586629)
                ·
                  refine ⟨3791815009148361728172493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20223013382124595883586629 3791815009148361728172493)
                  ·
                    refine ⟨1421930628430635648064685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3791815009148361728172493 1421930628430635648064685)
                    ·
                      rfl

theorem cell22_4153800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_4153800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153800 prefixEnd_4153800 := by exact prefixLift 4153800
  have htrace : WordTrace (prefixWord ++ tailWord_4153800) baseStart_4153800 baseEnd_4153800 := by
    simpa [prefixWord, tailWord_4153800, baseEnd_4153800] using wordTrace_append hprefix tailTrace_4153800
  have hstable : (prefixWord ++ tailWord_4153800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153800).length < 2 ^ (prefixWord ++ tailWord_4153800).sum := by decide
  have hdescent : baseEnd_4153800 < baseStart_4153800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153817 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 2, 3]
def baseStart_4153817 : Nat := 118140960795 + 4153817 * 2 ^ 59
def prefixEnd_4153817 : Nat := 4983230072969 + 3 ^ 40 * 4153817 * 2
def baseEnd_4153817 : Nat := 1421936447878053270389633

theorem tailTrace_4153817 : CollatzResearch.WordTrace tailWord_4153817 prefixEnd_4153817 1421936447878053270389633 := by
  unfold tailWord_4153817
  simp only [CollatzResearch.WordTrace]
  refine ⟨151502152392437899309259705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101001434928291932872839803 151502152392437899309259705)
  ·
    refine ⟨113626614294328424481944779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151502152392437899309259705 113626614294328424481944779)
    ·
      refine ⟨170439921441492636722917169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113626614294328424481944779 170439921441492636722917169)
      ·
        refine ⟨127829941081119477542187877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170439921441492636722917169 127829941081119477542187877)
        ·
          refine ⟨23968113952709902039160227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127829941081119477542187877 23968113952709902039160227)
          ·
            refine ⟨35952170929064853058740341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23968113952709902039160227 35952170929064853058740341)
            ·
              refine ⟨3370516024599829974256907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35952170929064853058740341 3370516024599829974256907)
              ·
                refine ⟨5055774036899744961385361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370516024599829974256907 5055774036899744961385361)
                ·
                  refine ⟨3791830527674808721039021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5055774036899744961385361 3791830527674808721039021)
                  ·
                    refine ⟨1421936447878053270389633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3791830527674808721039021 1421936447878053270389633)
                    ·
                      rfl

theorem cell22_4153817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 2, 3].length) (baseStart_4153817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153817 prefixEnd_4153817 := by exact prefixLift 4153817
  have htrace : WordTrace (prefixWord ++ tailWord_4153817) baseStart_4153817 baseEnd_4153817 := by
    simpa [prefixWord, tailWord_4153817, baseEnd_4153817] using wordTrace_append hprefix tailTrace_4153817
  have hstable : (prefixWord ++ tailWord_4153817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153817).length < 2 ^ (prefixWord ++ tailWord_4153817).sum := by decide
  have hdescent : baseEnd_4153817 < baseStart_4153817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153905 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 1, 4]
def baseStart_4153905 : Nat := 118140960795 + 4153905 * 2 ^ 59
def prefixEnd_4153905 : Nat := 4983230072969 + 3 ^ 40 * 4153905 * 2
def baseEnd_4153905 : Nat := 1421966572076450374189363

theorem tailTrace_4153905 : CollatzResearch.WordTrace tailWord_4153905 prefixEnd_4153905 1421966572076450374189363 := by
  unfold tailWord_4153905
  simp only [CollatzResearch.WordTrace]
  refine ⟨151505362016119090338463169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101003574677412726892308779 151505362016119090338463169)
  ·
    refine ⟨113629021512089317753847377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151505362016119090338463169 113629021512089317753847377)
    ·
      refine ⟨85221766134066988315385533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113629021512089317753847377 85221766134066988315385533)
      ·
        refine ⟨31958162300275120618269575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85221766134066988315385533 31958162300275120618269575)
        ·
          refine ⟨47937243450412680927404363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31958162300275120618269575 47937243450412680927404363)
          ·
            refine ⟨71905865175619021391106545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47937243450412680927404363 71905865175619021391106545)
            ·
              refine ⟨53929398881714266043329909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71905865175619021391106545 53929398881714266043329909)
              ·
                refine ⟨5055881145160712441562179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53929398881714266043329909 5055881145160712441562179)
                ·
                  refine ⟨7583821717741068662343269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055881145160712441562179 7583821717741068662343269)
                  ·
                    refine ⟨1421966572076450374189363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7583821717741068662343269 1421966572076450374189363)
                    ·
                      rfl

theorem cell22_4153905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_4153905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153905 prefixEnd_4153905 := by exact prefixLift 4153905
  have htrace : WordTrace (prefixWord ++ tailWord_4153905) baseStart_4153905 baseEnd_4153905 := by
    simpa [prefixWord, tailWord_4153905, baseEnd_4153905] using wordTrace_append hprefix tailTrace_4153905
  have hstable : (prefixWord ++ tailWord_4153905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153905).length < 2 ^ (prefixWord ++ tailWord_4153905).sum := by decide
  have hdescent : baseEnd_4153905 < baseStart_4153905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153965 : List Nat := [1, 5, 1, 1, 3, 2, 9]
def baseStart_4153965 : Nat := 118140960795 + 4153965 * 2 ^ 59
def prefixEnd_4153965 : Nat := 4983230072969 + 3 ^ 40 * 4153965 * 2
def baseEnd_4153965 : Nat := 52666189307504822877377

theorem tailTrace_4153965 : CollatzResearch.WordTrace tailWord_4153965 prefixEnd_4153965 52666189307504822877377 := by
  unfold tailWord_4153965
  simp only [CollatzResearch.WordTrace]
  refine ⟨151507550395901720585647349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101005033597267813723764899 151507550395901720585647349)
  ·
    refine ⟨14203832849615786304904439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151507550395901720585647349 14203832849615786304904439)
    ·
      refine ⟨21305749274423679457356659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14203832849615786304904439 21305749274423679457356659)
      ·
        refine ⟨31958623911635519186034989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21305749274423679457356659 31958623911635519186034989)
        ·
          refine ⟨11984483966863319694763121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31958623911635519186034989 11984483966863319694763121)
          ·
            refine ⟨8988362975147489771072341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11984483966863319694763121 8988362975147489771072341)
            ·
              refine ⟨52666189307504822877377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8988362975147489771072341 52666189307504822877377)
              ·
                rfl

theorem cell22_4153965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 9].length) (baseStart_4153965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4153965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4153965 prefixEnd_4153965 := by exact prefixLift 4153965
  have htrace : WordTrace (prefixWord ++ tailWord_4153965) baseStart_4153965 baseEnd_4153965 := by
    simpa [prefixWord, tailWord_4153965, baseEnd_4153965] using wordTrace_append hprefix tailTrace_4153965
  have hstable : (prefixWord ++ tailWord_4153965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153965).length < 2 ^ (prefixWord ++ tailWord_4153965).sum := by decide
  have hdescent : baseEnd_4153965 < baseStart_4153965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154031 : List Nat := [1, 1, 2, 1, 2, 6, 3, 2, 1, 3]
def baseStart_4154031 : Nat := 118140960795 + 4154031 * 2 ^ 59
def prefixEnd_4154031 : Nat := 4983230072969 + 3 ^ 40 * 4154031 * 2
def baseEnd_4154031 : Nat := 1422009704451428045538977

theorem tailTrace_4154031 : CollatzResearch.WordTrace tailWord_4154031 prefixEnd_4154031 1422009704451428045538977 := by
  unfold tailWord_4154031
  simp only [CollatzResearch.WordTrace]
  refine ⟨151509957613662613857549947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101006638409108409238366631 151509957613662613857549947)
  ·
    refine ⟨227264936420493920786324921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151509957613662613857549947 227264936420493920786324921)
    ·
      refine ⟨170448702315370440589743691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227264936420493920786324921 170448702315370440589743691)
      ·
        refine ⟨255673053473055660884615537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170448702315370440589743691 255673053473055660884615537)
        ·
          refine ⟨191754790104791745663461653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255673053473055660884615537 191754790104791745663461653)
          ·
            refine ⟨8988505786162113077974765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191754790104791745663461653 8988505786162113077974765)
            ·
              refine ⟨3370689669810792404240537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8988505786162113077974765 3370689669810792404240537)
              ·
                refine ⟨2528017252358094303180403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3370689669810792404240537 2528017252358094303180403)
                ·
                  refine ⟨3792025878537141454770605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528017252358094303180403 3792025878537141454770605)
                  ·
                    refine ⟨1422009704451428045538977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3792025878537141454770605 1422009704451428045538977)
                    ·
                      rfl

theorem cell22_4154031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 1, 3].length) (baseStart_4154031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154031 prefixEnd_4154031 := by exact prefixLift 4154031
  have htrace : WordTrace (prefixWord ++ tailWord_4154031) baseStart_4154031 baseEnd_4154031 := by
    simpa [prefixWord, tailWord_4154031, baseEnd_4154031] using wordTrace_append hprefix tailTrace_4154031
  have hstable : (prefixWord ++ tailWord_4154031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154031).length < 2 ^ (prefixWord ++ tailWord_4154031).sum := by decide
  have hdescent : baseEnd_4154031 < baseStart_4154031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154074 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 1, 4]
def baseStart_4154074 : Nat := 118140960795 + 4154074 * 2 ^ 59
def prefixEnd_4154074 : Nat := 4983230072969 + 3 ^ 40 * 4154074 * 2
def baseEnd_4154074 : Nat := 1422024424230190266713845

theorem tailTrace_4154074 : CollatzResearch.WordTrace tailWord_4154074 prefixEnd_4154074 1422024424230190266713845 := by
  unfold tailWord_4154074
  simp only [CollatzResearch.WordTrace]
  refine ⟨37877881488126708050341319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101007683968337888134243517 37877881488126708050341319)
  ·
    refine ⟨56816822232190062075511979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37877881488126708050341319 56816822232190062075511979)
    ·
      refine ⟨85225233348285093113267969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56816822232190062075511979 85225233348285093113267969)
      ·
        refine ⟨63918925011213819834950977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85225233348285093113267969 63918925011213819834950977)
        ·
          refine ⟨47939193758410364876213233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63918925011213819834950977 47939193758410364876213233)
          ·
            refine ⟨35954395318807773657159925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47939193758410364876213233 35954395318807773657159925)
            ·
              refine ⟨3370724561138228780358743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35954395318807773657159925 3370724561138228780358743)
              ·
                refine ⟨5056086841707343170538115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370724561138228780358743 5056086841707343170538115)
                ·
                  refine ⟨7584130262561014755807173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5056086841707343170538115 7584130262561014755807173)
                  ·
                    refine ⟨1422024424230190266713845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7584130262561014755807173 1422024424230190266713845)
                    ·
                      rfl

theorem cell22_4154074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_4154074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154074 prefixEnd_4154074 := by exact prefixLift 4154074
  have htrace : WordTrace (prefixWord ++ tailWord_4154074) baseStart_4154074 baseEnd_4154074 := by
    simpa [prefixWord, tailWord_4154074, baseEnd_4154074] using wordTrace_append hprefix tailTrace_4154074
  have hstable : (prefixWord ++ tailWord_4154074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154074).length < 2 ^ (prefixWord ++ tailWord_4154074).sum := by decide
  have hdescent : baseEnd_4154074 < baseStart_4154074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
