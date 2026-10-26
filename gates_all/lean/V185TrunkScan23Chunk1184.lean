import V185TrunkScan23Chunk1183

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7014768 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_7014768 : Nat := 118140960795 + 7014768 * 2 ^ 59
def prefixEnd_7014768 : Nat := 4983230072969 + 3 ^ 40 * 7014768 * 2
def baseEnd_7014768 : Nat := 3601947663778315921639675

theorem tailTrace_7014768 : CollatzResearch.WordTrace tailWord_7014768 prefixEnd_7014768 3601947663778315921639675 := by
  unfold tailWord_7014768
  simp only [CollatzResearch.WordTrace]
  refine ⟨127924803925350518919854479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170566405233800691893139305 127924803925350518919854479)
  ·
    refine ⟨191887205888025778379781719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127924803925350518919854479 191887205888025778379781719)
    ·
      refine ⟨287830808832038667569672579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191887205888025778379781719 287830808832038667569672579)
      ·
        refine ⟨431746213248058001354508869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287830808832038667569672579 431746213248058001354508869)
        ·
          refine ⟨80952414984010875253970413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431746213248058001354508869 80952414984010875253970413)
          ·
            refine ⟨30357155619004078220238905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80952414984010875253970413 30357155619004078220238905)
            ·
              refine ⟨22767866714253058665179179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30357155619004078220238905 22767866714253058665179179)
              ·
                refine ⟨34151800071379587997768769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22767866714253058665179179 34151800071379587997768769)
                ·
                  refine ⟨25613850053534690998326577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34151800071379587997768769 25613850053534690998326577)
                  ·
                    refine ⟨19210387540151018248744933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25613850053534690998326577 19210387540151018248744933)
                    ·
                      refine ⟨3601947663778315921639675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19210387540151018248744933 3601947663778315921639675)
                      ·
                        rfl

theorem cell23_7014768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_7014768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014768 prefixEnd_7014768 := by exact prefixLift 7014768
  have htrace : WordTrace (prefixWord ++ tailWord_7014768) baseStart_7014768 baseEnd_7014768 := by
    simpa [prefixWord, tailWord_7014768, baseEnd_7014768] using wordTrace_append hprefix tailTrace_7014768
  have hstable : (prefixWord ++ tailWord_7014768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014768).length < 2 ^ (prefixWord ++ tailWord_7014768).sum := by decide
  have hdescent : baseEnd_7014768 < baseStart_7014768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014795 : List Nat := [1, 1, 1, 1, 4, 4, 3, 3, 5]
def baseStart_7014795 : Nat := 118140960795 + 7014795 * 2 ^ 59
def prefixEnd_7014795 : Nat := 4983230072969 + 3 ^ 40 * 7014795 * 2
def baseEnd_7014795 : Nat := 400217947528443035111339

theorem tailTrace_7014795 : CollatzResearch.WordTrace tailWord_7014795 prefixEnd_7014795 400217947528443035111339 := by
  unfold tailWord_7014795
  simp only [CollatzResearch.WordTrace]
  refine ⟨255850592621603221450941839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170567061747735480967294559 255850592621603221450941839)
  ·
    refine ⟨383775888932404832176412759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255850592621603221450941839 383775888932404832176412759)
    ·
      refine ⟨575663833398607248264619139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383775888932404832176412759 575663833398607248264619139)
      ·
        refine ⟨863495750097910872396928709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575663833398607248264619139 863495750097910872396928709)
        ·
          refine ⟨161905453143358288574424133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 863495750097910872396928709 161905453143358288574424133)
          ·
            refine ⟨30357272464379679107704525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161905453143358288574424133 30357272464379679107704525)
            ·
              refine ⟨11383977174142379665389197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30357272464379679107704525 11383977174142379665389197)
              ·
                refine ⟨4268991440303392374520949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11383977174142379665389197 4268991440303392374520949)
                ·
                  refine ⟨400217947528443035111339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4268991440303392374520949 400217947528443035111339)
                  ·
                    rfl

theorem cell23_7014795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 5].length) (baseStart_7014795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014795 prefixEnd_7014795 := by exact prefixLift 7014795
  have htrace : WordTrace (prefixWord ++ tailWord_7014795) baseStart_7014795 baseEnd_7014795 := by
    simpa [prefixWord, tailWord_7014795, baseEnd_7014795] using wordTrace_append hprefix tailTrace_7014795
  have hstable : (prefixWord ++ tailWord_7014795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014795).length < 2 ^ (prefixWord ++ tailWord_7014795).sum := by decide
  have hdescent : baseEnd_7014795 < baseStart_7014795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014815 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 2, 5, 2]
def baseStart_7014815 : Nat := 118140960795 + 7014815 * 2 ^ 59
def prefixEnd_7014815 : Nat := 4983230072969 + 3 ^ 40 * 7014815 * 2
def baseEnd_7014815 : Nat := 3601971797369077237751959

theorem tailTrace_7014815 : CollatzResearch.WordTrace tailWord_7014815 prefixEnd_7014815 3601971797369077237751959 := by
  unfold tailWord_7014815
  simp only [CollatzResearch.WordTrace]
  refine ⟨255851322081530764866669899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170567548054353843244446599 255851322081530764866669899)
  ·
    refine ⟨383776983122296147300004849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255851322081530764866669899 383776983122296147300004849)
    ·
      refine ⟨287832737341722110475003637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383776983122296147300004849 287832737341722110475003637)
      ·
        refine ⟨26984319125786447857031591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 287832737341722110475003637 26984319125786447857031591)
        ·
          refine ⟨40476478688679671785547387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26984319125786447857031591 40476478688679671785547387)
          ·
            refine ⟨60714718033019507678321081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40476478688679671785547387 60714718033019507678321081)
            ·
              refine ⟨45536038524764630758740811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60714718033019507678321081 45536038524764630758740811)
              ·
                refine ⟨68304057787146946138111217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45536038524764630758740811 68304057787146946138111217)
                ·
                  refine ⟨51228043340360209603583413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68304057787146946138111217 51228043340360209603583413)
                  ·
                    refine ⟨4802629063158769650335945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51228043340360209603583413 4802629063158769650335945)
                    ·
                      refine ⟨3601971797369077237751959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802629063158769650335945 3601971797369077237751959)
                      ·
                        rfl

theorem cell23_7014815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_7014815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014815 prefixEnd_7014815 := by exact prefixLift 7014815
  have htrace : WordTrace (prefixWord ++ tailWord_7014815) baseStart_7014815 baseEnd_7014815 := by
    simpa [prefixWord, tailWord_7014815, baseEnd_7014815] using wordTrace_append hprefix tailTrace_7014815
  have hstable : (prefixWord ++ tailWord_7014815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014815).length < 2 ^ (prefixWord ++ tailWord_7014815).sum := by decide
  have hdescent : baseEnd_7014815 < baseStart_7014815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014828 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_7014828 : Nat := 118140960795 + 7014828 * 2 ^ 59
def prefixEnd_7014828 : Nat := 4983230072969 + 3 ^ 40 * 7014828 * 2
def baseEnd_7014828 : Nat := 3601978472617585686889399

theorem tailTrace_7014828 : CollatzResearch.WordTrace tailWord_7014828 prefixEnd_7014828 3601978472617585686889399 := by
  unfold tailWord_7014828
  simp only [CollatzResearch.WordTrace]
  refine ⟨127925898115241834043446569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170567864153655778724595425 127925898115241834043446569)
  ·
    refine ⟨95944423586431375532584927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127925898115241834043446569 95944423586431375532584927)
    ·
      refine ⟨143916635379647063298877391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95944423586431375532584927 143916635379647063298877391)
      ·
        refine ⟨215874953069470594948316087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143916635379647063298877391 215874953069470594948316087)
        ·
          refine ⟨323812429604205892422474131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215874953069470594948316087 323812429604205892422474131)
          ·
            refine ⟨485718644406308838633711197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323812429604205892422474131 485718644406308838633711197)
            ·
              refine ⟨182144491652365814487641699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485718644406308838633711197 182144491652365814487641699)
              ·
                refine ⟨273216737478548721731462549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182144491652365814487641699 273216737478548721731462549)
                ·
                  refine ⟨12807034569306971331162307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 273216737478548721731462549 12807034569306971331162307)
                  ·
                    refine ⟨19210551853960456996743461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12807034569306971331162307 19210551853960456996743461)
                    ·
                      refine ⟨3601978472617585686889399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19210551853960456996743461 3601978472617585686889399)
                      ·
                        rfl

theorem cell23_7014828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_7014828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014828 prefixEnd_7014828 := by exact prefixLift 7014828
  have htrace : WordTrace (prefixWord ++ tailWord_7014828) baseStart_7014828 baseEnd_7014828 := by
    simpa [prefixWord, tailWord_7014828, baseEnd_7014828] using wordTrace_append hprefix tailTrace_7014828
  have hstable : (prefixWord ++ tailWord_7014828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014828).length < 2 ^ (prefixWord ++ tailWord_7014828).sum := by decide
  have hdescent : baseEnd_7014828 < baseStart_7014828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014845 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_7014845 : Nat := 118140960795 + 7014845 * 2 ^ 59
def prefixEnd_7014845 : Nat := 4983230072969 + 3 ^ 40 * 7014845 * 2
def baseEnd_7014845 : Nat := 3601987201788712120376821

theorem tailTrace_7014845 : CollatzResearch.WordTrace tailWord_7014845 prefixEnd_7014845 3601987201788712120376821 := by
  unfold tailWord_7014845
  simp only [CollatzResearch.WordTrace]
  refine ⟨255852416271422079990261989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170568277514281386660174659 255852416271422079990261989)
  ·
    refine ⟨47972328050891639998174123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255852416271422079990261989 47972328050891639998174123)
    ·
      refine ⟨71958492076337459997261185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47972328050891639998174123 71958492076337459997261185)
      ·
        refine ⟨53968869057253094997945889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71958492076337459997261185 53968869057253094997945889)
        ·
          refine ⟨40476651792939821248459417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53968869057253094997945889 40476651792939821248459417)
          ·
            refine ⟨30357488844704865936344563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40476651792939821248459417 30357488844704865936344563)
            ·
              refine ⟨45536233267057298904516845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30357488844704865936344563 45536233267057298904516845)
              ·
                refine ⟨17076087475146487089193817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45536233267057298904516845 17076087475146487089193817)
                ·
                  refine ⟨12807065606359865316895363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17076087475146487089193817 12807065606359865316895363)
                  ·
                    refine ⟨19210598409539797975343045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12807065606359865316895363 19210598409539797975343045)
                    ·
                      refine ⟨3601987201788712120376821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19210598409539797975343045 3601987201788712120376821)
                      ·
                        rfl

theorem cell23_7014845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_7014845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014845 prefixEnd_7014845 := by exact prefixLift 7014845
  have htrace : WordTrace (prefixWord ++ tailWord_7014845) baseStart_7014845 baseEnd_7014845 := by
    simpa [prefixWord, tailWord_7014845, baseEnd_7014845] using wordTrace_append hprefix tailTrace_7014845
  have hstable : (prefixWord ++ tailWord_7014845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014845).length < 2 ^ (prefixWord ++ tailWord_7014845).sum := by decide
  have hdescent : baseEnd_7014845 < baseStart_7014845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014858 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_7014858 : Nat := 118140960795 + 7014858 * 2 ^ 59
def prefixEnd_7014858 : Nat := 4983230072969 + 3 ^ 40 * 7014858 * 2
def baseEnd_7014858 : Nat := 3601993877037220569514261

theorem tailTrace_7014858 : CollatzResearch.WordTrace tailWord_7014858 prefixEnd_7014858 3601993877037220569514261 := by
  unfold tailWord_7014858
  simp only [CollatzResearch.WordTrace]
  refine ⟨63963222605093745802621307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170568593613583322140323485 63963222605093745802621307)
  ·
    refine ⟨95944833907640618703931961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63963222605093745802621307 95944833907640618703931961)
    ·
      refine ⟨71958625430730464027948971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95944833907640618703931961 71958625430730464027948971)
      ·
        refine ⟨107937938146095696041923457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71958625430730464027948971 107937938146095696041923457)
        ·
          refine ⟨80953453609571772031442593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107937938146095696041923457 80953453609571772031442593)
          ·
            refine ⟨60715090207178829023581945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80953453609571772031442593 60715090207178829023581945)
            ·
              refine ⟨45536317655384121767686459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60715090207178829023581945 45536317655384121767686459)
              ·
                refine ⟨68304476483076182651529689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45536317655384121767686459 68304476483076182651529689)
                ·
                  refine ⟨51228357362307136988647267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68304476483076182651529689 51228357362307136988647267)
                  ·
                    refine ⟨76842536043460705482970901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51228357362307136988647267 76842536043460705482970901)
                    ·
                      refine ⟨3601993877037220569514261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76842536043460705482970901 3601993877037220569514261)
                      ·
                        rfl

theorem cell23_7014858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_7014858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014858 prefixEnd_7014858 := by exact prefixLift 7014858
  have htrace : WordTrace (prefixWord ++ tailWord_7014858) baseStart_7014858 baseEnd_7014858 := by
    simpa [prefixWord, tailWord_7014858, baseEnd_7014858] using wordTrace_append hprefix tailTrace_7014858
  have hstable : (prefixWord ++ tailWord_7014858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014858).length < 2 ^ (prefixWord ++ tailWord_7014858).sum := by decide
  have hdescent : baseEnd_7014858 < baseStart_7014858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014908 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_7014908 : Nat := 118140960795 + 7014908 * 2 ^ 59
def prefixEnd_7014908 : Nat := 4983230072969 + 3 ^ 40 * 7014908 * 2
def baseEnd_7014908 : Nat := 3602019551069945373889031

theorem tailTrace_7014908 : CollatzResearch.WordTrace tailWord_7014908 prefixEnd_7014908 3602019551069945373889031 := by
  unfold tailWord_7014908
  simp only [CollatzResearch.WordTrace]
  refine ⟨127927357035096920874902689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170569809380129227833203585 127927357035096920874902689)
  ·
    refine ⟨95945517776322690656177017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127927357035096920874902689 95945517776322690656177017)
    ·
      refine ⟨71959138332242017992132763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95945517776322690656177017 71959138332242017992132763)
      ·
        refine ⟨107938707498363026988199145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71959138332242017992132763 107938707498363026988199145)
        ·
          refine ⟨80954030623772270241149359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107938707498363026988199145 80954030623772270241149359)
          ·
            refine ⟨121431045935658405361724039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80954030623772270241149359 121431045935658405361724039)
            ·
              refine ⟨182146568903487608042586059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121431045935658405361724039 182146568903487608042586059)
              ·
                refine ⟨273219853355231412063879089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182146568903487608042586059 273219853355231412063879089)
                ·
                  refine ⟨204914890016423559047909317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273219853355231412063879089 204914890016423559047909317)
                  ·
                    refine ⟨38421541878079417321482997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204914890016423559047909317 38421541878079417321482997)
                    ·
                      refine ⟨3602019551069945373889031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38421541878079417321482997 3602019551069945373889031)
                      ·
                        rfl

theorem cell23_7014908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_7014908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014908 prefixEnd_7014908 := by exact prefixLift 7014908
  have htrace : WordTrace (prefixWord ++ tailWord_7014908) baseStart_7014908 baseEnd_7014908 := by
    simpa [prefixWord, tailWord_7014908, baseEnd_7014908] using wordTrace_append hprefix tailTrace_7014908
  have hstable : (prefixWord ++ tailWord_7014908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014908).length < 2 ^ (prefixWord ++ tailWord_7014908).sum := by decide
  have hdescent : baseEnd_7014908 < baseStart_7014908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014915 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 1, 5]
def baseStart_7014915 : Nat := 118140960795 + 7014915 * 2 ^ 59
def prefixEnd_7014915 : Nat := 4983230072969 + 3 ^ 40 * 7014915 * 2
def baseEnd_7014915 : Nat := 1200674381811508948833833

theorem tailTrace_7014915 : CollatzResearch.WordTrace tailWord_7014915 prefixEnd_7014915 1200674381811508948833833 := by
  unfold tailWord_7014915
  simp only [CollatzResearch.WordTrace]
  refine ⟨255854969381168481945310199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170569979587445654630206799 255854969381168481945310199)
  ·
    refine ⟨383782454071752722917965299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255854969381168481945310199 383782454071752722917965299)
    ·
      refine ⟨575673681107629084376947949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383782454071752722917965299 575673681107629084376947949)
      ·
        refine ⟨215877630415360906641355481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575673681107629084376947949 215877630415360906641355481)
        ·
          refine ⟨161908222811520679981016611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215877630415360906641355481 161908222811520679981016611)
          ·
            refine ⟨242862334217281019971524917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161908222811520679981016611 242862334217281019971524917)
            ·
              refine ⟨22768343832870095622330461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242862334217281019971524917 22768343832870095622330461)
              ·
                refine ⟨8538128937326285858373923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22768343832870095622330461 8538128937326285858373923)
                ·
                  refine ⟨12807193405989428787560885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8538128937326285858373923 12807193405989428787560885)
                  ·
                    refine ⟨1200674381811508948833833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12807193405989428787560885 1200674381811508948833833)
                    ·
                      rfl

theorem cell23_7014915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 5].length) (baseStart_7014915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014915 prefixEnd_7014915 := by exact prefixLift 7014915
  have htrace : WordTrace (prefixWord ++ tailWord_7014915) baseStart_7014915 baseEnd_7014915 := by
    simpa [prefixWord, tailWord_7014915, baseEnd_7014915] using wordTrace_append hprefix tailTrace_7014915
  have hstable : (prefixWord ++ tailWord_7014915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014915).length < 2 ^ (prefixWord ++ tailWord_7014915).sum := by decide
  have hdescent : baseEnd_7014915 < baseStart_7014915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014919 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 6]
def baseStart_7014919 : Nat := 118140960795 + 7014919 * 2 ^ 59
def prefixEnd_7014919 : Nat := 4983230072969 + 3 ^ 40 * 7014919 * 2
def baseEnd_7014919 : Nat := 400225022150793870094609

theorem tailTrace_7014919 : CollatzResearch.WordTrace tailWord_7014919 prefixEnd_7014919 400225022150793870094609 := by
  unfold tailWord_7014919
  simp only [CollatzResearch.WordTrace]
  refine ⟨255855115273153990628455811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170570076848769327085637207 255855115273153990628455811)
  ·
    refine ⟨383782672909730985942683717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255855115273153990628455811 383782672909730985942683717)
    ·
      refine ⟨71959251170574559864253197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383782672909730985942683717 71959251170574559864253197)
      ·
        refine ⟨26984719188965459949094949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71959251170574559864253197 26984719188965459949094949)
        ·
          refine ⟨5059634847931023740455303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26984719188965459949094949 5059634847931023740455303)
          ·
            refine ⟨7589452271896535610682955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059634847931023740455303 7589452271896535610682955)
            ·
              refine ⟨11384178407844803416024433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589452271896535610682955 11384178407844803416024433)
              ·
                refine ⟨8538133805883602562018325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11384178407844803416024433 8538133805883602562018325)
                ·
                  refine ⟨400225022150793870094609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8538133805883602562018325 400225022150793870094609)
                  ·
                    rfl

theorem cell23_7014919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 6].length) (baseStart_7014919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014919 prefixEnd_7014919 := by exact prefixLift 7014919
  have htrace : WordTrace (prefixWord ++ tailWord_7014919) baseStart_7014919 baseEnd_7014919 := by
    simpa [prefixWord, tailWord_7014919, baseEnd_7014919] using wordTrace_append hprefix tailTrace_7014919
  have hstable : (prefixWord ++ tailWord_7014919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014919).length < 2 ^ (prefixWord ++ tailWord_7014919).sum := by decide
  have hdescent : baseEnd_7014919 < baseStart_7014919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014922 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2]
def baseStart_7014922 : Nat := 118140960795 + 7014922 * 2 ^ 59
def prefixEnd_7014922 : Nat := 4983230072969 + 3 ^ 40 * 7014922 * 2
def baseEnd_7014922 : Nat := 3602026739799108319113967

theorem tailTrace_7014922 : CollatzResearch.WordTrace tailWord_7014922 prefixEnd_7014922 3602026739799108319113967 := by
  unfold tailWord_7014922
  simp only [CollatzResearch.WordTrace]
  refine ⟨63963806173035780535203755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170570149794762081427210013 63963806173035780535203755)
  ·
    refine ⟨95945709259553670802805633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63963806173035780535203755 95945709259553670802805633)
    ·
      refine ⟨71959281944665253102104225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95945709259553670802805633 71959281944665253102104225)
      ·
        refine ⟨53969461458498939826578169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71959281944665253102104225 53969461458498939826578169)
        ·
          refine ⟨40477096093874204869933627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53969461458498939826578169 40477096093874204869933627)
          ·
            refine ⟨60715644140811307304900441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40477096093874204869933627 60715644140811307304900441)
            ·
              refine ⟨45536733105608480478675331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60715644140811307304900441 45536733105608480478675331)
              ·
                refine ⟨68305099658412720718012997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45536733105608480478675331 68305099658412720718012997)
                ·
                  refine ⟨12807206185952385134627437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68305099658412720718012997 12807206185952385134627437)
                  ·
                    refine ⟨4802702319732144425485289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12807206185952385134627437 4802702319732144425485289)
                    ·
                      refine ⟨3602026739799108319113967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802702319732144425485289 3602026739799108319113967)
                      ·
                        rfl

theorem cell23_7014922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_7014922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014922 prefixEnd_7014922 := by exact prefixLift 7014922
  have htrace : WordTrace (prefixWord ++ tailWord_7014922) baseStart_7014922 baseEnd_7014922 := by
    simpa [prefixWord, tailWord_7014922, baseEnd_7014922] using wordTrace_append hprefix tailTrace_7014922
  have hstable : (prefixWord ++ tailWord_7014922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014922).length < 2 ^ (prefixWord ++ tailWord_7014922).sum := by decide
  have hdescent : baseEnd_7014922 < baseStart_7014922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014955 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 3]
def baseStart_7014955 : Nat := 118140960795 + 7014955 * 2 ^ 59
def prefixEnd_7014955 : Nat := 4983230072969 + 3 ^ 40 * 7014955 * 2
def baseEnd_7014955 : Nat := 3602043684660706690001315

theorem tailTrace_7014955 : CollatzResearch.WordTrace tailWord_7014955 prefixEnd_7014955 3602043684660706690001315 := by
  unfold tailWord_7014955
  simp only [CollatzResearch.WordTrace]
  refine ⟨255856428301023568776766319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170570952200682379184510879 255856428301023568776766319)
  ·
    refine ⟨383784642451535353165149479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255856428301023568776766319 383784642451535353165149479)
    ·
      refine ⟨575676963677303029747724219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383784642451535353165149479 575676963677303029747724219)
      ·
        refine ⟨863515445515954544621586329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575676963677303029747724219 863515445515954544621586329)
        ·
          refine ⟨647636584136965908466189747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863515445515954544621586329 647636584136965908466189747)
          ·
            refine ⟨971454876205448862699284621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647636584136965908466189747 971454876205448862699284621)
            ·
              refine ⟨364295578577043323512231733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 971454876205448862699284621 364295578577043323512231733)
              ·
                refine ⟨34152710491597811579271725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 364295578577043323512231733 34152710491597811579271725)
                ·
                  refine ⟨12807266434349179342226897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34152710491597811579271725 12807266434349179342226897)
                  ·
                    refine ⟨9605449825761884506670173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12807266434349179342226897 9605449825761884506670173)
                    ·
                      refine ⟨3602043684660706690001315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9605449825761884506670173 3602043684660706690001315)
                      ·
                        rfl

theorem cell23_7014955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 3].length) (baseStart_7014955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014955 prefixEnd_7014955 := by exact prefixLift 7014955
  have htrace : WordTrace (prefixWord ++ tailWord_7014955) baseStart_7014955 baseEnd_7014955 := by
    simpa [prefixWord, tailWord_7014955, baseEnd_7014955] using wordTrace_append hprefix tailTrace_7014955
  have hstable : (prefixWord ++ tailWord_7014955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014955).length < 2 ^ (prefixWord ++ tailWord_7014955).sum := by decide
  have hdescent : baseEnd_7014955 < baseStart_7014955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014957 : List Nat := [1, 5, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7014957 : Nat := 118140960795 + 7014957 * 2 ^ 59
def prefixEnd_7014957 : Nat := 4983230072969 + 3 ^ 40 * 7014957 * 2
def baseEnd_7014957 : Nat := 1200681570540671894058769

theorem tailTrace_7014957 : CollatzResearch.WordTrace tailWord_7014957 prefixEnd_7014957 1200681570540671894058769 := by
  unfold tailWord_7014957
  simp only [CollatzResearch.WordTrace]
  refine ⟨255856501247016323118339125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170571000831344215412226083 255856501247016323118339125)
  ·
    refine ⟨23986546991907780292344293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255856501247016323118339125 23986546991907780292344293)
    ·
      refine ⟨4497477560982708804814555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23986546991907780292344293 4497477560982708804814555)
      ·
        refine ⟨6746216341474063207221833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497477560982708804814555 6746216341474063207221833)
        ·
          refine ⟨5059662256105547405416375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6746216341474063207221833 5059662256105547405416375)
          ·
            refine ⟨7589493384158321108124563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059662256105547405416375 7589493384158321108124563)
            ·
              refine ⟨11384240076237481662186845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589493384158321108124563 11384240076237481662186845)
              ·
                refine ⟨4269090028589055623320067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11384240076237481662186845 4269090028589055623320067)
                ·
                  refine ⟨6403635042883583434980101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269090028589055623320067 6403635042883583434980101)
                  ·
                    refine ⟨1200681570540671894058769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6403635042883583434980101 1200681570540671894058769)
                    ·
                      rfl

theorem cell23_7014957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7014957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014957 prefixEnd_7014957 := by exact prefixLift 7014957
  have htrace : WordTrace (prefixWord ++ tailWord_7014957) baseStart_7014957 baseEnd_7014957 := by
    simpa [prefixWord, tailWord_7014957, baseEnd_7014957] using wordTrace_append hprefix tailTrace_7014957
  have hstable : (prefixWord ++ tailWord_7014957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014957).length < 2 ^ (prefixWord ++ tailWord_7014957).sum := by decide
  have hdescent : baseEnd_7014957 < baseStart_7014957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014965 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_7014965 : Nat := 118140960795 + 7014965 * 2 ^ 59
def prefixEnd_7014965 : Nat := 4983230072969 + 3 ^ 40 * 7014965 * 2
def baseEnd_7014965 : Nat := 3602048819467251650876269

theorem tailTrace_7014965 : CollatzResearch.WordTrace tailWord_7014965 prefixEnd_7014965 3602048819467251650876269 := by
  unfold tailWord_7014965
  simp only [CollatzResearch.WordTrace]
  refine ⟨255856793030987340484630349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170571195353991560323086899 255856793030987340484630349)
  ·
    refine ⟨95946297386620252681736381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255856793030987340484630349 95946297386620252681736381)
    ·
      refine ⟨35979861519982594755651143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95946297386620252681736381 35979861519982594755651143)
      ·
        refine ⟨53969792279973892133476715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35979861519982594755651143 53969792279973892133476715)
        ·
          refine ⟨80954688419960838200215073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53969792279973892133476715 80954688419960838200215073)
          ·
            refine ⟨60716016314970628650161305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80954688419960838200215073 60716016314970628650161305)
            ·
              refine ⟨45537012236227971487620979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60716016314970628650161305 45537012236227971487620979)
              ·
                refine ⟨68305518354341957231431469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45537012236227971487620979 68305518354341957231431469)
                ·
                  refine ⟨25614569382878233961786801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68305518354341957231431469 25614569382878233961786801)
                  ·
                    refine ⟨19210927037158675471340101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25614569382878233961786801 19210927037158675471340101)
                    ·
                      refine ⟨3602048819467251650876269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19210927037158675471340101 3602048819467251650876269)
                      ·
                        rfl

theorem cell23_7014965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_7014965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014965 prefixEnd_7014965 := by exact prefixLift 7014965
  have htrace : WordTrace (prefixWord ++ tailWord_7014965) baseStart_7014965 baseEnd_7014965 := by
    simpa [prefixWord, tailWord_7014965, baseEnd_7014965] using wordTrace_append hprefix tailTrace_7014965
  have hstable : (prefixWord ++ tailWord_7014965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014965).length < 2 ^ (prefixWord ++ tailWord_7014965).sum := by decide
  have hdescent : baseEnd_7014965 < baseStart_7014965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014972 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_7014972 : Nat := 118140960795 + 7014972 * 2 ^ 59
def prefixEnd_7014972 : Nat := 4983230072969 + 3 ^ 40 * 7014972 * 2
def baseEnd_7014972 : Nat := 3602052413831833123488737

theorem tailTrace_7014972 : CollatzResearch.WordTrace tailWord_7014972 prefixEnd_7014972 3602052413831833123488737 := by
  unfold tailWord_7014972
  simp only [CollatzResearch.WordTrace]
  refine ⟨127928524170980990340067585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170571365561307987120090113 127928524170980990340067585)
  ·
    refine ⟨95946393128235742755050689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127928524170980990340067585 95946393128235742755050689)
    ·
      refine ⟨71959794846176807066288017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95946393128235742755050689 71959794846176807066288017)
      ·
        refine ⟨53969846134632605299716013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71959794846176807066288017 53969846134632605299716013)
        ·
          refine ⟨20238692300487226987393505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53969846134632605299716013 20238692300487226987393505)
          ·
            refine ⟨15179019225365420240545129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20238692300487226987393505 15179019225365420240545129)
            ·
              refine ⟨11384264419024065180408847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15179019225365420240545129 11384264419024065180408847)
              ·
                refine ⟨17076396628536097770613271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11384264419024065180408847 17076396628536097770613271)
                ·
                  refine ⟨25614594942804146655919907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17076396628536097770613271 25614594942804146655919907)
                  ·
                    refine ⟨38421892414206219983879861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25614594942804146655919907 38421892414206219983879861)
                    ·
                      refine ⟨3602052413831833123488737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38421892414206219983879861 3602052413831833123488737)
                      ·
                        rfl

theorem cell23_7014972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_7014972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014972 prefixEnd_7014972 := by exact prefixLift 7014972
  have htrace : WordTrace (prefixWord ++ tailWord_7014972) baseStart_7014972 baseEnd_7014972 := by
    simpa [prefixWord, tailWord_7014972, baseEnd_7014972] using wordTrace_append hprefix tailTrace_7014972
  have hstable : (prefixWord ++ tailWord_7014972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014972).length < 2 ^ (prefixWord ++ tailWord_7014972).sum := by decide
  have hdescent : baseEnd_7014972 < baseStart_7014972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014980 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7014980 : Nat := 118140960795 + 7014980 * 2 ^ 59
def prefixEnd_7014980 : Nat := 4983230072969 + 3 ^ 40 * 7014980 * 2
def baseEnd_7014980 : Nat := 3602056521677069092188701

theorem tailTrace_7014980 : CollatzResearch.WordTrace tailWord_7014980 prefixEnd_7014980 3602056521677069092188701 := by
  unfold tailWord_7014980
  simp only [CollatzResearch.WordTrace]
  refine ⟨127928670062966499023213197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170571560083955332030950929 127928670062966499023213197)
  ·
    refine ⟨47973251273612437133704949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127928670062966499023213197 47973251273612437133704949)
    ·
      refine ⟨4497492306901165981284839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47973251273612437133704949 4497492306901165981284839)
      ·
        refine ⟨6746238460351748971927259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497492306901165981284839 6746238460351748971927259)
        ·
          refine ⟨10119357690527623457890889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746238460351748971927259 10119357690527623457890889)
          ·
            refine ⟨7589518267895717593418167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10119357690527623457890889 7589518267895717593418167)
            ·
              refine ⟨11384277401843576390127251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589518267895717593418167 11384277401843576390127251)
              ·
                refine ⟨17076416102765364585190877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11384277401843576390127251 17076416102765364585190877)
                ·
                  refine ⟨6403656038537011719446579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17076416102765364585190877 6403656038537011719446579)
                  ·
                    refine ⟨9605484057805517579169869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6403656038537011719446579 9605484057805517579169869)
                    ·
                      refine ⟨3602056521677069092188701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9605484057805517579169869 3602056521677069092188701)
                      ·
                        rfl

theorem cell23_7014980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7014980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014980 prefixEnd_7014980 := by exact prefixLift 7014980
  have htrace : WordTrace (prefixWord ++ tailWord_7014980) baseStart_7014980 baseEnd_7014980 := by
    simpa [prefixWord, tailWord_7014980, baseEnd_7014980] using wordTrace_append hprefix tailTrace_7014980
  have hstable : (prefixWord ++ tailWord_7014980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014980).length < 2 ^ (prefixWord ++ tailWord_7014980).sum := by decide
  have hdescent : baseEnd_7014980 < baseStart_7014980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014986 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2]
def baseStart_7014986 : Nat := 118140960795 + 7014986 * 2 ^ 59
def prefixEnd_7014986 : Nat := 4983230072969 + 3 ^ 40 * 7014986 * 2
def baseEnd_7014986 : Nat := 3602059602560996068713673

theorem tailTrace_7014986 : CollatzResearch.WordTrace tailWord_7014986 prefixEnd_7014986 3602059602560996068713673 := by
  unfold tailWord_7014986
  simp only [CollatzResearch.WordTrace]
  refine ⟨63964389740977815267786203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170571705975940840714096541 63964389740977815267786203)
  ·
    refine ⟨95946584611466722901679305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63964389740977815267786203 95946584611466722901679305)
    ·
      refine ⟨71959938458600042176259479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95946584611466722901679305 71959938458600042176259479)
      ·
        refine ⟨107939907687900063264389219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71959938458600042176259479 107939907687900063264389219)
        ·
          refine ⟨161909861531850094896583829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107939907687900063264389219 161909861531850094896583829)
          ·
            refine ⟨7589524759305473198277367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161909861531850094896583829 7589524759305473198277367)
            ·
              refine ⟨11384287138958209797416051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589524759305473198277367 11384287138958209797416051)
              ·
                refine ⟨17076430708437314696124077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11384287138958209797416051 17076430708437314696124077)
                ·
                  refine ⟨6403661515663993011046529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17076430708437314696124077 6403661515663993011046529)
                  ·
                    refine ⟨4802746136747994758284897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6403661515663993011046529 4802746136747994758284897)
                    ·
                      refine ⟨3602059602560996068713673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802746136747994758284897 3602059602560996068713673)
                      ·
                        rfl

theorem cell23_7014986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_7014986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014986 prefixEnd_7014986 := by exact prefixLift 7014986
  have htrace : WordTrace (prefixWord ++ tailWord_7014986) baseStart_7014986 baseEnd_7014986 := by
    simpa [prefixWord, tailWord_7014986, baseEnd_7014986] using wordTrace_append hprefix tailTrace_7014986
  have hstable : (prefixWord ++ tailWord_7014986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014986).length < 2 ^ (prefixWord ++ tailWord_7014986).sum := by decide
  have hdescent : baseEnd_7014986 < baseStart_7014986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014996 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_7014996 : Nat := 118140960795 + 7014996 * 2 ^ 59
def prefixEnd_7014996 : Nat := 4983230072969 + 3 ^ 40 * 7014996 * 2
def baseEnd_7014996 : Nat := 1200688245789180343196209

theorem tailTrace_7014996 : CollatzResearch.WordTrace tailWord_7014996 prefixEnd_7014996 1200688245789180343196209 := by
  unfold tailWord_7014996
  simp only [CollatzResearch.WordTrace]
  refine ⟨127928961846937516389504421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170571949129250021852672561 127928961846937516389504421)
  ·
    refine ⟨23986680346300784323032079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127928961846937516389504421 23986680346300784323032079)
    ·
      refine ⟨35980020519451176484548119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23986680346300784323032079 35980020519451176484548119)
      ·
        refine ⟨53970030779176764726822179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35980020519451176484548119 53970030779176764726822179)
        ·
          refine ⟨80955046168765147090233269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53970030779176764726822179 80955046168765147090233269)
          ·
            refine ⟨7589535578321732539709369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80955046168765147090233269 7589535578321732539709369)
            ·
              refine ⟨5692151683741299404782027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7589535578321732539709369 5692151683741299404782027)
              ·
                refine ⟨8538227525611949107173041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5692151683741299404782027 8538227525611949107173041)
                ·
                  refine ⟨6403670644208961830379781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8538227525611949107173041 6403670644208961830379781)
                  ·
                    refine ⟨1200688245789180343196209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6403670644208961830379781 1200688245789180343196209)
                    ·
                      rfl

theorem cell23_7014996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_7014996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014996 prefixEnd_7014996 := by exact prefixLift 7014996
  have htrace : WordTrace (prefixWord ++ tailWord_7014996) baseStart_7014996 baseEnd_7014996 := by
    simpa [prefixWord, tailWord_7014996, baseEnd_7014996] using wordTrace_append hprefix tailTrace_7014996
  have hstable : (prefixWord ++ tailWord_7014996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014996).length < 2 ^ (prefixWord ++ tailWord_7014996).sum := by decide
  have hdescent : baseEnd_7014996 < baseStart_7014996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015037 : List Nat := [1, 4, 1, 1, 6, 1, 2, 2, 1, 2, 2]
def baseStart_7015037 : Nat := 118140960795 + 7015037 * 2 ^ 59
def prefixEnd_7015037 : Nat := 4983230072969 + 3 ^ 40 * 7015037 * 2
def baseEnd_7015037 : Nat := 3602085790074375369175939

theorem tailTrace_7015037 : CollatzResearch.WordTrace tailWord_7015037 prefixEnd_7015037 3602085790074375369175939 := by
  unfold tailWord_7015037
  simp only [CollatzResearch.WordTrace]
  refine ⟨255859419086726496781251365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170572946057817664520834243 255859419086726496781251365)
  ·
    refine ⟨47973641078761218146484631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255859419086726496781251365 47973641078761218146484631)
    ·
      refine ⟨71960461618141827219726947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47973641078761218146484631 71960461618141827219726947)
      ·
        refine ⟨107940692427212740829590421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71960461618141827219726947 107940692427212740829590421)
        ·
          refine ⟨5059719957525597226387051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107940692427212740829590421 5059719957525597226387051)
          ·
            refine ⟨7589579936288395839580577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059719957525597226387051 7589579936288395839580577)
            ·
              refine ⟨5692184952216296879685433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7589579936288395839580577 5692184952216296879685433)
              ·
                refine ⟨4269138714162222659764075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5692184952216296879685433 4269138714162222659764075)
                ·
                  refine ⟨6403708071243333989646113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269138714162222659764075 6403708071243333989646113)
                  ·
                    refine ⟨4802781053432500492234585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6403708071243333989646113 4802781053432500492234585)
                    ·
                      refine ⟨3602085790074375369175939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802781053432500492234585 3602085790074375369175939)
                      ·
                        rfl

theorem cell23_7015037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_7015037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015037 prefixEnd_7015037 := by exact prefixLift 7015037
  have htrace : WordTrace (prefixWord ++ tailWord_7015037) baseStart_7015037 baseEnd_7015037 := by
    simpa [prefixWord, tailWord_7015037, baseEnd_7015037] using wordTrace_append hprefix tailTrace_7015037
  have hstable : (prefixWord ++ tailWord_7015037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015037).length < 2 ^ (prefixWord ++ tailWord_7015037).sum := by decide
  have hdescent : baseEnd_7015037 < baseStart_7015037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015055 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_7015055 : Nat := 118140960795 + 7015055 * 2 ^ 59
def prefixEnd_7015055 : Nat := 4983230072969 + 3 ^ 40 * 7015055 * 2
def baseEnd_7015055 : Nat := 3602095032726156298750855

theorem tailTrace_7015055 : CollatzResearch.WordTrace tailWord_7015055 prefixEnd_7015055 3602095032726156298750855 := by
  unfold tailWord_7015055
  simp only [CollatzResearch.WordTrace]
  refine ⟨255860075600661285855406619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170573383733774190570271079 255860075600661285855406619)
  ·
    refine ⟨383790113400991928783109929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255860075600661285855406619 383790113400991928783109929)
    ·
      refine ⟨287842585050743946587332447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383790113400991928783109929 287842585050743946587332447)
      ·
        refine ⟨431763877576115919880998671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287842585050743946587332447 431763877576115919880998671)
        ·
          refine ⟨647645816364173879821498007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431763877576115919880998671 647645816364173879821498007)
          ·
            refine ⟨971468724546260819732247011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647645816364173879821498007 971468724546260819732247011)
            ·
              refine ⟨1457203086819391229598370517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971468724546260819732247011 1457203086819391229598370517)
              ·
                refine ⟨34153197347329481943711809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1457203086819391229598370517 34153197347329481943711809)
                ·
                  refine ⟨25614898010497111457783857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34153197347329481943711809 25614898010497111457783857)
                  ·
                    refine ⟨19211173507872833593337893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25614898010497111457783857 19211173507872833593337893)
                    ·
                      refine ⟨3602095032726156298750855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19211173507872833593337893 3602095032726156298750855)
                      ·
                        rfl

theorem cell23_7015055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_7015055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015055 prefixEnd_7015055 := by exact prefixLift 7015055
  have htrace : WordTrace (prefixWord ++ tailWord_7015055) baseStart_7015055 baseEnd_7015055 := by
    simpa [prefixWord, tailWord_7015055, baseEnd_7015055] using wordTrace_append hprefix tailTrace_7015055
  have hstable : (prefixWord ++ tailWord_7015055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015055).length < 2 ^ (prefixWord ++ tailWord_7015055).sum := by decide
  have hdescent : baseEnd_7015055 < baseStart_7015055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015065 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 7]
def baseStart_7015065 : Nat := 118140960795 + 7015065 * 2 ^ 59
def prefixEnd_7015065 : Nat := 4983230072969 + 3 ^ 40 * 7015065 * 2
def baseEnd_7015065 : Nat := 400233351948077917736201

theorem tailTrace_7015065 : CollatzResearch.WordTrace tailWord_7015065 prefixEnd_7015065 400233351948077917736201 := by
  unfold tailWord_7015065
  simp only [CollatzResearch.WordTrace]
  refine ⟨255860440330625057563270649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170573626887083371708847099 255860440330625057563270649)
  ·
    refine ⟨191895330247968793172452987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255860440330625057563270649 191895330247968793172452987)
    ·
      refine ⟨287842995371953189758679481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191895330247968793172452987 287842995371953189758679481)
      ·
        refine ⟨215882246528964892319009611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287842995371953189758679481 215882246528964892319009611)
        ·
          refine ⟨323823369793447338478514417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215882246528964892319009611 323823369793447338478514417)
          ·
            refine ⟨242867527345085503858885813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323823369793447338478514417 242867527345085503858885813)
            ·
              refine ⟨22768830688601765986770545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242867527345085503858885813 22768830688601765986770545)
              ·
                refine ⟨17076623016451324490077909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22768830688601765986770545 17076623016451324490077909)
                ·
                  refine ⟨400233351948077917736201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17076623016451324490077909 400233351948077917736201)
                  ·
                    rfl

theorem cell23_7015065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 7].length) (baseStart_7015065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015065 prefixEnd_7015065 := by exact prefixLift 7015065
  have htrace : WordTrace (prefixWord ++ tailWord_7015065) baseStart_7015065 baseEnd_7015065 := by
    simpa [prefixWord, tailWord_7015065, baseEnd_7015065] using wordTrace_append hprefix tailTrace_7015065
  have hstable : (prefixWord ++ tailWord_7015065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015065).length < 2 ^ (prefixWord ++ tailWord_7015065).sum := by decide
  have hdescent : baseEnd_7015065 < baseStart_7015065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015093 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_7015093 : Nat := 118140960795 + 7015093 * 2 ^ 59
def prefixEnd_7015093 : Nat := 4983230072969 + 3 ^ 40 * 7015093 * 2
def baseEnd_7015093 : Nat := 3602114544991027150075681

theorem tailTrace_7015093 : CollatzResearch.WordTrace tailWord_7015093 prefixEnd_7015093 3602114544991027150075681 := by
  unfold tailWord_7015093
  simp only [CollatzResearch.WordTrace]
  refine ⟨255861461574523618345289933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170574307716349078896859955 255861461574523618345289933)
  ·
    refine ⟨95948048090446356879483725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255861461574523618345289933 95948048090446356879483725)
    ·
      refine ⟨35980518033917383829806397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95948048090446356879483725 35980518033917383829806397)
      ·
        refine ⟨13492694262719018936177399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35980518033917383829806397 13492694262719018936177399)
        ·
          refine ⟨20239041394078528404266099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13492694262719018936177399 20239041394078528404266099)
          ·
            refine ⟨30358562091117792606399149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20239041394078528404266099 30358562091117792606399149)
            ·
              refine ⟨11384460784169172227399681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30358562091117792606399149 11384460784169172227399681)
              ·
                refine ⟨8538345588126879170549761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11384460784169172227399681 8538345588126879170549761)
                ·
                  refine ⟨6403759191095159377912321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8538345588126879170549761 6403759191095159377912321)
                  ·
                    refine ⟨4802819393321369533434241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6403759191095159377912321 4802819393321369533434241)
                    ·
                      refine ⟨3602114544991027150075681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802819393321369533434241 3602114544991027150075681)
                      ·
                        rfl

theorem cell23_7015093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_7015093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015093 prefixEnd_7015093 := by exact prefixLift 7015093
  have htrace : WordTrace (prefixWord ++ tailWord_7015093) baseStart_7015093 baseEnd_7015093 := by
    simpa [prefixWord, tailWord_7015093, baseEnd_7015093] using wordTrace_append hprefix tailTrace_7015093
  have hstable : (prefixWord ++ tailWord_7015093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015093).length < 2 ^ (prefixWord ++ tailWord_7015093).sum := by decide
  have hdescent : baseEnd_7015093 < baseStart_7015093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015145 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_7015145 : Nat := 118140960795 + 7015145 * 2 ^ 59
def prefixEnd_7015145 : Nat := 4983230072969 + 3 ^ 40 * 7015145 * 2
def baseEnd_7015145 : Nat := 3602141245985060946625441

theorem tailTrace_7015145 : CollatzResearch.WordTrace tailWord_7015145 prefixEnd_7015145 3602141245985060946625441 := by
  unfold tailWord_7015145
  simp only [CollatzResearch.WordTrace]
  refine ⟨255863358170335231226182889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170575572113556820817455259 255863358170335231226182889)
  ·
    refine ⟨191897518627751423419637167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255863358170335231226182889 191897518627751423419637167)
    ·
      refine ⟨287846277941627135129455751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191897518627751423419637167 287846277941627135129455751)
      ·
        refine ⟨431769416912440702694183627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287846277941627135129455751 431769416912440702694183627)
        ·
          refine ⟨647654125368661054041275441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431769416912440702694183627 647654125368661054041275441)
          ·
            refine ⟨485740594026495790530956581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647654125368661054041275441 485740594026495790530956581)
            ·
              refine ⟨91076361379967960724554359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 485740594026495790530956581 91076361379967960724554359)
              ·
                refine ⟨136614542069951941086831539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91076361379967960724554359 136614542069951941086831539)
                ·
                  refine ⟨204921813104927911630247309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136614542069951941086831539 204921813104927911630247309)
                  ·
                    refine ⟨76845679914347966861342741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204921813104927911630247309 76845679914347966861342741)
                    ·
                      refine ⟨3602141245985060946625441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76845679914347966861342741 3602141245985060946625441)
                      ·
                        rfl

theorem cell23_7015145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_7015145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015145 prefixEnd_7015145 := by exact prefixLift 7015145
  have htrace : WordTrace (prefixWord ++ tailWord_7015145) baseStart_7015145 baseEnd_7015145 := by
    simpa [prefixWord, tailWord_7015145, baseEnd_7015145] using wordTrace_append hprefix tailTrace_7015145
  have hstable : (prefixWord ++ tailWord_7015145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015145).length < 2 ^ (prefixWord ++ tailWord_7015145).sum := by decide
  have hdescent : baseEnd_7015145 < baseStart_7015145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015149 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7015149 : Nat := 118140960795 + 7015149 * 2 ^ 59
def prefixEnd_7015149 : Nat := 4983230072969 + 3 ^ 40 * 7015149 * 2
def baseEnd_7015149 : Nat := 3602143299907678930975423

theorem tailTrace_7015149 : CollatzResearch.WordTrace tailWord_7015149 prefixEnd_7015149 3602143299907678930975423 := by
  unfold tailWord_7015149
  simp only [CollatzResearch.WordTrace]
  refine ⟨255863504062320739909328501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170575669374880493272885667 255863504062320739909328501)
  ·
    refine ⟨23987203505842569366499547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255863504062320739909328501 23987203505842569366499547)
    ·
      refine ⟨35980805258763854049749321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23987203505842569366499547 35980805258763854049749321)
      ·
        refine ⟨26985603944072890537311991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35980805258763854049749321 26985603944072890537311991)
        ·
          refine ⟨40478405916109335805967987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26985603944072890537311991 40478405916109335805967987)
          ·
            refine ⟨60717608874164003708951981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40478405916109335805967987 60717608874164003708951981)
            ·
              refine ⟨22769103327811501390856993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60717608874164003708951981 22769103327811501390856993)
              ·
                refine ⟨17076827495858626043142745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22769103327811501390856993 17076827495858626043142745)
                ·
                  refine ⟨12807620621893969532357059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17076827495858626043142745 12807620621893969532357059)
                  ·
                    refine ⟨19211430932840954298535589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12807620621893969532357059 19211430932840954298535589)
                    ·
                      refine ⟨3602143299907678930975423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19211430932840954298535589 3602143299907678930975423)
                      ·
                        rfl

theorem cell23_7015149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7015149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015149 prefixEnd_7015149 := by exact prefixLift 7015149
  have htrace : WordTrace (prefixWord ++ tailWord_7015149) baseStart_7015149 baseEnd_7015149 := by
    simpa [prefixWord, tailWord_7015149, baseEnd_7015149] using wordTrace_append hprefix tailTrace_7015149
  have hstable : (prefixWord ++ tailWord_7015149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015149).length < 2 ^ (prefixWord ++ tailWord_7015149).sum := by decide
  have hdescent : baseEnd_7015149 < baseStart_7015149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015210 : List Nat := [3, 1, 4, 3, 1, 1, 1, 4, 1, 4]
def baseStart_7015210 : Nat := 118140960795 + 7015210 * 2 ^ 59
def prefixEnd_7015210 : Nat := 4983230072969 + 3 ^ 40 * 7015210 * 2
def baseEnd_7015210 : Nat := 1200724874075867730770881

theorem tailTrace_7015210 : CollatzResearch.WordTrace tailWord_7015210 prefixEnd_7015210 1200724874075867730770881 := by
  unfold tailWord_7015210
  simp only [CollatzResearch.WordTrace]
  refine ⟨63966432228774936831824771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170577152610066498218199389 63966432228774936831824771)
  ·
    refine ⟨95949648343162405247737157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63966432228774936831824771 95949648343162405247737157)
    ·
      refine ⟨17990559064342950983950717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95949648343162405247737157 17990559064342950983950717)
      ·
        refine ⟨6746459649128606618981519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17990559064342950983950717 6746459649128606618981519)
        ·
          refine ⟨10119689473692909928472279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746459649128606618981519 10119689473692909928472279)
          ·
            refine ⟨15179534210539364892708419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10119689473692909928472279 15179534210539364892708419)
            ·
              refine ⟨22769301315809047339062629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15179534210539364892708419 22769301315809047339062629)
              ·
                refine ⟨4269243996714196376074243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22769301315809047339062629 4269243996714196376074243)
                ·
                  refine ⟨6403865995071294564111365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269243996714196376074243 6403865995071294564111365)
                  ·
                    refine ⟨1200724874075867730770881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6403865995071294564111365 1200724874075867730770881)
                    ·
                      rfl

theorem cell23_7015210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_7015210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015210 prefixEnd_7015210 := by exact prefixLift 7015210
  have htrace : WordTrace (prefixWord ++ tailWord_7015210) baseStart_7015210 baseEnd_7015210 := by
    simpa [prefixWord, tailWord_7015210, baseEnd_7015210] using wordTrace_append hprefix tailTrace_7015210
  have hstable : (prefixWord ++ tailWord_7015210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015210).length < 2 ^ (prefixWord ++ tailWord_7015210).sum := by decide
  have hdescent : baseEnd_7015210 < baseStart_7015210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015239 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_7015239 : Nat := 118140960795 + 7015239 * 2 ^ 59
def prefixEnd_7015239 : Nat := 4983230072969 + 3 ^ 40 * 7015239 * 2
def baseEnd_7015239 : Nat := 3602189513166583578850009

theorem tailTrace_7015239 : CollatzResearch.WordTrace tailWord_7015239 prefixEnd_7015239 3602189513166583578850009 := by
  unfold tailWord_7015239
  simp only [CollatzResearch.WordTrace]
  refine ⟨255866786631994685280104771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170577857754663123520069847 255866786631994685280104771)
  ·
    refine ⟨383800179947992027920157157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255866786631994685280104771 383800179947992027920157157)
    ·
      refine ⟨71962533740248505235029467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383800179947992027920157157 71962533740248505235029467)
      ·
        refine ⟨107943800610372757852544201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71962533740248505235029467 107943800610372757852544201)
        ·
          refine ⟨80957850457779568389408151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107943800610372757852544201 80957850457779568389408151)
          ·
            refine ⟨121436775686669352584112227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80957850457779568389408151 121436775686669352584112227)
            ·
              refine ⟨182155163530004028876168341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121436775686669352584112227 182155163530004028876168341)
              ·
                refine ⟨8538523290468938853570391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182155163530004028876168341 8538523290468938853570391)
                ·
                  refine ⟨12807784935703408280355587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8538523290468938853570391 12807784935703408280355587)
                  ·
                    refine ⟨19211677403555112420533381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12807784935703408280355587 19211677403555112420533381)
                    ·
                      refine ⟨3602189513166583578850009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19211677403555112420533381 3602189513166583578850009)
                      ·
                        rfl

theorem cell23_7015239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_7015239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015239 prefixEnd_7015239 := by exact prefixLift 7015239
  have htrace : WordTrace (prefixWord ++ tailWord_7015239) baseStart_7015239 baseEnd_7015239 := by
    simpa [prefixWord, tailWord_7015239, baseEnd_7015239] using wordTrace_append hprefix tailTrace_7015239
  have hstable : (prefixWord ++ tailWord_7015239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015239).length < 2 ^ (prefixWord ++ tailWord_7015239).sum := by decide
  have hdescent : baseEnd_7015239 < baseStart_7015239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015242 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_7015242 : Nat := 118140960795 + 7015242 * 2 ^ 59
def prefixEnd_7015242 : Nat := 4983230072969 + 3 ^ 40 * 7015242 * 2
def baseEnd_7015242 : Nat := 3602191053608547067112495

theorem tailTrace_7015242 : CollatzResearch.WordTrace tailWord_7015242 prefixEnd_7015242 3602191053608547067112495 := by
  unfold tailWord_7015242
  simp only [CollatzResearch.WordTrace]
  refine ⟨63966724012745954198115995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170577930700655877861642653 63966724012745954198115995)
  ·
    refine ⟨95950086019118931297173993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63966724012745954198115995 95950086019118931297173993)
    ·
      refine ⟨71962564514339198472880495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95950086019118931297173993 71962564514339198472880495)
      ·
        refine ⟨107943846771508797709320743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71962564514339198472880495 107943846771508797709320743)
        ·
          refine ⟨161915770157263196563981115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107943846771508797709320743 161915770157263196563981115)
          ·
            refine ⟨242873655235894794845971673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161915770157263196563981115 242873655235894794845971673)
            ·
              refine ⟨182155241426921096134478755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242873655235894794845971673 182155241426921096134478755)
              ·
                refine ⟨273232862140381644201718133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182155241426921096134478755 273232862140381644201718133)
                ·
                  refine ⟨25615580825660779143911075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273232862140381644201718133 25615580825660779143911075)
                  ·
                    refine ⟨38423371238491168715866613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25615580825660779143911075 38423371238491168715866613)
                    ·
                      refine ⟨3602191053608547067112495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38423371238491168715866613 3602191053608547067112495)
                      ·
                        rfl

theorem cell23_7015242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_7015242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015242 prefixEnd_7015242 := by exact prefixLift 7015242
  have htrace : WordTrace (prefixWord ++ tailWord_7015242) baseStart_7015242 baseEnd_7015242 := by
    simpa [prefixWord, tailWord_7015242, baseEnd_7015242] using wordTrace_append hprefix tailTrace_7015242
  have hstable : (prefixWord ++ tailWord_7015242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015242).length < 2 ^ (prefixWord ++ tailWord_7015242).sum := by decide
  have hdescent : baseEnd_7015242 < baseStart_7015242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015286 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7015286 : Nat := 118140960795 + 7015286 * 2 ^ 59
def prefixEnd_7015286 : Nat := 4983230072969 + 3 ^ 40 * 7015286 * 2
def baseEnd_7015286 : Nat := 3602213646757344894962293

theorem tailTrace_7015286 : CollatzResearch.WordTrace tailWord_7015286 prefixEnd_7015286 3602213646757344894962293 := by
  unfold tailWord_7015286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15991781303926525769191607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170579000575216274871377141 15991781303926525769191607)
  ·
    refine ⟨23987671955889788653787411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15991781303926525769191607 23987671955889788653787411)
    ·
      refine ⟨35981507933834682980681117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23987671955889788653787411 35981507933834682980681117)
      ·
        refine ⟨13493065475188006117755419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35981507933834682980681117 13493065475188006117755419)
        ·
          refine ⟨20239598212782009176633129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493065475188006117755419 20239598212782009176633129)
          ·
            refine ⟨15179698659586506882474847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20239598212782009176633129 15179698659586506882474847)
            ·
              refine ⟨22769547989379760323712271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15179698659586506882474847 22769547989379760323712271)
              ·
                refine ⟨34154321984069640485568407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22769547989379760323712271 34154321984069640485568407)
                ·
                  refine ⟨51231482976104460728352611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34154321984069640485568407 51231482976104460728352611)
                  ·
                    refine ⟨76847224464156691092528917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51231482976104460728352611 76847224464156691092528917)
                    ·
                      refine ⟨3602213646757344894962293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76847224464156691092528917 3602213646757344894962293)
                      ·
                        rfl

theorem cell23_7015286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7015286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015286 prefixEnd_7015286 := by exact prefixLift 7015286
  have htrace : WordTrace (prefixWord ++ tailWord_7015286) baseStart_7015286 baseEnd_7015286 := by
    simpa [prefixWord, tailWord_7015286, baseEnd_7015286] using wordTrace_append hprefix tailTrace_7015286
  have hstable : (prefixWord ++ tailWord_7015286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015286).length < 2 ^ (prefixWord ++ tailWord_7015286).sum := by decide
  have hdescent : baseEnd_7015286 < baseStart_7015286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015292 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_7015292 : Nat := 118140960795 + 7015292 * 2 ^ 59
def prefixEnd_7015292 : Nat := 4983230072969 + 3 ^ 40 * 7015292 * 2
def baseEnd_7015292 : Nat := 1200738909213757290495755

theorem tailTrace_7015292 : CollatzResearch.WordTrace tailWord_7015292 prefixEnd_7015292 1200738909213757290495755 := by
  unfold tailWord_7015292
  simp only [CollatzResearch.WordTrace]
  refine ⟨127934359850401337665892065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170579146467201783554522753 127934359850401337665892065)
  ·
    refine ⟨95950769887801003249419049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127934359850401337665892065 95950769887801003249419049)
    ·
      refine ⟨71963077415850752437064287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95950769887801003249419049 71963077415850752437064287)
      ·
        refine ⟨107944616123776128655596431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71963077415850752437064287 107944616123776128655596431)
        ·
          refine ⟨161916924185664192983394647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107944616123776128655596431 161916924185664192983394647)
          ·
            refine ⟨242875386278496289475091971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161916924185664192983394647 242875386278496289475091971)
            ·
              refine ⟨364313079417744434212637957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242875386278496289475091971 364313079417744434212637957)
              ·
                refine ⟨68308702390827081414869617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364313079417744434212637957 68308702390827081414869617)
                ·
                  refine ⟨51231526793120311061152213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68308702390827081414869617 51231526793120311061152213)
                  ·
                    refine ⟨1200738909213757290495755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51231526793120311061152213 1200738909213757290495755)
                    ·
                      rfl

theorem cell23_7015292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_7015292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015292 prefixEnd_7015292 := by exact prefixLift 7015292
  have htrace : WordTrace (prefixWord ++ tailWord_7015292) baseStart_7015292 baseEnd_7015292 := by
    simpa [prefixWord, tailWord_7015292, baseEnd_7015292] using wordTrace_append hprefix tailTrace_7015292
  have hstable : (prefixWord ++ tailWord_7015292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015292).length < 2 ^ (prefixWord ++ tailWord_7015292).sum := by decide
  have hdescent : baseEnd_7015292 < baseStart_7015292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015324 : List Nat := [2, 2, 3, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_7015324 : Nat := 118140960795 + 7015324 * 2 ^ 59
def prefixEnd_7015324 : Nat := 4983230072969 + 3 ^ 40 * 7015324 * 2
def baseEnd_7015324 : Nat := 3602233159022215746287119

theorem tailTrace_7015324 : CollatzResearch.WordTrace tailWord_7015324 prefixEnd_7015324 3602233159022215746287119 := by
  unfold tailWord_7015324
  simp only [CollatzResearch.WordTrace]
  refine ⟨127934943418343372398474513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170579924557791163197966017 127934943418343372398474513)
  ·
    refine ⟨95951207563757529298855885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127934943418343372398474513 95951207563757529298855885)
    ·
      refine ⟨35981702836409073487070957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95951207563757529298855885 35981702836409073487070957)
      ·
        refine ⟨13493138563653402557651609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35981702836409073487070957 13493138563653402557651609)
        ·
          refine ⟨10119853922740051918238707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13493138563653402557651609 10119853922740051918238707)
          ·
            refine ⟨15179780884110077877358061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10119853922740051918238707 15179780884110077877358061)
            ·
              refine ⟨5692417831541279204009273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15179780884110077877358061 5692417831541279204009273)
              ·
                refine ⟨4269313373655959403006955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5692417831541279204009273 4269313373655959403006955)
                ·
                  refine ⟨6403970060483939104510433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269313373655959403006955 6403970060483939104510433)
                  ·
                    refine ⟨4802977545362954328382825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6403970060483939104510433 4802977545362954328382825)
                    ·
                      refine ⟨3602233159022215746287119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802977545362954328382825 3602233159022215746287119)
                      ·
                        rfl

theorem cell23_7015324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_7015324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015324 prefixEnd_7015324 := by exact prefixLift 7015324
  have htrace : WordTrace (prefixWord ++ tailWord_7015324) baseStart_7015324 baseEnd_7015324 := by
    simpa [prefixWord, tailWord_7015324, baseEnd_7015324] using wordTrace_append hprefix tailTrace_7015324
  have hstable : (prefixWord ++ tailWord_7015324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015324).length < 2 ^ (prefixWord ++ tailWord_7015324).sum := by decide
  have hdescent : baseEnd_7015324 < baseStart_7015324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015349 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_7015349 : Nat := 118140960795 + 7015349 * 2 ^ 59
def prefixEnd_7015349 : Nat := 4983230072969 + 3 ^ 40 * 7015349 * 2
def baseEnd_7015349 : Nat := 3602245996038578148474503

theorem tailTrace_7015349 : CollatzResearch.WordTrace tailWord_7015349 prefixEnd_7015349 3602245996038578148474503 := by
  unfold tailWord_7015349
  simp only [CollatzResearch.WordTrace]
  refine ⟨255870798661596174066609101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170580532441064116044406067 255870798661596174066609101)
  ·
    refine ⟨95951549498098565274978413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255870798661596174066609101 95951549498098565274978413)
    ·
      refine ⟨35981831061786961978116905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95951549498098565274978413 35981831061786961978116905)
      ·
        refine ⟨26986373296340221483587679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35981831061786961978116905 26986373296340221483587679)
        ·
          refine ⟨40479559944510332225381519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26986373296340221483587679 40479559944510332225381519)
          ·
            refine ⟨60719339916765498338072279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40479559944510332225381519 60719339916765498338072279)
            ·
              refine ⟨91079009875148247507108419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60719339916765498338072279 91079009875148247507108419)
              ·
                refine ⟨136618514812722371260662629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91079009875148247507108419 136618514812722371260662629)
                ·
                  refine ⟨25615971527385444611374243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136618514812722371260662629 25615971527385444611374243)
                  ·
                    refine ⟨38423957291078166917061365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25615971527385444611374243 38423957291078166917061365)
                    ·
                      refine ⟨3602245996038578148474503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38423957291078166917061365 3602245996038578148474503)
                      ·
                        rfl

theorem cell23_7015349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_7015349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015349 prefixEnd_7015349 := by exact prefixLift 7015349
  have htrace : WordTrace (prefixWord ++ tailWord_7015349) baseStart_7015349 baseEnd_7015349 := by
    simpa [prefixWord, tailWord_7015349, baseEnd_7015349] using wordTrace_append hprefix tailTrace_7015349
  have hstable : (prefixWord ++ tailWord_7015349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015349).length < 2 ^ (prefixWord ++ tailWord_7015349).sum := by decide
  have hdescent : baseEnd_7015349 < baseStart_7015349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015380 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_7015380 : Nat := 118140960795 + 7015380 * 2 ^ 59
def prefixEnd_7015380 : Nat := 4983230072969 + 3 ^ 40 * 7015380 * 2
def baseEnd_7015380 : Nat := 3602261913938867527186861

theorem tailTrace_7015380 : CollatzResearch.WordTrace tailWord_7015380 prefixEnd_7015380 3602261913938867527186861 := by
  unfold tailWord_7015380
  simp only [CollatzResearch.WordTrace]
  refine ⟨127935964662241933180493797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170581286216322577573991729 127935964662241933180493797)
  ·
    refine ⟨23987993374170362471342587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127935964662241933180493797 23987993374170362471342587)
    ·
      refine ⟨35981990061255543707013881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23987993374170362471342587 35981990061255543707013881)
      ·
        refine ⟨26986492545941657780260411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35981990061255543707013881 26986492545941657780260411)
        ·
          refine ⟨40479738818912486670390617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26986492545941657780260411 40479738818912486670390617)
          ·
            refine ⟨30359804114184365002792963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40479738818912486670390617 30359804114184365002792963)
            ·
              refine ⟨45539706171276547504189445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30359804114184365002792963 45539706171276547504189445)
              ·
                refine ⟨8538694907114352657035521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45539706171276547504189445 8538694907114352657035521)
                ·
                  refine ⟨6404021180335764492776641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8538694907114352657035521 6404021180335764492776641)
                  ·
                    refine ⟨4803015885251823369582481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6404021180335764492776641 4803015885251823369582481)
                    ·
                      refine ⟨3602261913938867527186861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803015885251823369582481 3602261913938867527186861)
                      ·
                        rfl

theorem cell23_7015380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_7015380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015380 prefixEnd_7015380 := by exact prefixLift 7015380
  have htrace : WordTrace (prefixWord ++ tailWord_7015380) baseStart_7015380 baseEnd_7015380 := by
    simpa [prefixWord, tailWord_7015380, baseEnd_7015380] using wordTrace_append hprefix tailTrace_7015380
  have hstable : (prefixWord ++ tailWord_7015380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015380).length < 2 ^ (prefixWord ++ tailWord_7015380).sum := by decide
  have hdescent : baseEnd_7015380 < baseStart_7015380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015439 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 3]
def baseStart_7015439 : Nat := 118140960795 + 7015439 * 2 ^ 59
def prefixEnd_7015439 : Nat := 4983230072969 + 3 ^ 40 * 7015439 * 2
def baseEnd_7015439 : Nat := 3602292209297482796349089

theorem tailTrace_7015439 : CollatzResearch.WordTrace tailWord_7015439 prefixEnd_7015439 3602292209297482796349089 := by
  unfold tailWord_7015439
  simp only [CollatzResearch.WordTrace]
  refine ⟨255874081231270119437385371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170582720820846746291590247 255874081231270119437385371)
  ·
    refine ⟨383811121846905179156078057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255874081231270119437385371 383811121846905179156078057)
    ·
      refine ⟨287858341385178884367058543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383811121846905179156078057 287858341385178884367058543)
      ·
        refine ⟨431787512077768326550587815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287858341385178884367058543 431787512077768326550587815)
        ·
          refine ⟨647681268116652489825881723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431787512077768326550587815 647681268116652489825881723)
          ·
            refine ⟨971521902174978734738822585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647681268116652489825881723 971521902174978734738822585)
            ·
              refine ⟨728641426631234051054116939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971521902174978734738822585 728641426631234051054116939)
              ·
                refine ⟨1092962139946851076581175409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728641426631234051054116939 1092962139946851076581175409)
                ·
                  refine ⟨819721604960138307435881557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092962139946851076581175409 819721604960138307435881557)
                  ·
                    refine ⟨9606112558126620790264237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 819721604960138307435881557 9606112558126620790264237)
                    ·
                      refine ⟨3602292209297482796349089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9606112558126620790264237 3602292209297482796349089)
                      ·
                        rfl

theorem cell23_7015439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 3].length) (baseStart_7015439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015439 prefixEnd_7015439 := by exact prefixLift 7015439
  have htrace : WordTrace (prefixWord ++ tailWord_7015439) baseStart_7015439 baseEnd_7015439 := by
    simpa [prefixWord, tailWord_7015439, baseEnd_7015439] using wordTrace_append hprefix tailTrace_7015439
  have hstable : (prefixWord ++ tailWord_7015439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015439).length < 2 ^ (prefixWord ++ tailWord_7015439).sum := by decide
  have hdescent : baseEnd_7015439 < baseStart_7015439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015480 : List Nat := [2, 1, 2, 1, 5, 1, 3, 3, 1, 4]
def baseStart_7015480 : Nat := 118140960795 + 7015480 * 2 ^ 59
def prefixEnd_7015480 : Nat := 4983230072969 + 3 ^ 40 * 7015480 * 2
def baseEnd_7015480 : Nat := 1200771087334772378645467

theorem tailTrace_7015480 : CollatzResearch.WordTrace tailWord_7015480 prefixEnd_7015480 1200771087334772378645467 := by
  unfold tailWord_7015480
  simp only [CollatzResearch.WordTrace]
  refine ⟨127937788312060791719813947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170583717749414388959751929 127937788312060791719813947)
  ·
    refine ⟨191906682468091187579720921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127937788312060791719813947 191906682468091187579720921)
    ·
      refine ⟨143930011851068390684790691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191906682468091187579720921 143930011851068390684790691)
      ·
        refine ⟨215895017776602586027186037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143930011851068390684790691 215895017776602586027186037)
        ·
          refine ⟨20240157916556492440048691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215895017776602586027186037 20240157916556492440048691)
          ·
            refine ⟨30360236874834738660073037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20240157916556492440048691 30360236874834738660073037)
            ·
              refine ⟨11385088828063026997527389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30360236874834738660073037 11385088828063026997527389)
              ·
                refine ⟨4269408310523635124072771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11385088828063026997527389 4269408310523635124072771)
                ·
                  refine ⟨6404112465785452686109157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269408310523635124072771 6404112465785452686109157)
                  ·
                    refine ⟨1200771087334772378645467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6404112465785452686109157 1200771087334772378645467)
                    ·
                      rfl

theorem cell23_7015480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_7015480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015480 prefixEnd_7015480 := by exact prefixLift 7015480
  have htrace : WordTrace (prefixWord ++ tailWord_7015480) baseStart_7015480 baseEnd_7015480 := by
    simpa [prefixWord, tailWord_7015480, baseEnd_7015480] using wordTrace_append hprefix tailTrace_7015480
  have hstable : (prefixWord ++ tailWord_7015480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015480).length < 2 ^ (prefixWord ++ tailWord_7015480).sum := by decide
  have hdescent : baseEnd_7015480 < baseStart_7015480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015530 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_7015530 : Nat := 118140960795 + 7015530 * 2 ^ 59
def prefixEnd_7015530 : Nat := 4983230072969 + 3 ^ 40 * 7015530 * 2
def baseEnd_7015530 : Nat := 3602338936037041940311171

theorem tailTrace_7015530 : CollatzResearch.WordTrace tailWord_7015530 prefixEnd_7015530 3602338936037041940311171 := by
  unfold tailWord_7015530
  simp only [CollatzResearch.WordTrace]
  refine ⟨63969350068485110494737011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170584933515960294652632029 63969350068485110494737011)
  ·
    refine ⟨95954025102727665742105517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63969350068485110494737011 95954025102727665742105517)
    ·
      refine ⟨35982759413522874653289569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95954025102727665742105517 35982759413522874653289569)
      ·
        refine ⟨26987069560142155989967177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35982759413522874653289569 26987069560142155989967177)
        ·
          refine ⟨20240302170106616992475383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26987069560142155989967177 20240302170106616992475383)
          ·
            refine ⟨30360453255159925488713075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20240302170106616992475383 30360453255159925488713075)
            ·
              refine ⟨45540679882739888233069613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30360453255159925488713075 45540679882739888233069613)
              ·
                refine ⟨17077754956027458087401105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45540679882739888233069613 17077754956027458087401105)
                ·
                  refine ⟨12808316217020593565550829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17077754956027458087401105 12808316217020593565550829)
                  ·
                    refine ⟨4803118581382722587081561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12808316217020593565550829 4803118581382722587081561)
                    ·
                      refine ⟨3602338936037041940311171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803118581382722587081561 3602338936037041940311171)
                      ·
                        rfl

theorem cell23_7015530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_7015530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015530 prefixEnd_7015530 := by exact prefixLift 7015530
  have htrace : WordTrace (prefixWord ++ tailWord_7015530) baseStart_7015530 baseEnd_7015530 := by
    simpa [prefixWord, tailWord_7015530, baseEnd_7015530] using wordTrace_append hprefix tailTrace_7015530
  have hstable : (prefixWord ++ tailWord_7015530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015530).length < 2 ^ (prefixWord ++ tailWord_7015530).sum := by decide
  have hdescent : baseEnd_7015530 < baseStart_7015530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015536 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 1, 6]
def baseStart_7015536 : Nat := 118140960795 + 7015536 * 2 ^ 59
def prefixEnd_7015536 : Nat := 4983230072969 + 3 ^ 40 * 7015536 * 2
def baseEnd_7015536 : Nat := 1200780672306989638945381

theorem tailTrace_7015536 : CollatzResearch.WordTrace tailWord_7015536 prefixEnd_7015536 1200780672306989638945381 := by
  unfold tailWord_7015536
  simp only [CollatzResearch.WordTrace]
  refine ⟨127938809555959352501833231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170585079407945803335777641 127938809555959352501833231)
  ·
    refine ⟨191908214333939028752749847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127938809555959352501833231 191908214333939028752749847)
    ·
      refine ⟨287862321500908543129124771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191908214333939028752749847 287862321500908543129124771)
      ·
        refine ⟨431793482251362814693687157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287862321500908543129124771 431793482251362814693687157)
        ·
          refine ⟨40480638961065263877533171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 431793482251362814693687157 40480638961065263877533171)
          ·
            refine ⟨60720958441597895816299757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40480638961065263877533171 60720958441597895816299757)
            ·
              refine ⟨22770359415599210931112409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60720958441597895816299757 22770359415599210931112409)
              ·
                refine ⟨17077769561699408198334307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22770359415599210931112409 17077769561699408198334307)
                ·
                  refine ⟨25616654342549112297501461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17077769561699408198334307 25616654342549112297501461)
                  ·
                    refine ⟨1200780672306989638945381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25616654342549112297501461 1200780672306989638945381)
                    ·
                      rfl

theorem cell23_7015536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_7015536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015536 prefixEnd_7015536 := by exact prefixLift 7015536
  have htrace : WordTrace (prefixWord ++ tailWord_7015536) baseStart_7015536 baseEnd_7015536 := by
    simpa [prefixWord, tailWord_7015536, baseEnd_7015536] using wordTrace_append hprefix tailTrace_7015536
  have hstable : (prefixWord ++ tailWord_7015536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015536).length < 2 ^ (prefixWord ++ tailWord_7015536).sum := by decide
  have hdescent : baseEnd_7015536 < baseStart_7015536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015539 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 6]
def baseStart_7015539 : Nat := 118140960795 + 7015539 * 2 ^ 59
def prefixEnd_7015539 : Nat := 4983230072969 + 3 ^ 40 * 7015539 * 2
def baseEnd_7015539 : Nat := 3602343557362932405098629

theorem tailTrace_7015539 : CollatzResearch.WordTrace tailWord_7015539 prefixEnd_7015539 3602343557362932405098629 := by
  unfold tailWord_7015539
  simp only [CollatzResearch.WordTrace]
  refine ⟨255877728530907836516025671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170585152353938557677350447 255877728530907836516025671)
  ·
    refine ⟨383816592796361754774038507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255877728530907836516025671 383816592796361754774038507)
    ·
      refine ⟨575724889194542632161057761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383816592796361754774038507 575724889194542632161057761)
      ·
        refine ⟨431793666895906974120793321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575724889194542632161057761 431793666895906974120793321)
        ·
          refine ⟨323845250171930230590594991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431793666895906974120793321 323845250171930230590594991)
          ·
            refine ⟨485767875257895345885892487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323845250171930230590594991 485767875257895345885892487)
            ·
              refine ⟨728651812886843018828838731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485767875257895345885892487 728651812886843018828838731)
              ·
                refine ⟨1092977719330264528243258097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728651812886843018828838731 1092977719330264528243258097)
                ·
                  refine ⟨819733289497698396182443573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092977719330264528243258097 819733289497698396182443573)
                  ·
                    refine ⟨76849995890409224642104085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 819733289497698396182443573 76849995890409224642104085)
                    ·
                      refine ⟨3602343557362932405098629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76849995890409224642104085 3602343557362932405098629)
                      ·
                        rfl

theorem cell23_7015539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_7015539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015539 prefixEnd_7015539 := by exact prefixLift 7015539
  have htrace : WordTrace (prefixWord ++ tailWord_7015539) baseStart_7015539 baseEnd_7015539 := by
    simpa [prefixWord, tailWord_7015539, baseEnd_7015539] using wordTrace_append hprefix tailTrace_7015539
  have hstable : (prefixWord ++ tailWord_7015539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015539).length < 2 ^ (prefixWord ++ tailWord_7015539).sum := by decide
  have hdescent : baseEnd_7015539 < baseStart_7015539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015570 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7015570 : Nat := 118140960795 + 7015570 * 2 ^ 59
def prefixEnd_7015570 : Nat := 4983230072969 + 3 ^ 40 * 7015570 * 2
def baseEnd_7015570 : Nat := 1200786491754407261270329

theorem tailTrace_7015570 : CollatzResearch.WordTrace tailWord_7015570 prefixEnd_7015570 1200786491754407261270329 := by
  unfold tailWord_7015570
  simp only [CollatzResearch.WordTrace]
  refine ⟨63969714798448882202601041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170585906129197019206936109 63969714798448882202601041)
  ·
    refine ⟨47977286098836661651950781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63969714798448882202601041 47977286098836661651950781)
    ·
      refine ⟨17991482287063748119481543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47977286098836661651950781 17991482287063748119481543)
      ·
        refine ⟨26987223430595622179222315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17991482287063748119481543 26987223430595622179222315)
        ·
          refine ⟨40480835145893433268833473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26987223430595622179222315 40480835145893433268833473)
          ·
            refine ⟨30360626359420074951625105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40480835145893433268833473 30360626359420074951625105)
            ·
              refine ⟨22770469769565056213718829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30360626359420074951625105 22770469769565056213718829)
              ·
                refine ⟨8538926163586896080144561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22770469769565056213718829 8538926163586896080144561)
                ·
                  refine ⟨6404194622690172060108421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8538926163586896080144561 6404194622690172060108421)
                  ·
                    refine ⟨1200786491754407261270329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6404194622690172060108421 1200786491754407261270329)
                    ·
                      rfl

theorem cell23_7015570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7015570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015570 prefixEnd_7015570 := by exact prefixLift 7015570
  have htrace : WordTrace (prefixWord ++ tailWord_7015570) baseStart_7015570 baseEnd_7015570 := by
    simpa [prefixWord, tailWord_7015570, baseEnd_7015570] using wordTrace_append hprefix tailTrace_7015570
  have hstable : (prefixWord ++ tailWord_7015570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015570).length < 2 ^ (prefixWord ++ tailWord_7015570).sum := by decide
  have hdescent : baseEnd_7015570 < baseStart_7015570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015594 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7015594 : Nat := 118140960795 + 7015594 * 2 ^ 59
def prefixEnd_7015594 : Nat := 4983230072969 + 3 ^ 40 * 7015594 * 2
def baseEnd_7015594 : Nat := 3602371798798929689910877

theorem tailTrace_7015594 : CollatzResearch.WordTrace tailWord_7015594 prefixEnd_7015594 3602371798798929689910877 := by
  unfold tailWord_7015594
  simp only [CollatzResearch.WordTrace]
  refine ⟨63969933636427145227319459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170586489697139053939518557 63969933636427145227319459)
  ·
    refine ⟨95954900454640717840979189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63969933636427145227319459 95954900454640717840979189)
    ·
      refine ⟨8995771917622567297591799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95954900454640717840979189 8995771917622567297591799)
      ·
        refine ⟨13493657876433850946387699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8995771917622567297591799 13493657876433850946387699)
        ·
          refine ⟨20240486814650776419581549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493657876433850946387699 20240486814650776419581549)
          ·
            refine ⟨7590182555494041157343081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20240486814650776419581549 7590182555494041157343081)
            ·
              refine ⟨5692636916620530868007311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7590182555494041157343081 5692636916620530868007311)
              ·
                refine ⟨8538955374930796302010967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5692636916620530868007311 8538955374930796302010967)
                ·
                  refine ⟨12808433062396194453016451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8538955374930796302010967 12808433062396194453016451)
                  ·
                    refine ⟨19212649593594291679524677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12808433062396194453016451 19212649593594291679524677)
                    ·
                      refine ⟨3602371798798929689910877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19212649593594291679524677 3602371798798929689910877)
                      ·
                        rfl

theorem cell23_7015594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7015594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015594 prefixEnd_7015594 := by exact prefixLift 7015594
  have htrace : WordTrace (prefixWord ++ tailWord_7015594) baseStart_7015594 baseEnd_7015594 := by
    simpa [prefixWord, tailWord_7015594, baseEnd_7015594] using wordTrace_append hprefix tailTrace_7015594
  have hstable : (prefixWord ++ tailWord_7015594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015594).length < 2 ^ (prefixWord ++ tailWord_7015594).sum := by decide
  have hdescent : baseEnd_7015594 < baseStart_7015594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015597 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_7015597 : Nat := 118140960795 + 7015597 * 2 ^ 59
def prefixEnd_7015597 : Nat := 4983230072969 + 3 ^ 40 * 7015597 * 2
def baseEnd_7015597 : Nat := 3602373339240893178173363

theorem tailTrace_7015597 : CollatzResearch.WordTrace tailWord_7015597 prefixEnd_7015597 3602373339240893178173363 := by
  unfold tailWord_7015597
  simp only [CollatzResearch.WordTrace]
  refine ⟨255879843964697712421637045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170586562643131808281091363 255879843964697712421637045)
  ·
    refine ⟨23988735371690410539528473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255879843964697712421637045 23988735371690410539528473)
    ·
      refine ⟨17991551528767807904646355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23988735371690410539528473 17991551528767807904646355)
      ·
        refine ⟨26987327293151711856969533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17991551528767807904646355 26987327293151711856969533)
        ·
          refine ⟨10120247734931891946363575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26987327293151711856969533 10120247734931891946363575)
          ·
            refine ⟨15180371602397837919545363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10120247734931891946363575 15180371602397837919545363)
            ·
              refine ⟨22770557403596756879318045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15180371602397837919545363 22770557403596756879318045)
              ·
                refine ⟨8538959026348783829744267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22770557403596756879318045 8538959026348783829744267)
                ·
                  refine ⟨12808438539523175744616401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8538959026348783829744267 12808438539523175744616401)
                  ·
                    refine ⟨9606328904642381808462301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12808438539523175744616401 9606328904642381808462301)
                    ·
                      refine ⟨3602373339240893178173363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9606328904642381808462301 3602373339240893178173363)
                      ·
                        rfl

theorem cell23_7015597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_7015597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015597 prefixEnd_7015597 := by exact prefixLift 7015597
  have htrace : WordTrace (prefixWord ++ tailWord_7015597) baseStart_7015597 baseEnd_7015597 := by
    simpa [prefixWord, tailWord_7015597, baseEnd_7015597] using wordTrace_append hprefix tailTrace_7015597
  have hstable : (prefixWord ++ tailWord_7015597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015597).length < 2 ^ (prefixWord ++ tailWord_7015597).sum := by decide
  have hdescent : baseEnd_7015597 < baseStart_7015597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015637 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 1, 3, 2]
def baseStart_7015637 : Nat := 118140960795 + 7015637 * 2 ^ 59
def prefixEnd_7015637 : Nat := 4983230072969 + 3 ^ 40 * 7015637 * 2
def baseEnd_7015637 : Nat := 3602393878467073021673179

theorem tailTrace_7015637 : CollatzResearch.WordTrace tailWord_7015637 prefixEnd_7015637 3602393878467073021673179 := by
  unfold tailWord_7015637
  simp only [CollatzResearch.WordTrace]
  refine ⟨255881302884552799253093165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170587535256368532835395443 255881302884552799253093165)
  ·
    refine ⟨95955488581707299719909937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255881302884552799253093165 95955488581707299719909937)
    ·
      refine ⟨71966616436280474789932453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95955488581707299719909937 71966616436280474789932453)
      ·
        refine ⟨13493740581802589023112335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71966616436280474789932453 13493740581802589023112335)
        ·
          refine ⟨20240610872703883534668503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493740581802589023112335 20240610872703883534668503)
          ·
            refine ⟨30360916309055825302002755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20240610872703883534668503 30360916309055825302002755)
            ·
              refine ⟨45541374463583737953004133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30360916309055825302002755 45541374463583737953004133)
              ·
                refine ⟨8539007711921950866188275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45541374463583737953004133 8539007711921950866188275)
                ·
                  refine ⟨12808511567882926299282413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8539007711921950866188275 12808511567882926299282413)
                  ·
                    refine ⟨4803191837956097362230905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12808511567882926299282413 4803191837956097362230905)
                    ·
                      refine ⟨3602393878467073021673179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803191837956097362230905 3602393878467073021673179)
                      ·
                        rfl

theorem cell23_7015637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_7015637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015637 prefixEnd_7015637 := by exact prefixLift 7015637
  have htrace : WordTrace (prefixWord ++ tailWord_7015637) baseStart_7015637 baseEnd_7015637 := by
    simpa [prefixWord, tailWord_7015637, baseEnd_7015637] using wordTrace_append hprefix tailTrace_7015637
  have hstable : (prefixWord ++ tailWord_7015637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015637).length < 2 ^ (prefixWord ++ tailWord_7015637).sum := by decide
  have hdescent : baseEnd_7015637 < baseStart_7015637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015684 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_7015684 : Nat := 118140960795 + 7015684 * 2 ^ 59
def prefixEnd_7015684 : Nat := 4983230072969 + 3 ^ 40 * 7015684 * 2
def baseEnd_7015684 : Nat := 3602418012057834337785463

theorem tailTrace_7015684 : CollatzResearch.WordTrace tailWord_7015684 prefixEnd_7015684 3602418012057834337785463 := by
  unfold tailWord_7015684
  simp only [CollatzResearch.WordTrace]
  refine ⟨127941508557691263140027053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170588678076921684186702737 127941508557691263140027053)
  ·
    refine ⟨47978065709134223677510145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127941508557691263140027053 47978065709134223677510145)
    ·
      refine ⟨35983549281850667758132609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47978065709134223677510145 35983549281850667758132609)
      ·
        refine ⟨26987661961388000818599457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35983549281850667758132609 26987661961388000818599457)
        ·
          refine ⟨20240746471041000613949593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26987661961388000818599457 20240746471041000613949593)
          ·
            refine ⟨15180559853280750460462195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20240746471041000613949593 15180559853280750460462195)
            ·
              refine ⟨22770839779921125690693293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15180559853280750460462195 22770839779921125690693293)
              ·
                refine ⟨8539064917470422134009985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22770839779921125690693293 8539064917470422134009985)
                ·
                  refine ⟨6404298688102816600507489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8539064917470422134009985 6404298688102816600507489)
                  ·
                    refine ⟨4803224016077112450380617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6404298688102816600507489 4803224016077112450380617)
                    ·
                      refine ⟨3602418012057834337785463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803224016077112450380617 3602418012057834337785463)
                      ·
                        rfl

theorem cell23_7015684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_7015684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015684 prefixEnd_7015684 := by exact prefixLift 7015684
  have htrace : WordTrace (prefixWord ++ tailWord_7015684) baseStart_7015684 baseEnd_7015684 := by
    simpa [prefixWord, tailWord_7015684, baseEnd_7015684] using wordTrace_append hprefix tailTrace_7015684
  have hstable : (prefixWord ++ tailWord_7015684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015684).length < 2 ^ (prefixWord ++ tailWord_7015684).sum := by decide
  have hdescent : baseEnd_7015684 < baseStart_7015684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015720 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 2, 5]
def baseStart_7015720 : Nat := 118140960795 + 7015720 * 2 ^ 59
def prefixEnd_7015720 : Nat := 4983230072969 + 3 ^ 40 * 7015720 * 2
def baseEnd_7015720 : Nat := 1200812165787132065645099

theorem tailTrace_7015720 : CollatzResearch.WordTrace tailWord_7015720 prefixEnd_7015720 1200812165787132065645099 := by
  unfold tailWord_7015720
  simp only [CollatzResearch.WordTrace]
  refine ⟨127942165071626052214182307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170589553428834736285576409 127942165071626052214182307)
  ·
    refine ⟨191913247607439078321273461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127942165071626052214182307 191913247607439078321273461)
    ·
      refine ⟨17991866963197413592619387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191913247607439078321273461 17991866963197413592619387)
      ·
        refine ⟨26987800444796120388929081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17991866963197413592619387 26987800444796120388929081)
        ·
          refine ⟨20240850333597090291696811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26987800444796120388929081 20240850333597090291696811)
          ·
            refine ⟨30361275500395635437545217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20240850333597090291696811 30361275500395635437545217)
            ·
              refine ⟨22770956625296726578158913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30361275500395635437545217 22770956625296726578158913)
              ·
                refine ⟨17078217468972544933619185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22770956625296726578158913 17078217468972544933619185)
                ·
                  refine ⟨12808663101729408700214389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17078217468972544933619185 12808663101729408700214389)
                  ·
                    refine ⟨1200812165787132065645099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12808663101729408700214389 1200812165787132065645099)
                    ·
                      rfl

theorem cell23_7015720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_7015720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015720 prefixEnd_7015720 := by exact prefixLift 7015720
  have htrace : WordTrace (prefixWord ++ tailWord_7015720) baseStart_7015720 baseEnd_7015720 := by
    simpa [prefixWord, tailWord_7015720, baseEnd_7015720] using wordTrace_append hprefix tailTrace_7015720
  have hstable : (prefixWord ++ tailWord_7015720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015720).length < 2 ^ (prefixWord ++ tailWord_7015720).sum := by decide
  have hdescent : baseEnd_7015720 < baseStart_7015720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015734 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7015734 : Nat := 118140960795 + 7015734 * 2 ^ 59
def prefixEnd_7015734 : Nat := 4983230072969 + 3 ^ 40 * 7015734 * 2
def baseEnd_7015734 : Nat := 3602443686090559142160233

theorem tailTrace_7015734 : CollatzResearch.WordTrace tailWord_7015734 prefixEnd_7015734 3602443686090559142160233 := by
  unfold tailWord_7015734
  simp only [CollatzResearch.WordTrace]
  refine ⟨15992802547825086551210891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170589893843467589879582837 15992802547825086551210891)
  ·
    refine ⟨23989203821737629826816337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15992802547825086551210891 23989203821737629826816337)
    ·
      refine ⟨17991902866303222370112253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23989203821737629826816337 17991902866303222370112253)
      ·
        refine ⟨6746963574863708388792095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17991902866303222370112253 6746963574863708388792095)
        ·
          refine ⟨10120445362295562583188143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746963574863708388792095 10120445362295562583188143)
          ·
            refine ⟨15180668043443343874782215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10120445362295562583188143 15180668043443343874782215)
            ·
              refine ⟨22771002065165015812173323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15180668043443343874782215 22771002065165015812173323)
              ·
                refine ⟨34156503097747523718259985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22771002065165015812173323 34156503097747523718259985)
                ·
                  refine ⟨25617377323310642788694989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34156503097747523718259985 25617377323310642788694989)
                  ·
                    refine ⟨9606516496241491045760621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25617377323310642788694989 9606516496241491045760621)
                    ·
                      refine ⟨3602443686090559142160233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9606516496241491045760621 3602443686090559142160233)
                      ·
                        rfl

theorem cell23_7015734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7015734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015734 prefixEnd_7015734 := by exact prefixLift 7015734
  have htrace : WordTrace (prefixWord ++ tailWord_7015734) baseStart_7015734 baseEnd_7015734 := by
    simpa [prefixWord, tailWord_7015734, baseEnd_7015734] using wordTrace_append hprefix tailTrace_7015734
  have hstable : (prefixWord ++ tailWord_7015734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015734).length < 2 ^ (prefixWord ++ tailWord_7015734).sum := by decide
  have hdescent : baseEnd_7015734 < baseStart_7015734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015740 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 1, 6, 2]
def baseStart_7015740 : Nat := 118140960795 + 7015740 * 2 ^ 59
def prefixEnd_7015740 : Nat := 4983230072969 + 3 ^ 40 * 7015740 * 2
def baseEnd_7015740 : Nat := 3602446766974486118685205

theorem tailTrace_7015740 : CollatzResearch.WordTrace tailWord_7015740 prefixEnd_7015740 3602446766974486118685205 := by
  unfold tailWord_7015740
  simp only [CollatzResearch.WordTrace]
  refine ⟨127942529801589823922046337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170590039735453098562728449 127942529801589823922046337)
  ·
    refine ⟨95956897351192367941534753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127942529801589823922046337 95956897351192367941534753)
    ·
      refine ⟨71967673013394275956151065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95956897351192367941534753 71967673013394275956151065)
      ·
        refine ⟨53975754760045706967113299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71967673013394275956151065 53975754760045706967113299)
        ·
          refine ⟨80963632140068560450669949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53975754760045706967113299 80963632140068560450669949)
          ·
            refine ⟨30361362052525710169001231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80963632140068560450669949 30361362052525710169001231)
            ·
              refine ⟨45542043078788565253501847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30361362052525710169001231 45542043078788565253501847)
              ·
                refine ⟨68313064618182847880252771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45542043078788565253501847 68313064618182847880252771)
                ·
                  refine ⟨102469596927274271820379157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68313064618182847880252771 102469596927274271820379157)
                  ·
                    refine ⟨4803262355965981491580273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102469596927274271820379157 4803262355965981491580273)
                    ·
                      refine ⟨3602446766974486118685205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803262355965981491580273 3602446766974486118685205)
                      ·
                        rfl

theorem cell23_7015740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_7015740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015740 prefixEnd_7015740 := by exact prefixLift 7015740
  have htrace : WordTrace (prefixWord ++ tailWord_7015740) baseStart_7015740 baseEnd_7015740 := by
    simpa [prefixWord, tailWord_7015740, baseEnd_7015740] using wordTrace_append hprefix tailTrace_7015740
  have hstable : (prefixWord ++ tailWord_7015740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015740).length < 2 ^ (prefixWord ++ tailWord_7015740).sum := by decide
  have hdescent : baseEnd_7015740 < baseStart_7015740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015767 : List Nat := [1, 1, 3, 2, 3, 2, 1, 5, 1, 4]
def baseStart_7015767 : Nat := 118140960795 + 7015767 * 2 ^ 59
def prefixEnd_7015767 : Nat := 4983230072969 + 3 ^ 40 * 7015767 * 2
def baseEnd_7015767 : Nat := 1200820210317385837682527

theorem tailTrace_7015767 : CollatzResearch.WordTrace tailWord_7015767 prefixEnd_7015767 1200820210317385837682527 := by
  unfold tailWord_7015767
  simp only [CollatzResearch.WordTrace]
  refine ⟨255886044374081831455325555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170590696249387887636883703 255886044374081831455325555)
  ·
    refine ⟨383829066561122747182988333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255886044374081831455325555 383829066561122747182988333)
    ·
      refine ⟨143935899960421030193620625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383829066561122747182988333 143935899960421030193620625)
      ·
        refine ⟨107951924970315772645215469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143935899960421030193620625 107951924970315772645215469)
        ·
          refine ⟨40481971863868414741955801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107951924970315772645215469 40481971863868414741955801)
          ·
            refine ⟨30361478897901311056466851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40481971863868414741955801 30361478897901311056466851)
            ·
              refine ⟨45542218346851966584700277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30361478897901311056466851 45542218346851966584700277)
              ·
                refine ⟨4269582970017371867315651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45542218346851966584700277 4269582970017371867315651)
                ·
                  refine ⟨6404374455026057800973477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269582970017371867315651 6404374455026057800973477)
                  ·
                    refine ⟨1200820210317385837682527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6404374455026057800973477 1200820210317385837682527)
                    ·
                      rfl

theorem cell23_7015767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_7015767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015767 prefixEnd_7015767 := by exact prefixLift 7015767
  have htrace : WordTrace (prefixWord ++ tailWord_7015767) baseStart_7015767 baseEnd_7015767 := by
    simpa [prefixWord, tailWord_7015767, baseEnd_7015767] using wordTrace_append hprefix tailTrace_7015767
  have hstable : (prefixWord ++ tailWord_7015767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015767).length < 2 ^ (prefixWord ++ tailWord_7015767).sum := by decide
  have hdescent : baseEnd_7015767 < baseStart_7015767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015780 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 6]
def baseStart_7015780 : Nat := 118140960795 + 7015780 * 2 ^ 59
def prefixEnd_7015780 : Nat := 4983230072969 + 3 ^ 40 * 7015780 * 2
def baseEnd_7015780 : Nat := 400274145133407329131669

theorem tailTrace_7015780 : CollatzResearch.WordTrace tailWord_7015780 prefixEnd_7015780 400274145133407329131669 := by
  unfold tailWord_7015780
  simp only [CollatzResearch.WordTrace]
  refine ⟨127943259261517367337774397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170591012348689823117032529 127943259261517367337774397)
  ·
    refine ⟨47978722223069012751665399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127943259261517367337774397 47978722223069012751665399)
    ·
      refine ⟨71968083334603519127498099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47978722223069012751665399 71968083334603519127498099)
      ·
        refine ⟨107952125001905278691247149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71968083334603519127498099 107952125001905278691247149)
        ·
          refine ⟨40482046875714479509217681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107952125001905278691247149 40482046875714479509217681)
          ·
            refine ⟨30361535156785859631913261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40482046875714479509217681 30361535156785859631913261)
            ·
              refine ⟨11385575683794697361967473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30361535156785859631913261 11385575683794697361967473)
              ·
                refine ⟨8539181762846023021475605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11385575683794697361967473 8539181762846023021475605)
                ·
                  refine ⟨400274145133407329131669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8539181762846023021475605 400274145133407329131669)
                  ·
                    rfl

theorem cell23_7015780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_7015780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015780 prefixEnd_7015780 := by exact prefixLift 7015780
  have htrace : WordTrace (prefixWord ++ tailWord_7015780) baseStart_7015780 baseEnd_7015780 := by
    simpa [prefixWord, tailWord_7015780, baseEnd_7015780] using wordTrace_append hprefix tailTrace_7015780
  have hstable : (prefixWord ++ tailWord_7015780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015780).length < 2 ^ (prefixWord ++ tailWord_7015780).sum := by decide
  have hdescent : baseEnd_7015780 < baseStart_7015780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015793 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 5, 5]
def baseStart_7015793 : Nat := 118140960795 + 7015793 * 2 ^ 59
def prefixEnd_7015793 : Nat := 4983230072969 + 3 ^ 40 * 7015793 * 2
def baseEnd_7015793 : Nat := 1200824660483058137107487

theorem tailTrace_7015793 : CollatzResearch.WordTrace tailWord_7015793 prefixEnd_7015793 1200824660483058137107487 := by
  unfold tailWord_7015793
  simp only [CollatzResearch.WordTrace]
  refine ⟨255886992671987637895772033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170591328447991758597181355 255886992671987637895772033)
  ·
    refine ⟨191915244503990728421829025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255886992671987637895772033 191915244503990728421829025)
    ·
      refine ⟨143936433377993046316371769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191915244503990728421829025 143936433377993046316371769)
      ·
        refine ⟨107952325033494784737278827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143936433377993046316371769 107952325033494784737278827)
        ·
          refine ⟨161928487550242177105918241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107952325033494784737278827 161928487550242177105918241)
          ·
            refine ⟨121446365662681632829438681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161928487550242177105918241 121446365662681632829438681)
            ·
              refine ⟨91084774247011224622079011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121446365662681632829438681 91084774247011224622079011)
              ·
                refine ⟨136627161370516836933118517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91084774247011224622079011 136627161370516836933118517)
                ·
                  refine ⟨12808796378485953462479861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136627161370516836933118517 12808796378485953462479861)
                  ·
                    refine ⟨1200824660483058137107487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12808796378485953462479861 1200824660483058137107487)
                    ·
                      rfl

theorem cell23_7015793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_7015793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015793 prefixEnd_7015793 := by exact prefixLift 7015793
  have htrace : WordTrace (prefixWord ++ tailWord_7015793) baseStart_7015793 baseEnd_7015793 := by
    simpa [prefixWord, tailWord_7015793, baseEnd_7015793] using wordTrace_append hprefix tailTrace_7015793
  have hstable : (prefixWord ++ tailWord_7015793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015793).length < 2 ^ (prefixWord ++ tailWord_7015793).sum := by decide
  have hdescent : baseEnd_7015793 < baseStart_7015793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015840 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 4, 4]
def baseStart_7015840 : Nat := 118140960795 + 7015840 * 2 ^ 59
def prefixEnd_7015840 : Nat := 4983230072969 + 3 ^ 40 * 7015840 * 2
def baseEnd_7015840 : Nat := 1200832705013311909144915

theorem tailTrace_7015840 : CollatzResearch.WordTrace tailWord_7015840 prefixEnd_7015840 1200832705013311909144915 := by
  unfold tailWord_7015840
  simp only [CollatzResearch.WordTrace]
  refine ⟨127944353451408682461366487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170592471268544909948488649 127944353451408682461366487)
  ·
    refine ⟨191916530177113023692049731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127944353451408682461366487 191916530177113023692049731)
    ·
      refine ⟨287874795265669535538074597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191916530177113023692049731 287874795265669535538074597)
      ·
        refine ⟨53976524112313037913388987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287874795265669535538074597 53976524112313037913388987)
        ·
          refine ⟨80964786168469556870083481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53976524112313037913388987 80964786168469556870083481)
          ·
            refine ⟨60723589626352167652562611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80964786168469556870083481 60723589626352167652562611)
            ·
              refine ⟨91085384439528251478843917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60723589626352167652562611 91085384439528251478843917)
              ·
                refine ⟨34157019164823094304566469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91085384439528251478843917 34157019164823094304566469)
                ·
                  refine ⟨6404441093404330182106213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34157019164823094304566469 6404441093404330182106213)
                  ·
                    refine ⟨1200832705013311909144915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6404441093404330182106213 1200832705013311909144915)
                    ·
                      rfl

theorem cell23_7015840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4, 4].length) (baseStart_7015840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015840 prefixEnd_7015840 := by exact prefixLift 7015840
  have htrace : WordTrace (prefixWord ++ tailWord_7015840) baseStart_7015840 baseEnd_7015840 := by
    simpa [prefixWord, tailWord_7015840, baseEnd_7015840] using wordTrace_append hprefix tailTrace_7015840
  have hstable : (prefixWord ++ tailWord_7015840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015840).length < 2 ^ (prefixWord ++ tailWord_7015840).sum := by decide
  have hdescent : baseEnd_7015840 < baseStart_7015840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015843 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 6]
def baseStart_7015843 : Nat := 118140960795 + 7015843 * 2 ^ 59
def prefixEnd_7015843 : Nat := 4983230072969 + 3 ^ 40 * 7015843 * 2
def baseEnd_7015843 : Nat := 3602499655481899215697231

theorem tailTrace_7015843 : CollatzResearch.WordTrace tailWord_7015843 prefixEnd_7015843 3602499655481899215697231 := by
  unfold tailWord_7015843
  simp only [CollatzResearch.WordTrace]
  refine ⟨255888816321806496435092183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170592544214537664290061455 255888816321806496435092183)
  ·
    refine ⟨383833224482709744652638275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255888816321806496435092183 383833224482709744652638275)
    ·
      refine ⟨575749836724064616978957413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383833224482709744652638275 575749836724064616978957413)
      ·
        refine ⟨107953094385762115683554515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 575749836724064616978957413 107953094385762115683554515)
        ·
          refine ⟨161929641578643173525331773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107953094385762115683554515 161929641578643173525331773)
          ·
            refine ⟨60723615591991190071999415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161929641578643173525331773 60723615591991190071999415)
            ·
              refine ⟨91085423387986785107999123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60723615591991190071999415 91085423387986785107999123)
              ·
                refine ⟨136628135081980177661998685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91085423387986785107999123 136628135081980177661998685)
                ·
                  refine ⟨51235550655742566623249507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136628135081980177661998685 51235550655742566623249507)
                  ·
                    refine ⟨76853325983613849934874261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51235550655742566623249507 76853325983613849934874261)
                    ·
                      refine ⟨3602499655481899215697231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76853325983613849934874261 3602499655481899215697231)
                      ·
                        rfl

theorem cell23_7015843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_7015843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015843 prefixEnd_7015843 := by exact prefixLift 7015843
  have htrace : WordTrace (prefixWord ++ tailWord_7015843) baseStart_7015843 baseEnd_7015843 := by
    simpa [prefixWord, tailWord_7015843, baseEnd_7015843] using wordTrace_append hprefix tailTrace_7015843
  have hstable : (prefixWord ++ tailWord_7015843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015843).length < 2 ^ (prefixWord ++ tailWord_7015843).sum := by decide
  have hdescent : baseEnd_7015843 < baseStart_7015843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015857 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 2, 4]
def baseStart_7015857 : Nat := 118140960795 + 7015857 * 2 ^ 59
def prefixEnd_7015857 : Nat := 4983230072969 + 3 ^ 40 * 7015857 * 2
def baseEnd_7015857 : Nat := 1200835614737020720307389

theorem tailTrace_7015857 : CollatzResearch.WordTrace tailWord_7015857 prefixEnd_7015857 1200835614737020720307389 := by
  unfold tailWord_7015857
  simp only [CollatzResearch.WordTrace]
  refine ⟨255889326943755776826101825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170592884629170517884067883 255889326943755776826101825)
  ·
    refine ⟨191916995207816832619576369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255889326943755776826101825 191916995207816832619576369)
    ·
      refine ⟨143937746405862624464682277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191916995207816832619576369 143937746405862624464682277)
      ·
        refine ⟨26988327451099242087127927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143937746405862624464682277 26988327451099242087127927)
        ·
          refine ⟨40482491176648863130691891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26988327451099242087127927 40482491176648863130691891)
          ·
            refine ⟨60723736764973294696037837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40482491176648863130691891 60723736764973294696037837)
            ·
              refine ⟨22771401286864985511014189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60723736764973294696037837 22771401286864985511014189)
              ·
                refine ⟨8539275482574369566630321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22771401286864985511014189 8539275482574369566630321)
                ·
                  refine ⟨6404456611930777174972741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8539275482574369566630321 6404456611930777174972741)
                  ·
                    refine ⟨1200835614737020720307389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6404456611930777174972741 1200835614737020720307389)
                    ·
                      rfl

theorem cell23_7015857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_7015857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015857 prefixEnd_7015857 := by exact prefixLift 7015857
  have htrace : WordTrace (prefixWord ++ tailWord_7015857) baseStart_7015857 baseEnd_7015857 := by
    simpa [prefixWord, tailWord_7015857, baseEnd_7015857] using wordTrace_append hprefix tailTrace_7015857
  have hstable : (prefixWord ++ tailWord_7015857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015857).length < 2 ^ (prefixWord ++ tailWord_7015857).sum := by decide
  have hdescent : baseEnd_7015857 < baseStart_7015857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015898 : List Nat := [3, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2]
def baseStart_7015898 : Nat := 118140960795 + 7015898 * 2 ^ 59
def prefixEnd_7015898 : Nat := 4983230072969 + 3 ^ 40 * 7015898 * 2
def baseEnd_7015898 : Nat := 3602527896917896500509479

theorem tailTrace_7015898 : CollatzResearch.WordTrace tailWord_7015898 prefixEnd_7015898 3602527896917896500509479 := by
  unfold tailWord_7015898
  simp only [CollatzResearch.WordTrace]
  refine ⟨63972705584151810207086087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170593881557738160552229565 63972705584151810207086087)
  ·
    refine ⟨95959058376227715310629131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63972705584151810207086087 95959058376227715310629131)
    ·
      refine ⟨143938587564341572965943697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95959058376227715310629131 143938587564341572965943697)
      ·
        refine ⟨107953940673256179724457773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143938587564341572965943697 107953940673256179724457773)
        ·
          refine ⟨40482727752471067396671665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107953940673256179724457773 40482727752471067396671665)
          ·
            refine ⟨30362045814353300547503749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40482727752471067396671665 30362045814353300547503749)
            ·
              refine ⟨5692883590191243852656953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30362045814353300547503749 5692883590191243852656953)
              ·
                refine ⟨4269662692643432889492715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5692883590191243852656953 4269662692643432889492715)
                ·
                  refine ⟨6404494038965149334239073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269662692643432889492715 6404494038965149334239073)
                  ·
                    refine ⟨4803370529223862000679305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6404494038965149334239073 4803370529223862000679305)
                    ·
                      refine ⟨3602527896917896500509479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803370529223862000679305 3602527896917896500509479)
                      ·
                        rfl

theorem cell23_7015898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_7015898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015898 prefixEnd_7015898 := by exact prefixLift 7015898
  have htrace : WordTrace (prefixWord ++ tailWord_7015898) baseStart_7015898 baseEnd_7015898 := by
    simpa [prefixWord, tailWord_7015898, baseEnd_7015898] using wordTrace_append hprefix tailTrace_7015898
  have hstable : (prefixWord ++ tailWord_7015898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015898).length < 2 ^ (prefixWord ++ tailWord_7015898).sum := by decide
  have hdescent : baseEnd_7015898 < baseStart_7015898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015914 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_7015914 : Nat := 118140960795 + 7015914 * 2 ^ 59
def prefixEnd_7015914 : Nat := 4983230072969 + 3 ^ 40 * 7015914 * 2
def baseEnd_7015914 : Nat := 3602536112608368437909405

theorem tailTrace_7015914 : CollatzResearch.WordTrace tailWord_7015914 prefixEnd_7015914 3602536112608368437909405 := by
  unfold tailWord_7015914
  simp only [CollatzResearch.WordTrace]
  refine ⟨63972851476137318890231699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170594270603032850373951197 63972851476137318890231699)
  ·
    refine ⟨95959277214205978335347549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63972851476137318890231699 95959277214205978335347549)
    ·
      refine ⟨35984728955327241875755331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95959277214205978335347549 35984728955327241875755331)
      ·
        refine ⟨53977093432990862813632997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35984728955327241875755331 53977093432990862813632997)
        ·
          refine ⟨10120705018685786777556187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53977093432990862813632997 10120705018685786777556187)
          ·
            refine ⟨15181057528028680166334281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10120705018685786777556187 15181057528028680166334281)
            ·
              refine ⟨11385793146021510124750711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15181057528028680166334281 11385793146021510124750711)
              ·
                refine ⟨17078689719032265187126067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11385793146021510124750711 17078689719032265187126067)
                ·
                  refine ⟨25618034578548397780689101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17078689719032265187126067 25618034578548397780689101)
                  ·
                    refine ⟨9606762966955649167758413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25618034578548397780689101 9606762966955649167758413)
                    ·
                      refine ⟨3602536112608368437909405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9606762966955649167758413 3602536112608368437909405)
                      ·
                        rfl

theorem cell23_7015914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_7015914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015914 prefixEnd_7015914 := by exact prefixLift 7015914
  have htrace : WordTrace (prefixWord ++ tailWord_7015914) baseStart_7015914 baseEnd_7015914 := by
    simpa [prefixWord, tailWord_7015914, baseEnd_7015914] using wordTrace_append hprefix tailTrace_7015914
  have hstable : (prefixWord ++ tailWord_7015914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015914).length < 2 ^ (prefixWord ++ tailWord_7015914).sum := by decide
  have hdescent : baseEnd_7015914 < baseStart_7015914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015942 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7015942 : Nat := 118140960795 + 7015942 * 2 ^ 59
def prefixEnd_7015942 : Nat := 4983230072969 + 3 ^ 40 * 7015942 * 2
def baseEnd_7015942 : Nat := 1200850163355564776119759

theorem tailTrace_7015942 : CollatzResearch.WordTrace tailWord_7015942 prefixEnd_7015942 1200850163355564776119759 := by
  unfold tailWord_7015942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996638348388994885717065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170594951432298557561964053 7996638348388994885717065)
  ·
    refine ⟨5997478761291746164287799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7996638348388994885717065 5997478761291746164287799)
    ·
      refine ⟨8996218141937619246431699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5997478761291746164287799 8996218141937619246431699)
      ·
        refine ⟨13494327212906428869647549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8996218141937619246431699 13494327212906428869647549)
        ·
          refine ⟨5060372704839910826117831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13494327212906428869647549 5060372704839910826117831)
          ·
            refine ⟨7590559057259866239176747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060372704839910826117831 7590559057259866239176747)
            ·
              refine ⟨11385838585889799358765121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590559057259866239176747 11385838585889799358765121)
              ·
                refine ⟨8539378939417349519073841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11385838585889799358765121 8539378939417349519073841)
                ·
                  refine ⟨6404534204563012139305381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8539378939417349519073841 6404534204563012139305381)
                  ·
                    refine ⟨1200850163355564776119759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6404534204563012139305381 1200850163355564776119759)
                    ·
                      rfl

theorem cell23_7015942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7015942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015942 prefixEnd_7015942 := by exact prefixLift 7015942
  have htrace : WordTrace (prefixWord ++ tailWord_7015942) baseStart_7015942 baseEnd_7015942 := by
    simpa [prefixWord, tailWord_7015942, baseEnd_7015942] using wordTrace_append hprefix tailTrace_7015942
  have hstable : (prefixWord ++ tailWord_7015942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015942).length < 2 ^ (prefixWord ++ tailWord_7015942).sum := by decide
  have hdescent : baseEnd_7015942 < baseStart_7015942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015948 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 2, 1, 3]
def baseStart_7015948 : Nat := 118140960795 + 7015948 * 2 ^ 59
def prefixEnd_7015948 : Nat := 4983230072969 + 3 ^ 40 * 7015948 * 2
def baseEnd_7015948 : Nat := 3602553570950621304884249

theorem tailTrace_7015948 : CollatzResearch.WordTrace tailWord_7015948 prefixEnd_7015948 3602553570950621304884249 := by
  unfold tailWord_7015948
  simp only [CollatzResearch.WordTrace]
  refine ⟨127946322993213049683832249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170595097324284066245109665 127946322993213049683832249)
  ·
    refine ⟨95959742244909787262874187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127946322993213049683832249 95959742244909787262874187)
    ·
      refine ⟨143939613367364680894311281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95959742244909787262874187 143939613367364680894311281)
      ·
        refine ⟨107954710025523510670733461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143939613367364680894311281 107954710025523510670733461)
        ·
          refine ⟨5060377032446414562690631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107954710025523510670733461 5060377032446414562690631)
          ·
            refine ⟨7590565548669621844035947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060377032446414562690631 7590565548669621844035947)
            ·
              refine ⟨11385848323004432766053921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590565548669621844035947 11385848323004432766053921)
              ·
                refine ⟨8539386242253324574540441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11385848323004432766053921 8539386242253324574540441)
                ·
                  refine ⟨6404539681689993430905331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8539386242253324574540441 6404539681689993430905331)
                  ·
                    refine ⟨9606809522534990146357997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6404539681689993430905331 9606809522534990146357997)
                    ·
                      refine ⟨3602553570950621304884249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9606809522534990146357997 3602553570950621304884249)
                      ·
                        rfl

theorem cell23_7015948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_7015948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015948 prefixEnd_7015948 := by exact prefixLift 7015948
  have htrace : WordTrace (prefixWord ++ tailWord_7015948) baseStart_7015948 baseEnd_7015948 := by
    simpa [prefixWord, tailWord_7015948, baseEnd_7015948] using wordTrace_append hprefix tailTrace_7015948
  have hstable : (prefixWord ++ tailWord_7015948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015948).length < 2 ^ (prefixWord ++ tailWord_7015948).sum := by decide
  have hdescent : baseEnd_7015948 < baseStart_7015948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7015971 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 1, 4, 2]
def baseStart_7015971 : Nat := 118140960795 + 7015971 * 2 ^ 59
def prefixEnd_7015971 : Nat := 4983230072969 + 3 ^ 40 * 7015971 * 2
def baseEnd_7015971 : Nat := 3602565381005674714896643

theorem tailTrace_7015971 : CollatzResearch.WordTrace tailWord_7015971 prefixEnd_7015971 3602565381005674714896643 := by
  unfold tailWord_7015971
  simp only [CollatzResearch.WordTrace]
  refine ⟨255893484865342774295751767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170595656576895182863834511 255893484865342774295751767)
  ·
    refine ⟨383840227298014161443627651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255893484865342774295751767 383840227298014161443627651)
    ·
      refine ⟨575760340947021242165441477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383840227298014161443627651 575760340947021242165441477)
      ·
        refine ⟨107955063927566482906020277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 575760340947021242165441477 107955063927566482906020277)
        ·
          refine ⟨10120787243209357772439401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107955063927566482906020277 10120787243209357772439401)
          ·
            refine ⟨7590590432407018329329551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10120787243209357772439401 7590590432407018329329551)
            ·
              refine ⟨11385885648610527493994327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590590432407018329329551 11385885648610527493994327)
              ·
                refine ⟨17078828472915791240991491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11385885648610527493994327 17078828472915791240991491)
                ·
                  refine ⟨25618242709373686861487237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17078828472915791240991491 25618242709373686861487237)
                  ·
                    refine ⟨4803420508007566286528857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25618242709373686861487237 4803420508007566286528857)
                    ·
                      refine ⟨3602565381005674714896643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803420508007566286528857 3602565381005674714896643)
                      ·
                        rfl

theorem cell23_7015971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_7015971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7015971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7015971 prefixEnd_7015971 := by exact prefixLift 7015971
  have htrace : WordTrace (prefixWord ++ tailWord_7015971) baseStart_7015971 baseEnd_7015971 := by
    simpa [prefixWord, tailWord_7015971, baseEnd_7015971] using wordTrace_append hprefix tailTrace_7015971
  have hstable : (prefixWord ++ tailWord_7015971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7015971).length < 2 ^ (prefixWord ++ tailWord_7015971).sum := by decide
  have hdescent : baseEnd_7015971 < baseStart_7015971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7015971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016000 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_7016000 : Nat := 118140960795 + 7016000 * 2 ^ 59
def prefixEnd_7016000 : Nat := 4983230072969 + 3 ^ 40 * 7016000 * 2
def baseEnd_7016000 : Nat := 3602580271944655101434009

theorem tailTrace_7016000 : CollatzResearch.WordTrace tailWord_7016000 prefixEnd_7016000 3602580271944655101434009 := by
  unfold tailWord_7016000
  simp only [CollatzResearch.WordTrace]
  refine ⟨127947271291118856124278727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170596361721491808165704969 127947271291118856124278727)
  ·
    refine ⟨191920906936678284186418091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127947271291118856124278727 191920906936678284186418091)
    ·
      refine ⟨287881360405017426279627137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191920906936678284186418091 287881360405017426279627137)
      ·
        refine ⟨215911020303763069709720353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287881360405017426279627137 215911020303763069709720353)
        ·
          refine ⟨161933265227822302282290265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215911020303763069709720353 161933265227822302282290265)
          ·
            refine ⟨121449948920866726711717699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161933265227822302282290265 121449948920866726711717699)
            ·
              refine ⟨182174923381300090067576549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121449948920866726711717699 182174923381300090067576549)
              ·
                refine ⟨34157798133993766887670603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182174923381300090067576549 34157798133993766887670603)
                ·
                  refine ⟨51236697200990650331505905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34157798133993766887670603 51236697200990650331505905)
                  ·
                    refine ⟨38427522900742987748629429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51236697200990650331505905 38427522900742987748629429)
                    ·
                      refine ⟨3602580271944655101434009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38427522900742987748629429 3602580271944655101434009)
                      ·
                        rfl

theorem cell23_7016000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_7016000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016000 prefixEnd_7016000 := by exact prefixLift 7016000
  have htrace : WordTrace (prefixWord ++ tailWord_7016000) baseStart_7016000 baseEnd_7016000 := by
    simpa [prefixWord, tailWord_7016000, baseEnd_7016000] using wordTrace_append hprefix tailTrace_7016000
  have hstable : (prefixWord ++ tailWord_7016000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016000).length < 2 ^ (prefixWord ++ tailWord_7016000).sum := by decide
  have hdescent : baseEnd_7016000 < baseStart_7016000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016022 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7016022 : Nat := 118140960795 + 7016022 * 2 ^ 59
def prefixEnd_7016022 : Nat := 4983230072969 + 3 ^ 40 * 7016022 * 2
def baseEnd_7016022 : Nat := 3602591568519054015358909

theorem tailTrace_7016022 : CollatzResearch.WordTrace tailWord_7016022 prefixEnd_7016022 3602591568519054015358909 := by
  unfold tailWord_7016022
  simp only [CollatzResearch.WordTrace]
  refine ⟨15993459061759875625366145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170596896658772006670572213 15993459061759875625366145)
  ·
    refine ⟨11995094296319906719024609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15993459061759875625366145 11995094296319906719024609)
    ·
      refine ⟨8996320722239930039268457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11995094296319906719024609 8996320722239930039268457)
      ·
        refine ⟨6747240541679947529451343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8996320722239930039268457 6747240541679947529451343)
        ·
          refine ⟨10120860812519921294177015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747240541679947529451343 10120860812519921294177015)
          ·
            refine ⟨15181291218779881941265523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10120860812519921294177015 15181291218779881941265523)
            ·
              refine ⟨22771936828169822911898285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15181291218779881941265523 22771936828169822911898285)
              ·
                refine ⟨8539476310563683591961857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22771936828169822911898285 8539476310563683591961857)
                ·
                  refine ⟨6404607232922762693971393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8539476310563683591961857 6404607232922762693971393)
                  ·
                    refine ⟨4803455424692072020478545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6404607232922762693971393 4803455424692072020478545)
                    ·
                      refine ⟨3602591568519054015358909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803455424692072020478545 3602591568519054015358909)
                      ·
                        rfl

theorem cell23_7016022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7016022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016022 prefixEnd_7016022 := by exact prefixLift 7016022
  have htrace : WordTrace (prefixWord ++ tailWord_7016022) baseStart_7016022 baseEnd_7016022 := by
    simpa [prefixWord, tailWord_7016022, baseEnd_7016022] using wordTrace_append hprefix tailTrace_7016022
  have hstable : (prefixWord ++ tailWord_7016022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016022).length < 2 ^ (prefixWord ++ tailWord_7016022).sum := by decide
  have hdescent : baseEnd_7016022 < baseStart_7016022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016071 : List Nat := [1, 1, 4, 2, 1, 4, 1, 4, 1, 4]
def baseStart_7016071 : Nat := 118140960795 + 7016071 * 2 ^ 59
def prefixEnd_7016071 : Nat := 4983230072969 + 3 ^ 40 * 7016071 * 2
def baseEnd_7016071 : Nat := 1200872243023708107882061

theorem tailTrace_7016071 : CollatzResearch.WordTrace tailWord_7016071 prefixEnd_7016071 1200872243023708107882061 := by
  unfold tailWord_7016071
  simp only [CollatzResearch.WordTrace]
  refine ⟨255897132164980491374392067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170598088109986994249594711 255897132164980491374392067)
  ·
    refine ⟨383845698247470737061588101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255897132164980491374392067 383845698247470737061588101)
    ·
      refine ⟨71971068421400763199047769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383845698247470737061588101 71971068421400763199047769)
      ·
        refine ⟨53978301316050572399285827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71971068421400763199047769 53978301316050572399285827)
        ·
          refine ⟨80967451974075858598928741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53978301316050572399285827 80967451974075858598928741)
          ·
            refine ⟨15181397245139223487299139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80967451974075858598928741 15181397245139223487299139)
            ·
              refine ⟨22772095867708835230948709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15181397245139223487299139 22772095867708835230948709)
              ·
                refine ⟨4269767975195406605802883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22772095867708835230948709 4269767975195406605802883)
                ·
                  refine ⟨6404651962793109908704325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269767975195406605802883 6404651962793109908704325)
                  ·
                    refine ⟨1200872243023708107882061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6404651962793109908704325 1200872243023708107882061)
                    ·
                      rfl

theorem cell23_7016071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_7016071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016071 prefixEnd_7016071 := by exact prefixLift 7016071
  have htrace : WordTrace (prefixWord ++ tailWord_7016071) baseStart_7016071 baseEnd_7016071 := by
    simpa [prefixWord, tailWord_7016071, baseEnd_7016071] using wordTrace_append hprefix tailTrace_7016071
  have hstable : (prefixWord ++ tailWord_7016071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016071).length < 2 ^ (prefixWord ++ tailWord_7016071).sum := by decide
  have hdescent : baseEnd_7016071 < baseStart_7016071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016118 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_7016118 : Nat := 118140960795 + 7016118 * 2 ^ 59
def prefixEnd_7016118 : Nat := 4983230072969 + 3 ^ 40 * 7016118 * 2
def baseEnd_7016118 : Nat := 400293429184653959973163

theorem tailTrace_7016118 : CollatzResearch.WordTrace tailWord_7016118 prefixEnd_7016118 400293429184653959973163 := by
  unfold tailWord_7016118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15993677899738138650084563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170599230930540145600902005 15993677899738138650084563)
  ·
    refine ⟨23990516849607207975126845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15993677899738138650084563 23990516849607207975126845)
    ·
      refine ⟨8996443818602702990672567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23990516849607207975126845 8996443818602702990672567)
      ·
        refine ⟨13494665727904054486008851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8996443818602702990672567 13494665727904054486008851)
        ·
          refine ⟨20241998591856081729013277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13494665727904054486008851 20241998591856081729013277)
          ·
            refine ⟨7590749471946030648379979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20241998591856081729013277 7590749471946030648379979)
            ·
              refine ⟨11386124207919045972569969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590749471946030648379979 11386124207919045972569969)
              ·
                refine ⟨8539593155939284479427477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11386124207919045972569969 8539593155939284479427477)
                ·
                  refine ⟨400293429184653959973163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8539593155939284479427477 400293429184653959973163)
                  ·
                    rfl

theorem cell23_7016118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_7016118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016118 prefixEnd_7016118 := by exact prefixLift 7016118
  have htrace : WordTrace (prefixWord ++ tailWord_7016118) baseStart_7016118 baseEnd_7016118 := by
    simpa [prefixWord, tailWord_7016118, baseEnd_7016118] using wordTrace_append hprefix tailTrace_7016118
  have hstable : (prefixWord ++ tailWord_7016118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016118).length < 2 ^ (prefixWord ++ tailWord_7016118).sum := by decide
  have hdescent : baseEnd_7016118 < baseStart_7016118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016151 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 3, 2, 2]
def baseStart_7016151 : Nat := 118140960795 + 7016151 * 2 ^ 59
def prefixEnd_7016151 : Nat := 4983230072969 + 3 ^ 40 * 7016151 * 2
def baseEnd_7016151 : Nat := 3602657807523484010645815

theorem tailTrace_7016151 : CollatzResearch.WordTrace tailWord_7016151 prefixEnd_7016151 3602657807523484010645815 := by
  unfold tailWord_7016151
  simp only [CollatzResearch.WordTrace]
  refine ⟨255900050004690665037304307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170600033336460443358202871 255900050004690665037304307)
  ·
    refine ⟨383850075007035997555956461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255900050004690665037304307 383850075007035997555956461)
    ·
      refine ⟨143943778127638499083483673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383850075007035997555956461 143943778127638499083483673)
      ·
        refine ⟨107957833595728874312612755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143943778127638499083483673 107957833595728874312612755)
        ·
          refine ⟨161936750393593311468919133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107957833595728874312612755 161936750393593311468919133)
          ·
            refine ⟨60726281397597491800844675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161936750393593311468919133 60726281397597491800844675)
            ·
              refine ⟨91089422096396237701267013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60726281397597491800844675 91089422096396237701267013)
              ·
                refine ⟨17079266643074294568987565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91089422096396237701267013 17079266643074294568987565)
                ·
                  refine ⟨6404724991152860463370337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17079266643074294568987565 6404724991152860463370337)
                  ·
                    refine ⟨4803543743364645347527753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6404724991152860463370337 4803543743364645347527753)
                    ·
                      refine ⟨3602657807523484010645815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803543743364645347527753 3602657807523484010645815)
                      ·
                        rfl

theorem cell23_7016151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_7016151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016151 prefixEnd_7016151 := by exact prefixLift 7016151
  have htrace : WordTrace (prefixWord ++ tailWord_7016151) baseStart_7016151 baseEnd_7016151 := by
    simpa [prefixWord, tailWord_7016151, baseEnd_7016151] using wordTrace_append hprefix tailTrace_7016151
  have hstable : (prefixWord ++ tailWord_7016151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016151).length < 2 ^ (prefixWord ++ tailWord_7016151).sum := by decide
  have hdescent : baseEnd_7016151 < baseStart_7016151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016194 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_7016194 : Nat := 118140960795 + 7016194 * 2 ^ 59
def prefixEnd_7016194 : Nat := 4983230072969 + 3 ^ 40 * 7016194 * 2
def baseEnd_7016194 : Nat := 3602679887191627342408117

theorem tailTrace_7016194 : CollatzResearch.WordTrace tailWord_7016194 prefixEnd_7016194 3602679887191627342408117 := by
  unfold tailWord_7016194
  simp only [CollatzResearch.WordTrace]
  refine ⟨63975404585883720845279909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170601078895689922254079757 63975404585883720845279909)
  ·
    refine ⟨11995388359853197658489983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63975404585883720845279909 11995388359853197658489983)
    ·
      refine ⟨17993082539779796487734975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11995388359853197658489983 17993082539779796487734975)
      ·
        refine ⟨26989623809669694731602463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17993082539779796487734975 26989623809669694731602463)
        ·
          refine ⟨40484435714504542097403695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26989623809669694731602463 40484435714504542097403695)
          ·
            refine ⟨60726653571756813146105543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40484435714504542097403695 60726653571756813146105543)
            ·
              refine ⟨91089980357635219719158315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60726653571756813146105543 91089980357635219719158315)
              ·
                refine ⟨136634970536452829578737473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91089980357635219719158315 136634970536452829578737473)
                ·
                  refine ⟨102476227902339622184053105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136634970536452829578737473 102476227902339622184053105)
                  ·
                    refine ⟨76857170926754716638039829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102476227902339622184053105 76857170926754716638039829)
                    ·
                      refine ⟨3602679887191627342408117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76857170926754716638039829 3602679887191627342408117)
                      ·
                        rfl

theorem cell23_7016194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_7016194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016194 prefixEnd_7016194 := by exact prefixLift 7016194
  have htrace : WordTrace (prefixWord ++ tailWord_7016194) baseStart_7016194 baseEnd_7016194 := by
    simpa [prefixWord, tailWord_7016194, baseEnd_7016194] using wordTrace_append hprefix tailTrace_7016194
  have hstable : (prefixWord ++ tailWord_7016194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016194).length < 2 ^ (prefixWord ++ tailWord_7016194).sum := by decide
  have hdescent : baseEnd_7016194 < baseStart_7016194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016207 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_7016207 : Nat := 118140960795 + 7016207 * 2 ^ 59
def prefixEnd_7016207 : Nat := 4983230072969 + 3 ^ 40 * 7016207 * 2
def baseEnd_7016207 : Nat := 3602686562440135791545557

theorem tailTrace_7016207 : CollatzResearch.WordTrace tailWord_7016207 prefixEnd_7016207 3602686562440135791545557 := by
  unfold tailWord_7016207
  simp only [CollatzResearch.WordTrace]
  refine ⟨255902092492487786601342875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170601394994991857734228583 255902092492487786601342875)
  ·
    refine ⟨383853138738731679902014313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255902092492487786601342875 383853138738731679902014313)
    ·
      refine ⟨287889854054048759926510735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383853138738731679902014313 287889854054048759926510735)
      ·
        refine ⟨431834781081073139889766103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287889854054048759926510735 431834781081073139889766103)
        ·
          refine ⟨647752171621609709834649155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431834781081073139889766103 647752171621609709834649155)
          ·
            refine ⟨971628257432414564751973733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647752171621609709834649155 971628257432414564751973733)
            ·
              refine ⟨182180298268577730890995075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 971628257432414564751973733 182180298268577730890995075)
              ·
                refine ⟨273270447402866596336492613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182180298268577730890995075 273270447402866596336492613)
                ·
                  refine ⟨51238208888037486813092365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273270447402866596336492613 51238208888037486813092365)
                  ·
                    refine ⟨19214328333014057554909637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51238208888037486813092365 19214328333014057554909637)
                    ·
                      refine ⟨3602686562440135791545557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19214328333014057554909637 3602686562440135791545557)
                      ·
                        rfl

theorem cell23_7016207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_7016207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016207 prefixEnd_7016207 := by exact prefixLift 7016207
  have htrace : WordTrace (prefixWord ++ tailWord_7016207) baseStart_7016207 baseEnd_7016207 := by
    simpa [prefixWord, tailWord_7016207, baseEnd_7016207] using wordTrace_append hprefix tailTrace_7016207
  have hstable : (prefixWord ++ tailWord_7016207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016207).length < 2 ^ (prefixWord ++ tailWord_7016207).sum := by decide
  have hdescent : baseEnd_7016207 < baseStart_7016207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016211 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 1, 3, 2]
def baseStart_7016211 : Nat := 118140960795 + 7016211 * 2 ^ 59
def prefixEnd_7016211 : Nat := 4983230072969 + 3 ^ 40 * 7016211 * 2
def baseEnd_7016211 : Nat := 3602688616362753775895539

theorem tailTrace_7016211 : CollatzResearch.WordTrace tailWord_7016211 prefixEnd_7016211 3602688616362753775895539 := by
  unfold tailWord_7016211
  simp only [CollatzResearch.WordTrace]
  refine ⟨255902238384473295284488487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170601492256315530189658991 255902238384473295284488487)
  ·
    refine ⟨383853357576709942926732731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255902238384473295284488487 383853357576709942926732731)
    ·
      refine ⟨575780036365064914390099097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383853357576709942926732731 575780036365064914390099097)
      ·
        refine ⟨431835027273798685792574323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575780036365064914390099097 431835027273798685792574323)
        ·
          refine ⟨647752540910698028688861485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431835027273798685792574323 647752540910698028688861485)
          ·
            refine ⟨242907202841511760758323057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647752540910698028688861485 242907202841511760758323057)
            ·
              refine ⟨182180402131133820568742293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242907202841511760758323057 182180402131133820568742293)
              ·
                refine ⟨8539706349896897839159795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182180402131133820568742293 8539706349896897839159795)
                ·
                  refine ⟨12809559524845346758739693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8539706349896897839159795 12809559524845346758739693)
                  ·
                    refine ⟨4803584821817005034527385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12809559524845346758739693 4803584821817005034527385)
                    ·
                      refine ⟨3602688616362753775895539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803584821817005034527385 3602688616362753775895539)
                      ·
                        rfl

theorem cell23_7016211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 3, 2].length) (baseStart_7016211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016211 prefixEnd_7016211 := by exact prefixLift 7016211
  have htrace : WordTrace (prefixWord ++ tailWord_7016211) baseStart_7016211 baseEnd_7016211 := by
    simpa [prefixWord, tailWord_7016211, baseEnd_7016211] using wordTrace_append hprefix tailTrace_7016211
  have hstable : (prefixWord ++ tailWord_7016211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016211).length < 2 ^ (prefixWord ++ tailWord_7016211).sum := by decide
  have hdescent : baseEnd_7016211 < baseStart_7016211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016222 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7016222 : Nat := 118140960795 + 7016222 * 2 ^ 59
def prefixEnd_7016222 : Nat := 4983230072969 + 3 ^ 40 * 7016222 * 2
def baseEnd_7016222 : Nat := 3602694264649953232857989

theorem tailTrace_7016222 : CollatzResearch.WordTrace tailWord_7016222 prefixEnd_7016222 3602694264649953232857989 := by
  unfold tailWord_7016222
  simp only [CollatzResearch.WordTrace]
  refine ⟨31987829948429180520392365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170601759724955629442092613 31987829948429180520392365)
  ·
    refine ⟨11995436230660942695147137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31987829948429180520392365 11995436230660942695147137)
    ·
      refine ⟨8996577172995707021360353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11995436230660942695147137 8996577172995707021360353)
      ·
        refine ⟨6747432879746780266020265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8996577172995707021360353 6747432879746780266020265)
        ·
          refine ⟨5060574659810085199515199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6747432879746780266020265 5060574659810085199515199)
          ·
            refine ⟨7590861989715127799272799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060574659810085199515199 7590861989715127799272799)
            ·
              refine ⟨11386292984572691698909199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590861989715127799272799 11386292984572691698909199)
              ·
                refine ⟨17079439476859037548363799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11386292984572691698909199 17079439476859037548363799)
                ·
                  refine ⟨25619159215288556322545699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17079439476859037548363799 25619159215288556322545699)
                  ·
                    refine ⟨38428738822932834483818549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25619159215288556322545699 38428738822932834483818549)
                    ·
                      refine ⟨3602694264649953232857989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38428738822932834483818549 3602694264649953232857989)
                      ·
                        rfl

theorem cell23_7016222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7016222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016222 prefixEnd_7016222 := by exact prefixLift 7016222
  have htrace : WordTrace (prefixWord ++ tailWord_7016222) baseStart_7016222 baseEnd_7016222 := by
    simpa [prefixWord, tailWord_7016222, baseEnd_7016222] using wordTrace_append hprefix tailTrace_7016222
  have hstable : (prefixWord ++ tailWord_7016222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016222).length < 2 ^ (prefixWord ++ tailWord_7016222).sum := by decide
  have hdescent : baseEnd_7016222 < baseStart_7016222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016264 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 7]
def baseStart_7016264 : Nat := 118140960795 + 7016264 * 2 ^ 59
def prefixEnd_7016264 : Nat := 4983230072969 + 3 ^ 40 * 7016264 * 2
def baseEnd_7016264 : Nat := 400301758981938007614755

theorem tailTrace_7016264 : CollatzResearch.WordTrace tailWord_7016264 prefixEnd_7016264 400301758981938007614755 := by
  unfold tailWord_7016264
  simp only [CollatzResearch.WordTrace]
  refine ⟨127952085726640642668083923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170602780968854190224111897 127952085726640642668083923)
  ·
    refine ⟨191928128589960964002125885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127952085726640642668083923 191928128589960964002125885)
    ·
      refine ⟨71973048221235361500797207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191928128589960964002125885 71973048221235361500797207)
      ·
        refine ⟨107959572331853042251195811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71973048221235361500797207 107959572331853042251195811)
        ·
          refine ⟨161939358497779563376793717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107959572331853042251195811 161939358497779563376793717)
          ·
            refine ⟨15181814859166834066574411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161939358497779563376793717 15181814859166834066574411)
            ·
              refine ⟨22772722288750251099861617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15181814859166834066574411 22772722288750251099861617)
              ·
                refine ⟨17079541716562688324896213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22772722288750251099861617 17079541716562688324896213)
                ·
                  refine ⟨400301758981938007614755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17079541716562688324896213 400301758981938007614755)
                  ·
                    rfl

theorem cell23_7016264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 7].length) (baseStart_7016264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016264 prefixEnd_7016264 := by exact prefixLift 7016264
  have htrace : WordTrace (prefixWord ++ tailWord_7016264) baseStart_7016264 baseEnd_7016264 := by
    simpa [prefixWord, tailWord_7016264, baseEnd_7016264] using wordTrace_append hprefix tailTrace_7016264
  have hstable : (prefixWord ++ tailWord_7016264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016264).length < 2 ^ (prefixWord ++ tailWord_7016264).sum := by decide
  have hdescent : baseEnd_7016264 < baseStart_7016264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016281 : List Nat := [1, 2, 1, 2, 2, 3, 4, 3, 5]
def baseStart_7016281 : Nat := 118140960795 + 7016281 * 2 ^ 59
def prefixEnd_7016281 : Nat := 4983230072969 + 3 ^ 40 * 7016281 * 2
def baseEnd_7016281 : Nat := 400302728889840944668913

theorem tailTrace_7016281 : CollatzResearch.WordTrace tailWord_7016281 prefixEnd_7016281 400302728889840944668913 := by
  unfold tailWord_7016281
  simp only [CollatzResearch.WordTrace]
  refine ⟨255904791494219697239536697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170603194329479798159691131 255904791494219697239536697)
  ·
    refine ⟨191928593620664772929652523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255904791494219697239536697 191928593620664772929652523)
    ·
      refine ⟨287892890430997159394478785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191928593620664772929652523 287892890430997159394478785)
      ·
        refine ⟨215919667823247869545859089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287892890430997159394478785 215919667823247869545859089)
        ·
          refine ⟨161939750867435902159394317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215919667823247869545859089 161939750867435902159394317)
          ·
            refine ⟨60727406575288463309772869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161939750867435902159394317 60727406575288463309772869)
            ·
              refine ⟨11386388732866586870582413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60727406575288463309772869 11386388732866586870582413)
              ·
                refine ⟨4269895774824970076468405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11386388732866586870582413 4269895774824970076468405)
                ·
                  refine ⟨400302728889840944668913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4269895774824970076468405 400302728889840944668913)
                  ·
                    rfl

theorem cell23_7016281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 5].length) (baseStart_7016281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016281 prefixEnd_7016281 := by exact prefixLift 7016281
  have htrace : WordTrace (prefixWord ++ tailWord_7016281) baseStart_7016281 baseEnd_7016281 := by
    simpa [prefixWord, tailWord_7016281, baseEnd_7016281] using wordTrace_append hprefix tailTrace_7016281
  have hstable : (prefixWord ++ tailWord_7016281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016281).length < 2 ^ (prefixWord ++ tailWord_7016281).sum := by decide
  have hdescent : baseEnd_7016281 < baseStart_7016281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016292 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 2, 2, 2]
def baseStart_7016292 : Nat := 118140960795 + 7016292 * 2 ^ 59
def prefixEnd_7016292 : Nat := 4983230072969 + 3 ^ 40 * 7016292 * 2
def baseEnd_7016292 : Nat := 3602730208295767958982667

theorem tailTrace_7016292 : CollatzResearch.WordTrace tailWord_7016292 prefixEnd_7016292 3602730208295767958982667 := by
  unfold tailWord_7016292
  simp only [CollatzResearch.WordTrace]
  refine ⟨127952596348589923059093565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170603461798119897412124753 127952596348589923059093565)
  ·
    refine ⟨47982223630721221147160087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127952596348589923059093565 47982223630721221147160087)
    ·
      refine ⟨71973335446081831720740131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47982223630721221147160087 71973335446081831720740131)
      ·
        refine ⟨107960003169122747581110197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71973335446081831720740131 107960003169122747581110197)
        ·
          refine ⟨10121250297105257585729081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107960003169122747581110197 10121250297105257585729081)
          ·
            refine ⟨7590937722828943189296811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10121250297105257585729081 7590937722828943189296811)
            ·
              refine ⟨11386406584243414783945217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590937722828943189296811 11386406584243414783945217)
              ·
                refine ⟨8539804938182561087958913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11386406584243414783945217 8539804938182561087958913)
                ·
                  refine ⟨6404853703636920815969185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8539804938182561087958913 6404853703636920815969185)
                  ·
                    refine ⟨4803640277727690611976889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6404853703636920815969185 4803640277727690611976889)
                    ·
                      refine ⟨3602730208295767958982667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803640277727690611976889 3602730208295767958982667)
                      ·
                        rfl

theorem cell23_7016292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_7016292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016292 prefixEnd_7016292 := by exact prefixLift 7016292
  have htrace : WordTrace (prefixWord ++ tailWord_7016292) baseStart_7016292 baseEnd_7016292 := by
    simpa [prefixWord, tailWord_7016292, baseEnd_7016292] using wordTrace_append hprefix tailTrace_7016292
  have hstable : (prefixWord ++ tailWord_7016292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016292).length < 2 ^ (prefixWord ++ tailWord_7016292).sum := by decide
  have hdescent : baseEnd_7016292 < baseStart_7016292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016298 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 7]
def baseStart_7016298 : Nat := 118140960795 + 7016298 * 2 ^ 59
def prefixEnd_7016298 : Nat := 4983230072969 + 3 ^ 40 * 7016298 * 2
def baseEnd_7016298 : Nat := 400303698797743881723071

theorem tailTrace_7016298 : CollatzResearch.WordTrace tailWord_7016298 prefixEnd_7016298 400303698797743881723071 := by
  unfold tailWord_7016298
  simp only [CollatzResearch.WordTrace]
  refine ⟨63976352883789527285726387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170603607690105406095270365 63976352883789527285726387)
  ·
    refine ⟨95964529325684290928589581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63976352883789527285726387 95964529325684290928589581)
    ·
      refine ⟨35986698497131609098221093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95964529325684290928589581 35986698497131609098221093)
      ·
        refine ⟨6747505968212176705916455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35986698497131609098221093 6747505968212176705916455)
        ·
          refine ⟨10121258952318265058874683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747505968212176705916455 10121258952318265058874683)
          ·
            refine ⟨15181888428477397588312025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10121258952318265058874683 15181888428477397588312025)
            ·
              refine ⟨11386416321358048191234019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15181888428477397588312025 11386416321358048191234019)
              ·
                refine ⟨17079624482037072286851029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11386416321358048191234019 17079624482037072286851029)
                ·
                  refine ⟨400303698797743881723071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17079624482037072286851029 400303698797743881723071)
                  ·
                    rfl

theorem cell23_7016298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_7016298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016298 prefixEnd_7016298 := by exact prefixLift 7016298
  have htrace : WordTrace (prefixWord ++ tailWord_7016298) baseStart_7016298 baseEnd_7016298 := by
    simpa [prefixWord, tailWord_7016298, baseEnd_7016298] using wordTrace_append hprefix tailTrace_7016298
  have hstable : (prefixWord ++ tailWord_7016298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016298).length < 2 ^ (prefixWord ++ tailWord_7016298).sum := by decide
  have hdescent : baseEnd_7016298 < baseStart_7016298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016301 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_7016301 : Nat := 118140960795 + 7016301 * 2 ^ 59
def prefixEnd_7016301 : Nat := 4983230072969 + 3 ^ 40 * 7016301 * 2
def baseEnd_7016301 : Nat := 3602734829621658423770125

theorem tailTrace_7016301 : CollatzResearch.WordTrace tailWord_7016301 prefixEnd_7016301 3602734829621658423770125 := by
  unfold tailWord_7016301
  simp only [CollatzResearch.WordTrace]
  refine ⟨255905520954147240655264757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170603680636098160436843171 255905520954147240655264757)
  ·
    refine ⟨23991142589451303811431071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255905520954147240655264757 23991142589451303811431071)
    ·
      refine ⟨35986713884176955717146607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23991142589451303811431071 35986713884176955717146607)
      ·
        refine ⟨53980070826265433575719911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35986713884176955717146607 53980070826265433575719911)
        ·
          refine ⟨80970106239398150363579867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53980070826265433575719911 80970106239398150363579867)
          ·
            refine ⟨121455159359097225545369801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80970106239398150363579867 121455159359097225545369801)
            ·
              refine ⟨91091369519322919159027351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121455159359097225545369801 91091369519322919159027351)
              ·
                refine ⟨136637054278984378738541027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91091369519322919159027351 136637054278984378738541027)
                ·
                  refine ⟨204955581418476568107811541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136637054278984378738541027 204955581418476568107811541)
                  ·
                    refine ⟨4803646439495544565026833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 204955581418476568107811541 4803646439495544565026833)
                    ·
                      refine ⟨3602734829621658423770125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803646439495544565026833 3602734829621658423770125)
                      ·
                        rfl

theorem cell23_7016301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_7016301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016301 prefixEnd_7016301 := by exact prefixLift 7016301
  have htrace : WordTrace (prefixWord ++ tailWord_7016301) baseStart_7016301 baseEnd_7016301 := by
    simpa [prefixWord, tailWord_7016301, baseEnd_7016301] using wordTrace_append hprefix tailTrace_7016301
  have hstable : (prefixWord ++ tailWord_7016301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016301).length < 2 ^ (prefixWord ++ tailWord_7016301).sum := by decide
  have hdescent : baseEnd_7016301 < baseStart_7016301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016314 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_7016314 : Nat := 118140960795 + 7016314 * 2 ^ 59
def prefixEnd_7016314 : Nat := 4983230072969 + 3 ^ 40 * 7016314 * 2
def baseEnd_7016314 : Nat := 3602741504870166872907565

theorem tailTrace_7016314 : CollatzResearch.WordTrace tailWord_7016314 prefixEnd_7016314 3602741504870166872907565 := by
  unfold tailWord_7016314
  simp only [CollatzResearch.WordTrace]
  refine ⟨63976498775775035968871999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170603996735400095916991997 63976498775775035968871999)
  ·
    refine ⟨95964748163662553953307999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63976498775775035968871999 95964748163662553953307999)
    ·
      refine ⟨143947122245493830929961999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95964748163662553953307999 143947122245493830929961999)
      ·
        refine ⟨215920683368240746394942999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143947122245493830929961999 215920683368240746394942999)
        ·
          refine ⟨323881025052361119592414499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215920683368240746394942999 323881025052361119592414499)
          ·
            refine ⟨485821537578541679388621749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323881025052361119592414499 485821537578541679388621749)
            ·
              refine ⟨45545769147988282442683289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 485821537578541679388621749 45545769147988282442683289)
              ·
                refine ⟨34159326860991211832012467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45545769147988282442683289 34159326860991211832012467)
                ·
                  refine ⟨51238990291486817748018701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34159326860991211832012467 51238990291486817748018701)
                  ·
                    refine ⟨19214621359307556655507013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51238990291486817748018701 19214621359307556655507013)
                    ·
                      refine ⟨3602741504870166872907565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19214621359307556655507013 3602741504870166872907565)
                      ·
                        rfl

theorem cell23_7016314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_7016314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016314 prefixEnd_7016314 := by exact prefixLift 7016314
  have htrace : WordTrace (prefixWord ++ tailWord_7016314) baseStart_7016314 baseEnd_7016314 := by
    simpa [prefixWord, tailWord_7016314, baseEnd_7016314] using wordTrace_append hprefix tailTrace_7016314
  have hstable : (prefixWord ++ tailWord_7016314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016314).length < 2 ^ (prefixWord ++ tailWord_7016314).sum := by decide
  have hdescent : baseEnd_7016314 < baseStart_7016314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016348 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7016348 : Nat := 118140960795 + 7016348 * 2 ^ 59
def prefixEnd_7016348 : Nat := 4983230072969 + 3 ^ 40 * 7016348 * 2
def baseEnd_7016348 : Nat := 3602758963212419739882409

theorem tailTrace_7016348 : CollatzResearch.WordTrace tailWord_7016348 prefixEnd_7016348 3602758963212419739882409 := by
  unfold tailWord_7016348
  simp only [CollatzResearch.WordTrace]
  refine ⟨127953617592488483841112849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170604823456651311788150465 127953617592488483841112849)
  ·
    refine ⟨95965213194366362880834637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127953617592488483841112849 95965213194366362880834637)
    ·
      refine ⟨35986954947887386080312989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95965213194366362880834637 35986954947887386080312989)
      ·
        refine ⟨13495108105457769780117371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35986954947887386080312989 13495108105457769780117371)
        ·
          refine ⟨20242662158186654670176057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13495108105457769780117371 20242662158186654670176057)
          ·
            refine ⟨15181996618639991002632043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20242662158186654670176057 15181996618639991002632043)
            ·
              refine ⟨22772994927959986503948065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15181996618639991002632043 22772994927959986503948065)
              ·
                refine ⟨17079746195969989877961049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22772994927959986503948065 17079746195969989877961049)
                ·
                  refine ⟨12809809646977492408470787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17079746195969989877961049 12809809646977492408470787)
                  ·
                    refine ⟨19214714470466238612706181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12809809646977492408470787 19214714470466238612706181)
                    ·
                      refine ⟨3602758963212419739882409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19214714470466238612706181 3602758963212419739882409)
                      ·
                        rfl

theorem cell23_7016348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7016348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016348 prefixEnd_7016348 := by exact prefixLift 7016348
  have htrace : WordTrace (prefixWord ++ tailWord_7016348) baseStart_7016348 baseEnd_7016348 := by
    simpa [prefixWord, tailWord_7016348, baseEnd_7016348] using wordTrace_append hprefix tailTrace_7016348
  have hstable : (prefixWord ++ tailWord_7016348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016348).length < 2 ^ (prefixWord ++ tailWord_7016348).sum := by decide
  have hdescent : baseEnd_7016348 < baseStart_7016348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016408 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 2, 3, 2]
def baseStart_7016408 : Nat := 118140960795 + 7016408 * 2 ^ 59
def prefixEnd_7016408 : Nat := 4983230072969 + 3 ^ 40 * 7016408 * 2
def baseEnd_7016408 : Nat := 3602789772051689505132133

theorem tailTrace_7016408 : CollatzResearch.WordTrace tailWord_7016408 prefixEnd_7016408 3602789772051689505132133 := by
  unfold tailWord_7016408
  simp only [CollatzResearch.WordTrace]
  refine ⟨127954711782379798964704939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170606282376506398619606585 127954711782379798964704939)
  ·
    refine ⟨191932067673569698447057409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127954711782379798964704939 191932067673569698447057409)
    ·
      refine ⟨143949050755177273835293057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191932067673569698447057409 143949050755177273835293057)
      ·
        refine ⟨107961788066382955376469793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143949050755177273835293057 107961788066382955376469793)
        ·
          refine ⟨80971341049787216532352345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107961788066382955376469793 80971341049787216532352345)
          ·
            refine ⟨60728505787340412399264259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80971341049787216532352345 60728505787340412399264259)
            ·
              refine ⟨91092758681010618598896389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60728505787340412399264259 91092758681010618598896389)
              ·
                refine ⟨17079892252689490987293073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91092758681010618598896389 17079892252689490987293073)
                ·
                  refine ⟨12809919189517118240469805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17079892252689490987293073 12809919189517118240469805)
                  ·
                    refine ⟨4803719696068919340176177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12809919189517118240469805 4803719696068919340176177)
                    ·
                      refine ⟨3602789772051689505132133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803719696068919340176177 3602789772051689505132133)
                      ·
                        rfl

theorem cell23_7016408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_7016408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016408 prefixEnd_7016408 := by exact prefixLift 7016408
  have htrace : WordTrace (prefixWord ++ tailWord_7016408) baseStart_7016408 baseEnd_7016408 := by
    simpa [prefixWord, tailWord_7016408, baseEnd_7016408] using wordTrace_append hprefix tailTrace_7016408
  have hstable : (prefixWord ++ tailWord_7016408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016408).length < 2 ^ (prefixWord ++ tailWord_7016408).sum := by decide
  have hdescent : baseEnd_7016408 < baseStart_7016408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016409 : List Nat := [1, 2, 1, 2, 7, 1, 2, 2, 1, 4]
def baseStart_7016409 : Nat := 118140960795 + 7016409 * 2 ^ 59
def prefixEnd_7016409 : Nat := 4983230072969 + 3 ^ 40 * 7016409 * 2
def baseEnd_7016409 : Nat := 1200930095177448000406543

theorem tailTrace_7016409 : CollatzResearch.WordTrace tailWord_7016409 prefixEnd_7016409 1200930095177448000406543 := by
  unfold tailWord_7016409
  simp only [CollatzResearch.WordTrace]
  refine ⟨255909460037755975100196281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170606306691837316733464187 255909460037755975100196281)
  ·
    refine ⟨191932095028316981325147211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255909460037755975100196281 191932095028316981325147211)
    ·
      refine ⟨287898142542475471987720817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191932095028316981325147211 287898142542475471987720817)
      ·
        refine ⟨215923606906856603990790613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287898142542475471987720817 215923606906856603990790613)
        ·
          refine ⟨5060709536879451656034155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 215923606906856603990790613 5060709536879451656034155)
          ·
            refine ⟨7591064305319177484051233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060709536879451656034155 7591064305319177484051233)
            ·
              refine ⟨5693298228989383113038425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7591064305319177484051233 5693298228989383113038425)
              ·
                refine ⟨4269973671742037334778819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5693298228989383113038425 4269973671742037334778819)
                ·
                  refine ⟨6404960507613056002168229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269973671742037334778819 6404960507613056002168229)
                  ·
                    refine ⟨1200930095177448000406543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6404960507613056002168229 1200930095177448000406543)
                    ·
                      rfl

theorem cell23_7016409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 1, 4].length) (baseStart_7016409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016409 prefixEnd_7016409 := by exact prefixLift 7016409
  have htrace : WordTrace (prefixWord ++ tailWord_7016409) baseStart_7016409 baseEnd_7016409 := by
    simpa [prefixWord, tailWord_7016409, baseEnd_7016409] using wordTrace_append hprefix tailTrace_7016409
  have hstable : (prefixWord ++ tailWord_7016409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016409).length < 2 ^ (prefixWord ++ tailWord_7016409).sum := by decide
  have hdescent : baseEnd_7016409 < baseStart_7016409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016431 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 1, 6]
def baseStart_7016431 : Nat := 118140960795 + 7016431 * 2 ^ 59
def prefixEnd_7016431 : Nat := 4983230072969 + 3 ^ 40 * 7016431 * 2
def baseEnd_7016431 : Nat := 1200933860702247638381509

theorem tailTrace_7016431 : CollatzResearch.WordTrace tailWord_7016431 prefixEnd_7016431 1200933860702247638381509 := by
  unfold tailWord_7016431
  simp only [CollatzResearch.WordTrace]
  refine ⟨255910262443676272857497147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170606841629117515238331431 255910262443676272857497147)
  ·
    refine ⟨383865393665514409286245721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255910262443676272857497147 383865393665514409286245721)
    ·
      refine ⟨287899045249135806964684291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383865393665514409286245721 287899045249135806964684291)
      ·
        refine ⟨431848567873703710447026437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287899045249135806964684291 431848567873703710447026437)
        ·
          refine ⟨80971606476319445708817457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431848567873703710447026437 80971606476319445708817457)
          ·
            refine ⟨60728704857239584281613093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80971606476319445708817457 60728704857239584281613093)
            ·
              refine ⟨11386632160732422052802455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60728704857239584281613093 11386632160732422052802455)
              ·
                refine ⟨17079948241098633079203683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11386632160732422052802455 17079948241098633079203683)
                ·
                  refine ⟨25619922361647949618805525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17079948241098633079203683 25619922361647949618805525)
                  ·
                    refine ⟨1200933860702247638381509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25619922361647949618805525 1200933860702247638381509)
                    ·
                      rfl

theorem cell23_7016431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 6].length) (baseStart_7016431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016431 prefixEnd_7016431 := by exact prefixLift 7016431
  have htrace : WordTrace (prefixWord ++ tailWord_7016431) baseStart_7016431 baseEnd_7016431 := by
    simpa [prefixWord, tailWord_7016431, baseEnd_7016431] using wordTrace_append hprefix tailTrace_7016431
  have hstable : (prefixWord ++ tailWord_7016431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016431).length < 2 ^ (prefixWord ++ tailWord_7016431).sum := by decide
  have hdescent : baseEnd_7016431 < baseStart_7016431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016455 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 1, 1, 4]
def baseStart_7016455 : Nat := 118140960795 + 7016455 * 2 ^ 59
def prefixEnd_7016455 : Nat := 4983230072969 + 3 ^ 40 * 7016455 * 2
def baseEnd_7016455 : Nat := 3602813905642450821244417

theorem tailTrace_7016455 : CollatzResearch.WordTrace tailWord_7016455 prefixEnd_7016455 3602813905642450821244417 := by
  unfold tailWord_7016455
  simp only [CollatzResearch.WordTrace]
  refine ⟨255911137795589324956370819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170607425197059549970913879 255911137795589324956370819)
  ·
    refine ⟨383866706693383987434556229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255911137795589324956370819 383866706693383987434556229)
    ·
      refine ⟨71975007505009497643979293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383866706693383987434556229 71975007505009497643979293)
      ·
        refine ⟨26990627814378561616492235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71975007505009497643979293 26990627814378561616492235)
        ·
          refine ⟨40485941721567842424738353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26990627814378561616492235 40485941721567842424738353)
          ·
            refine ⟨30364456291175881818553765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40485941721567842424738353 30364456291175881818553765)
            ·
              refine ⟨5693335554595477840978831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30364456291175881818553765 5693335554595477840978831)
              ·
                refine ⟨8540003331893216761468247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5693335554595477840978831 8540003331893216761468247)
                ·
                  refine ⟨12810004997839825142202371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8540003331893216761468247 12810004997839825142202371)
                  ·
                    refine ⟨19215007496759737713303557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12810004997839825142202371 19215007496759737713303557)
                    ·
                      refine ⟨3602813905642450821244417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19215007496759737713303557 3602813905642450821244417)
                      ·
                        rfl

theorem cell23_7016455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_7016455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016455 prefixEnd_7016455 := by exact prefixLift 7016455
  have htrace : WordTrace (prefixWord ++ tailWord_7016455) baseStart_7016455 baseEnd_7016455 := by
    simpa [prefixWord, tailWord_7016455, baseEnd_7016455] using wordTrace_append hprefix tailTrace_7016455
  have hstable : (prefixWord ++ tailWord_7016455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016455).length < 2 ^ (prefixWord ++ tailWord_7016455).sum := by decide
  have hdescent : baseEnd_7016455 < baseStart_7016455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016472 : List Nat := [2, 1, 2, 3, 2, 1, 1, 6, 1, 2, 2]
def baseStart_7016472 : Nat := 118140960795 + 7016472 * 2 ^ 59
def prefixEnd_7016472 : Nat := 4983230072969 + 3 ^ 40 * 7016472 * 2
def baseEnd_7016472 : Nat := 3602822634813577254731839

theorem tailTrace_7016472 : CollatzResearch.WordTrace tailWord_7016472 prefixEnd_7016472 3602822634813577254731839 := by
  unfold tailWord_7016472
  simp only [CollatzResearch.WordTrace]
  refine ⟨127955878918263868429869835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170607838557685157906493113 127955878918263868429869835)
  ·
    refine ⟨191933818377395802644804753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127955878918263868429869835 191933818377395802644804753)
    ·
      refine ⟨143950363783046851983603565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191933818377395802644804753 143950363783046851983603565)
      ·
        refine ⟨53981386418642569493851337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143950363783046851983603565 53981386418642569493851337)
        ·
          refine ⟨40486039813981927120388503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53981386418642569493851337 40486039813981927120388503)
          ·
            refine ⟨60729059720972890680582755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40486039813981927120388503 60729059720972890680582755)
            ·
              refine ⟨91093589581459336020874133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60729059720972890680582755 91093589581459336020874133)
              ·
                refine ⟨4270012011630906375978475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91093589581459336020874133 4270012011630906375978475)
                ·
                  refine ⟨6405018017446359563967713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270012011630906375978475 6405018017446359563967713)
                  ·
                    refine ⟨4803763513084769672975785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6405018017446359563967713 4803763513084769672975785)
                    ·
                      refine ⟨3602822634813577254731839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803763513084769672975785 3602822634813577254731839)
                      ·
                        rfl

theorem cell23_7016472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_7016472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016472 prefixEnd_7016472 := by exact prefixLift 7016472
  have htrace : WordTrace (prefixWord ++ tailWord_7016472) baseStart_7016472 baseEnd_7016472 := by
    simpa [prefixWord, tailWord_7016472, baseEnd_7016472] using wordTrace_append hprefix tailTrace_7016472
  have hstable : (prefixWord ++ tailWord_7016472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016472).length < 2 ^ (prefixWord ++ tailWord_7016472).sum := by decide
  have hdescent : baseEnd_7016472 < baseStart_7016472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016501 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_7016501 : Nat := 118140960795 + 7016501 * 2 ^ 59
def prefixEnd_7016501 : Nat := 4983230072969 + 3 ^ 40 * 7016501 * 2
def baseEnd_7016501 : Nat := 3602837525752557641269205

theorem tailTrace_7016501 : CollatzResearch.WordTrace tailWord_7016501 prefixEnd_7016501 3602837525752557641269205 := by
  unfold tailWord_7016501
  simp only [CollatzResearch.WordTrace]
  refine ⟨255912815553422674812545357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170608543702281783208363571 255912815553422674812545357)
  ·
    refine ⟨95967305832533503054704509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255912815553422674812545357 95967305832533503054704509)
    ·
      refine ⟨35987739687200063645514191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95967305832533503054704509 35987739687200063645514191)
      ·
        refine ⟨53981609530800095468271287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35987739687200063645514191 53981609530800095468271287)
        ·
          refine ⟨80972414296200143202406931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53981609530800095468271287 80972414296200143202406931)
          ·
            refine ⟨121458621444300214803610397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80972414296200143202406931 121458621444300214803610397)
            ·
              refine ⟨45546983041612580551353899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121458621444300214803610397 45546983041612580551353899)
              ·
                refine ⟨68320474562418870827030849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45546983041612580551353899 68320474562418870827030849)
                ·
                  refine ⟨51240355921814153120273137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68320474562418870827030849 51240355921814153120273137)
                  ·
                    refine ⟨38430266941360614840204853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51240355921814153120273137 38430266941360614840204853)
                    ·
                      refine ⟨3602837525752557641269205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38430266941360614840204853 3602837525752557641269205)
                      ·
                        rfl

theorem cell23_7016501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_7016501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016501 prefixEnd_7016501 := by exact prefixLift 7016501
  have htrace : WordTrace (prefixWord ++ tailWord_7016501) baseStart_7016501 baseEnd_7016501 := by
    simpa [prefixWord, tailWord_7016501, baseEnd_7016501] using wordTrace_append hprefix tailTrace_7016501
  have hstable : (prefixWord ++ tailWord_7016501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016501).length < 2 ^ (prefixWord ++ tailWord_7016501).sum := by decide
  have hdescent : baseEnd_7016501 < baseStart_7016501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016551 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 9]
def baseStart_7016551 : Nat := 118140960795 + 7016551 * 2 ^ 59
def prefixEnd_7016551 : Nat := 4983230072969 + 3 ^ 40 * 7016551 * 2
def baseEnd_7016551 : Nat := 400318133309475827293775

theorem tailTrace_7016551 : CollatzResearch.WordTrace tailWord_7016551 prefixEnd_7016551 400318133309475827293775 := by
  unfold tailWord_7016551
  simp only [CollatzResearch.WordTrace]
  refine ⟨255914639203241533351865507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170609759468827688901243671 255914639203241533351865507)
  ·
    refine ⟨383871958804862300027798261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255914639203241533351865507 383871958804862300027798261)
    ·
      refine ⟨35987996137955840627606087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 383871958804862300027798261 35987996137955840627606087)
      ·
        refine ⟨53981994206933760941409131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35987996137955840627606087 53981994206933760941409131)
        ·
          refine ⟨80972991310400641412113697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53981994206933760941409131 80972991310400641412113697)
          ·
            refine ⟨60729743482800481059085273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80972991310400641412113697 60729743482800481059085273)
            ·
              refine ⟨45547307612100360794313955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60729743482800481059085273 45547307612100360794313955)
              ·
                refine ⟨68320961418150541191470933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45547307612100360794313955 68320961418150541191470933)
                ·
                  refine ⟨400318133309475827293775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68320961418150541191470933 400318133309475827293775)
                  ·
                    rfl

theorem cell23_7016551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 9].length) (baseStart_7016551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016551 prefixEnd_7016551 := by exact prefixLift 7016551
  have htrace : WordTrace (prefixWord ++ tailWord_7016551) baseStart_7016551 baseEnd_7016551 := by
    simpa [prefixWord, tailWord_7016551, baseEnd_7016551] using wordTrace_append hprefix tailTrace_7016551
  have hstable : (prefixWord ++ tailWord_7016551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016551).length < 2 ^ (prefixWord ++ tailWord_7016551).sum := by decide
  have hdescent : baseEnd_7016551 < baseStart_7016551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016568 : List Nat := [2, 1, 2, 1, 1, 1, 3, 7, 5]
def baseStart_7016568 : Nat := 118140960795 + 7016568 * 2 ^ 59
def prefixEnd_7016568 : Nat := 4983230072969 + 3 ^ 40 * 7016568 * 2
def baseEnd_7016568 : Nat := 400319103217378764347933

theorem tailTrace_7016568 : CollatzResearch.WordTrace tailWord_7016568 prefixEnd_7016568 400319103217378764347933 := by
  unfold tailWord_7016568
  simp only [CollatzResearch.WordTrace]
  refine ⟨127957629622089972627617179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170610172829453296836822905 127957629622089972627617179)
  ·
    refine ⟨191936444433134958941425769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127957629622089972627617179 191936444433134958941425769)
    ·
      refine ⟨143952333324851219206069327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191936444433134958941425769 143952333324851219206069327)
      ·
        refine ⟨215928499987276828809103991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143952333324851219206069327 215928499987276828809103991)
        ·
          refine ⟨323892749980915243213655987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215928499987276828809103991 323892749980915243213655987)
          ·
            refine ⟨485839124971372864820483981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323892749980915243213655987 485839124971372864820483981)
            ·
              refine ⟨182189671864264824307681493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485839124971372864820483981 182189671864264824307681493)
              ·
                refine ⟨4270070434318706819711285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 182189671864264824307681493 4270070434318706819711285)
                ·
                  refine ⟨400319103217378764347933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4270070434318706819711285 400319103217378764347933)
                  ·
                    rfl

theorem cell23_7016568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 5].length) (baseStart_7016568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016568 prefixEnd_7016568 := by exact prefixLift 7016568
  have htrace : WordTrace (prefixWord ++ tailWord_7016568) baseStart_7016568 baseEnd_7016568 := by
    simpa [prefixWord, tailWord_7016568, baseEnd_7016568] using wordTrace_append hprefix tailTrace_7016568
  have hstable : (prefixWord ++ tailWord_7016568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016568).length < 2 ^ (prefixWord ++ tailWord_7016568).sum := by decide
  have hdescent : baseEnd_7016568 < baseStart_7016568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016615 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 1, 7]
def baseStart_7016615 : Nat := 118140960795 + 7016615 * 2 ^ 59
def prefixEnd_7016615 : Nat := 4983230072969 + 3 ^ 40 * 7016615 * 2
def baseEnd_7016615 : Nat := 1200965354182390065081227

theorem tailTrace_7016615 : CollatzResearch.WordTrace tailWord_7016615 prefixEnd_7016615 1200965354182390065081227 := by
  unfold tailWord_7016615
  simp only [CollatzResearch.WordTrace]
  refine ⟨255916973475009672282195299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170611315650006448188130199 255916973475009672282195299)
  ·
    refine ⟨383875460212514508423292949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255916973475009672282195299 383875460212514508423292949)
    ·
      refine ⟨17994162197461617582341857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 383875460212514508423292949 17994162197461617582341857)
      ·
        refine ⟨13495621648096213186756393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17994162197461617582341857 13495621648096213186756393)
        ·
          refine ⟨10121716236072159890067295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13495621648096213186756393 10121716236072159890067295)
          ·
            refine ⟨15182574354108239835100943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10121716236072159890067295 15182574354108239835100943)
            ·
              refine ⟨22773861531162359752651415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15182574354108239835100943 22773861531162359752651415)
              ·
                refine ⟨34160792296743539628977123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22773861531162359752651415 34160792296743539628977123)
                ·
                  refine ⟨51241188445115309443465685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34160792296743539628977123 51241188445115309443465685)
                  ·
                    refine ⟨1200965354182390065081227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51241188445115309443465685 1200965354182390065081227)
                    ·
                      rfl

theorem cell23_7016615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_7016615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016615 prefixEnd_7016615 := by exact prefixLift 7016615
  have htrace : WordTrace (prefixWord ++ tailWord_7016615) baseStart_7016615 baseEnd_7016615 := by
    simpa [prefixWord, tailWord_7016615, baseEnd_7016615] using wordTrace_append hprefix tailTrace_7016615
  have hstable : (prefixWord ++ tailWord_7016615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016615).length < 2 ^ (prefixWord ++ tailWord_7016615).sum := by decide
  have hdescent : baseEnd_7016615 < baseStart_7016615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016679 : List Nat := [1, 1, 5, 3, 1, 1, 3, 3, 1, 4]
def baseStart_7016679 : Nat := 118140960795 + 7016679 * 2 ^ 59
def prefixEnd_7016679 : Nat := 4983230072969 + 3 ^ 40 * 7016679 * 2
def baseEnd_7016679 : Nat := 1200976308436352648281129

theorem tailTrace_7016679 : CollatzResearch.WordTrace tailWord_7016679 prefixEnd_7016679 1200976308436352648281129 := by
  unfold tailWord_7016679
  simp only [CollatzResearch.WordTrace]
  refine ⟨255919307746777811212525091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170612871831185207475016727 255919307746777811212525091)
  ·
    refine ⟨383878961620166716818787637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255919307746777811212525091 383878961620166716818787637)
    ·
      refine ⟨35988652651890629701761341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 383878961620166716818787637 35988652651890629701761341)
      ·
        refine ⟨13495744744458986138160503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35988652651890629701761341 13495744744458986138160503)
        ·
          refine ⟨20243617116688479207240755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13495744744458986138160503 20243617116688479207240755)
          ·
            refine ⟨30365425675032718810861133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20243617116688479207240755 30365425675032718810861133)
            ·
              refine ⟨11387034628137269554072925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30365425675032718810861133 11387034628137269554072925)
              ·
                refine ⟨4270137985551476082777347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11387034628137269554072925 4270137985551476082777347)
                ·
                  refine ⟨6405206978327214124166021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270137985551476082777347 6405206978327214124166021)
                  ·
                    refine ⟨1200976308436352648281129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6405206978327214124166021 1200976308436352648281129)
                    ·
                      rfl

theorem cell23_7016679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_7016679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016679 prefixEnd_7016679 := by exact prefixLift 7016679
  have htrace : WordTrace (prefixWord ++ tailWord_7016679) baseStart_7016679 baseEnd_7016679 := by
    simpa [prefixWord, tailWord_7016679, baseEnd_7016679] using wordTrace_append hprefix tailTrace_7016679
  have hstable : (prefixWord ++ tailWord_7016679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016679).length < 2 ^ (prefixWord ++ tailWord_7016679).sum := by decide
  have hdescent : baseEnd_7016679 < baseStart_7016679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016725 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 2, 6, 2]
def baseStart_7016725 : Nat := 118140960795 + 7016725 * 2 ^ 59
def prefixEnd_7016725 : Nat := 4983230072969 + 3 ^ 40 * 7016725 * 2
def baseEnd_7016725 : Nat := 3602952545419164764868175

theorem tailTrace_7016725 : CollatzResearch.WordTrace tailWord_7016725 prefixEnd_7016725 3602952545419164764868175 := by
  unfold tailWord_7016725
  simp only [CollatzResearch.WordTrace]
  refine ⟨255920985504611161068699629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170613990336407440712466419 255920985504611161068699629)
  ·
    refine ⟨95970369564229185400762361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255920985504611161068699629 95970369564229185400762361)
    ·
      refine ⟨71977777173171889050571771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95970369564229185400762361 71977777173171889050571771)
      ·
        refine ⟨107966665759757833575857657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71977777173171889050571771 107966665759757833575857657)
        ·
          refine ⟨80974999319818375181893243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107966665759757833575857657 80974999319818375181893243)
          ·
            refine ⟨121462498979727562772839865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80974999319818375181893243 121462498979727562772839865)
            ·
              refine ⟨91096874234795672079629899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121462498979727562772839865 91096874234795672079629899)
              ·
                refine ⟨136645311352193508119444849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91096874234795672079629899 136645311352193508119444849)
                ·
                  refine ⟨102483983514145131089583637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136645311352193508119444849 102483983514145131089583637)
                  ·
                    refine ⟨4803936727225553019824233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102483983514145131089583637 4803936727225553019824233)
                    ·
                      refine ⟨3602952545419164764868175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4803936727225553019824233 3602952545419164764868175)
                      ·
                        rfl

theorem cell23_7016725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_7016725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016725 prefixEnd_7016725 := by exact prefixLift 7016725
  have htrace : WordTrace (prefixWord ++ tailWord_7016725) baseStart_7016725 baseEnd_7016725 := by
    simpa [prefixWord, tailWord_7016725, baseEnd_7016725] using wordTrace_append hprefix tailTrace_7016725
  have hstable : (prefixWord ++ tailWord_7016725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016725).length < 2 ^ (prefixWord ++ tailWord_7016725).sum := by decide
  have hdescent : baseEnd_7016725 < baseStart_7016725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016735 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 1, 6]
def baseStart_7016735 : Nat := 118140960795 + 7016735 * 2 ^ 59
def prefixEnd_7016735 : Nat := 4983230072969 + 3 ^ 40 * 7016735 * 2
def baseEnd_7016735 : Nat := 1200985893408569908581043

theorem tailTrace_7016735 : CollatzResearch.WordTrace tailWord_7016735 prefixEnd_7016735 1200985893408569908581043 := by
  unfold tailWord_7016735
  simp only [CollatzResearch.WordTrace]
  refine ⟨255921350234574932776563659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170614233489716621851042439 255921350234574932776563659)
  ·
    refine ⟨383882025351862399164845489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255921350234574932776563659 383882025351862399164845489)
    ·
      refine ⟨287911519013896799373634117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383882025351862399164845489 287911519013896799373634117)
      ·
        refine ⟨53983409815105649882556397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287911519013896799373634117 53983409815105649882556397)
        ·
          refine ⟨20243778680664618705958649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53983409815105649882556397 20243778680664618705958649)
          ·
            refine ⟨15182834010498464029468987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20243778680664618705958649 15182834010498464029468987)
            ·
              refine ⟨22774251015747696044203481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15182834010498464029468987 22774251015747696044203481)
              ·
                refine ⟨17080688261810772033152611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22774251015747696044203481 17080688261810772033152611)
                ·
                  refine ⟨25621032392716158049728917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17080688261810772033152611 25621032392716158049728917)
                  ·
                    refine ⟨1200985893408569908581043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25621032392716158049728917 1200985893408569908581043)
                    ·
                      rfl

theorem cell23_7016735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_7016735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016735 prefixEnd_7016735 := by exact prefixLift 7016735
  have htrace : WordTrace (prefixWord ++ tailWord_7016735) baseStart_7016735 baseEnd_7016735 := by
    simpa [prefixWord, tailWord_7016735, baseEnd_7016735] using wordTrace_append hprefix tailTrace_7016735
  have hstable : (prefixWord ++ tailWord_7016735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016735).length < 2 ^ (prefixWord ++ tailWord_7016735).sum := by decide
  have hdescent : baseEnd_7016735 < baseStart_7016735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016753 : List Nat := [1, 2, 2, 3, 4, 2, 2, 2, 1, 1, 3]
def baseStart_7016753 : Nat := 118140960795 + 7016753 * 2 ^ 59
def prefixEnd_7016753 : Nat := 4983230072969 + 3 ^ 40 * 7016753 * 2
def baseEnd_7016753 : Nat := 3602966922877490655318047

theorem tailTrace_7016753 : CollatzResearch.WordTrace tailWord_7016753 prefixEnd_7016753 3602966922877490655318047 := by
  unfold tailWord_7016753
  simp only [CollatzResearch.WordTrace]
  refine ⟨255922006748509721850718913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170614671165673147900479275 255922006748509721850718913)
  ·
    refine ⟨191941505061382291388039185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255922006748509721850718913 191941505061382291388039185)
    ·
      refine ⟨143956128796036718541029389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191941505061382291388039185 143956128796036718541029389)
      ·
        refine ⟨53983548298513769452886021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143956128796036718541029389 53983548298513769452886021)
        ·
          refine ⟨10121915305971331772416129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53983548298513769452886021 10121915305971331772416129)
          ·
            refine ⟨7591436479478498829312097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10121915305971331772416129 7591436479478498829312097)
            ·
              refine ⟨5693577359608874121984073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7591436479478498829312097 5693577359608874121984073)
              ·
                refine ⟨4270183019706655591488055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5693577359608874121984073 4270183019706655591488055)
                ·
                  refine ⟨6405274529559983387232083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270183019706655591488055 6405274529559983387232083)
                  ·
                    refine ⟨9607911794339975080848125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6405274529559983387232083 9607911794339975080848125)
                    ·
                      refine ⟨3602966922877490655318047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9607911794339975080848125 3602966922877490655318047)
                      ·
                        rfl

theorem cell23_7016753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_7016753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016753 prefixEnd_7016753 := by exact prefixLift 7016753
  have htrace : WordTrace (prefixWord ++ tailWord_7016753) baseStart_7016753 baseEnd_7016753 := by
    simpa [prefixWord, tailWord_7016753, baseEnd_7016753] using wordTrace_append hprefix tailTrace_7016753
  have hstable : (prefixWord ++ tailWord_7016753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016753).length < 2 ^ (prefixWord ++ tailWord_7016753).sum := by decide
  have hdescent : baseEnd_7016753 < baseStart_7016753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016796 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_7016796 : Nat := 118140960795 + 7016796 * 2 ^ 59
def prefixEnd_7016796 : Nat := 4983230072969 + 3 ^ 40 * 7016796 * 2
def baseEnd_7016796 : Nat := 3602989002545633987080349

theorem tailTrace_7016796 : CollatzResearch.WordTrace tailWord_7016796 prefixEnd_7016796 3602989002545633987080349 := by
  unfold tailWord_7016796
  simp only [CollatzResearch.WordTrace]
  refine ⟨127961787543676970097267121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170615716724902626796356161 127961787543676970097267121)
  ·
    refine ⟨95971340657757727572950341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127961787543676970097267121 95971340657757727572950341)
    ·
      refine ⟨17994626373329573919928189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95971340657757727572950341 17994626373329573919928189)
      ·
        refine ⟨6747984889998590219973071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17994626373329573919928189 6747984889998590219973071)
        ·
          refine ⟨10121977334997885329959607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747984889998590219973071 10121977334997885329959607)
          ·
            refine ⟨15182966002496827994939411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10121977334997885329959607 15182966002496827994939411)
            ·
              refine ⟨22774449003745241992409117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15182966002496827994939411 22774449003745241992409117)
              ·
                refine ⟨8540418376404465747153419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22774449003745241992409117 8540418376404465747153419)
                ·
                  refine ⟨12810627564606698620730129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8540418376404465747153419 12810627564606698620730129)
                  ·
                    refine ⟨9607970673455023965547597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12810627564606698620730129 9607970673455023965547597)
                    ·
                      refine ⟨3602989002545633987080349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9607970673455023965547597 3602989002545633987080349)
                      ·
                        rfl

theorem cell23_7016796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_7016796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016796 prefixEnd_7016796 := by exact prefixLift 7016796
  have htrace : WordTrace (prefixWord ++ tailWord_7016796) baseStart_7016796 baseEnd_7016796 := by
    simpa [prefixWord, tailWord_7016796, baseEnd_7016796] using wordTrace_append hprefix tailTrace_7016796
  have hstable : (prefixWord ++ tailWord_7016796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016796).length < 2 ^ (prefixWord ++ tailWord_7016796).sum := by decide
  have hdescent : baseEnd_7016796 < baseStart_7016796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016866 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_7016866 : Nat := 118140960795 + 7016866 * 2 ^ 59
def prefixEnd_7016866 : Nat := 4983230072969 + 3 ^ 40 * 7016866 * 2
def baseEnd_7016866 : Nat := 3603024946191448713205027

theorem tailTrace_7016866 : CollatzResearch.WordTrace tailWord_7016866 prefixEnd_7016866 3603024946191448713205027 := by
  unfold tailWord_7016866
  simp only [CollatzResearch.WordTrace]
  refine ⟨63981532049275085537395613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170617418798066894766388301 63981532049275085537395613)
  ·
    refine ⟨23993074518478157076523355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63981532049275085537395613 23993074518478157076523355)
    ·
      refine ⟨35989611777717235614785033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23993074518478157076523355 35989611777717235614785033)
      ·
        refine ⟨26992208833287926711088775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35989611777717235614785033 26992208833287926711088775)
        ·
          refine ⟨40488313249931890066633163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26992208833287926711088775 40488313249931890066633163)
          ·
            refine ⟨60732469874897835099949745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40488313249931890066633163 60732469874897835099949745)
            ·
              refine ⟨45549352406173376324962309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60732469874897835099949745 45549352406173376324962309)
              ·
                refine ⟨8540503576157508060930433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45549352406173376324962309 8540503576157508060930433)
                ·
                  refine ⟨6405377682118131045697825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8540503576157508060930433 6405377682118131045697825)
                  ·
                    refine ⟨4804033261588598284273369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6405377682118131045697825 4804033261588598284273369)
                    ·
                      refine ⟨3603024946191448713205027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4804033261588598284273369 3603024946191448713205027)
                      ·
                        rfl

theorem cell23_7016866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_7016866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016866 prefixEnd_7016866 := by exact prefixLift 7016866
  have htrace : WordTrace (prefixWord ++ tailWord_7016866) baseStart_7016866 baseEnd_7016866 := by
    simpa [prefixWord, tailWord_7016866, baseEnd_7016866] using wordTrace_append hprefix tailTrace_7016866
  have hstable : (prefixWord ++ tailWord_7016866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016866).length < 2 ^ (prefixWord ++ tailWord_7016866).sum := by decide
  have hdescent : baseEnd_7016866 < baseStart_7016866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016905 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_7016905 : Nat := 118140960795 + 7016905 * 2 ^ 59
def prefixEnd_7016905 : Nat := 4983230072969 + 3 ^ 40 * 7016905 * 2
def baseEnd_7016905 : Nat := 3603044971936974060617347

theorem tailTrace_7016905 : CollatzResearch.WordTrace tailWord_7016905 prefixEnd_7016905 3603044971936974060617347 := by
  unfold tailWord_7016905
  simp only [CollatzResearch.WordTrace]
  refine ⟨255927550643959051810252169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170618367095972701206834779 255927550643959051810252169)
  ·
    refine ⟨191945662982969288857689127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255927550643959051810252169 191945662982969288857689127)
    ·
      refine ⟨287918494474453933286533691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191945662982969288857689127 287918494474453933286533691)
      ·
        refine ⟨431877741711680899929800537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287918494474453933286533691 431877741711680899929800537)
        ·
          refine ⟨323908306283760674947350403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431877741711680899929800537 323908306283760674947350403)
          ·
            refine ⟨485862459425641012421025605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323908306283760674947350403 485862459425641012421025605)
            ·
              refine ⟨91099211142307689828942301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 485862459425641012421025605 91099211142307689828942301)
              ·
                refine ⟨34162204178365383685853363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91099211142307689828942301 34162204178365383685853363)
                ·
                  refine ⟨51243306267548075528780045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34162204178365383685853363 51243306267548075528780045)
                  ·
                    refine ⟨19216239850330528323292517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51243306267548075528780045 19216239850330528323292517)
                    ·
                      refine ⟨3603044971936974060617347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19216239850330528323292517 3603044971936974060617347)
                      ·
                        rfl

theorem cell23_7016905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_7016905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016905 prefixEnd_7016905 := by exact prefixLift 7016905
  have htrace : WordTrace (prefixWord ++ tailWord_7016905) baseStart_7016905 baseEnd_7016905 := by
    simpa [prefixWord, tailWord_7016905, baseEnd_7016905] using wordTrace_append hprefix tailTrace_7016905
  have hstable : (prefixWord ++ tailWord_7016905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016905).length < 2 ^ (prefixWord ++ tailWord_7016905).sum := by decide
  have hdescent : baseEnd_7016905 < baseStart_7016905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016922 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_7016922 : Nat := 118140960795 + 7016922 * 2 ^ 59
def prefixEnd_7016922 : Nat := 4983230072969 + 3 ^ 40 * 7016922 * 2
def baseEnd_7016922 : Nat := 3603053701108100494104769

theorem tailTrace_7016922 : CollatzResearch.WordTrace tailWord_7016922 prefixEnd_7016922 3603053701108100494104769 := by
  unfold tailWord_7016922
  simp only [CollatzResearch.WordTrace]
  refine ⟨63982042671224365928405255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170618780456598309142414013 63982042671224365928405255)
  ·
    refine ⟨95973064006836548892607883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63982042671224365928405255 95973064006836548892607883)
    ·
      refine ⟨143959596010254823338911825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95973064006836548892607883 143959596010254823338911825)
      ·
        refine ⟨107969697007691117504183869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143959596010254823338911825 107969697007691117504183869)
        ·
          refine ⟨40488636377884169064068951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107969697007691117504183869 40488636377884169064068951)
          ·
            refine ⟨60732954566826253596103427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40488636377884169064068951 60732954566826253596103427)
            ·
              refine ⟨91099431850239380394155141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60732954566826253596103427 91099431850239380394155141)
              ·
                refine ⟨17081143471919883823904089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91099431850239380394155141 17081143471919883823904089)
                ·
                  refine ⟨12810857603939912867928067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17081143471919883823904089 12810857603939912867928067)
                  ·
                    refine ⟨19216286405909869301892101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12810857603939912867928067 19216286405909869301892101)
                    ·
                      refine ⟨3603053701108100494104769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19216286405909869301892101 3603053701108100494104769)
                      ·
                        rfl

theorem cell23_7016922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_7016922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016922 prefixEnd_7016922 := by exact prefixLift 7016922
  have htrace : WordTrace (prefixWord ++ tailWord_7016922) baseStart_7016922 baseEnd_7016922 := by
    simpa [prefixWord, tailWord_7016922, baseEnd_7016922] using wordTrace_append hprefix tailTrace_7016922
  have hstable : (prefixWord ++ tailWord_7016922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016922).length < 2 ^ (prefixWord ++ tailWord_7016922).sum := by decide
  have hdescent : baseEnd_7016922 < baseStart_7016922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016973 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_7016973 : Nat := 118140960795 + 7016973 * 2 ^ 59
def prefixEnd_7016973 : Nat := 4983230072969 + 3 ^ 40 * 7016973 * 2
def baseEnd_7016973 : Nat := 3603079888621479794567035

theorem tailTrace_7016973 : CollatzResearch.WordTrace tailWord_7016973 prefixEnd_7016973 3603079888621479794567035 := by
  unfold tailWord_7016973
  simp only [CollatzResearch.WordTrace]
  refine ⟨255930030807712699423727573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170620020538475132949151715 255930030807712699423727573)
  ·
    refine ⟨5998360097055766392743615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 255930030807712699423727573 5998360097055766392743615)
    ·
      refine ⟨8997540145583649589115423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998360097055766392743615 8997540145583649589115423)
      ·
        refine ⟨13496310218375474383673135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8997540145583649589115423 13496310218375474383673135)
        ·
          refine ⟨20244465327563211575509703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13496310218375474383673135 20244465327563211575509703)
          ·
            refine ⟨30366697991344817363264555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20244465327563211575509703 30366697991344817363264555)
            ·
              refine ⟨45550046987017226044896833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30366697991344817363264555 45550046987017226044896833)
              ·
                refine ⟨34162535240262919533672625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45550046987017226044896833 34162535240262919533672625)
                ·
                  refine ⟨25621901430197189650254469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34162535240262919533672625 25621901430197189650254469)
                  ·
                    refine ⟨4804106518161973059422713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25621901430197189650254469 4804106518161973059422713)
                    ·
                      refine ⟨3603079888621479794567035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4804106518161973059422713 3603079888621479794567035)
                      ·
                        rfl

theorem cell23_7016973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_7016973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016973 prefixEnd_7016973 := by exact prefixLift 7016973
  have htrace : WordTrace (prefixWord ++ tailWord_7016973) baseStart_7016973 baseEnd_7016973 := by
    simpa [prefixWord, tailWord_7016973, baseEnd_7016973] using wordTrace_append hprefix tailTrace_7016973
  have hstable : (prefixWord ++ tailWord_7016973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016973).length < 2 ^ (prefixWord ++ tailWord_7016973).sum := by decide
  have hdescent : baseEnd_7016973 < baseStart_7016973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016985 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_7016985 : Nat := 118140960795 + 7016985 * 2 ^ 59
def prefixEnd_7016985 : Nat := 4983230072969 + 3 ^ 40 * 7016985 * 2
def baseEnd_7016985 : Nat := 3603086050389333747616979

theorem tailTrace_7016985 : CollatzResearch.WordTrace tailWord_7016985 prefixEnd_7016985 3603086050389333747616979 := by
  unfold tailWord_7016985
  simp only [CollatzResearch.WordTrace]
  refine ⟨255930468483669225473164409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170620312322446150315442939 255930468483669225473164409)
  ·
    refine ⟨191947851362751919104873307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255930468483669225473164409 191947851362751919104873307)
    ·
      refine ⟨287921777044127878657309961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191947851362751919104873307 287921777044127878657309961)
      ·
        refine ⟨215941332783095908992982471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287921777044127878657309961 215941332783095908992982471)
        ·
          refine ⟨323911999174643863489473707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215941332783095908992982471 323911999174643863489473707)
          ·
            refine ⟨485867998761965795234210561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323911999174643863489473707 485867998761965795234210561)
            ·
              refine ⟨364400999071474346425657921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485867998761965795234210561 364400999071474346425657921)
              ·
                refine ⟨273300749303605759819243441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364400999071474346425657921 273300749303605759819243441)
                ·
                  refine ⟨204975561977704319864432581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273300749303605759819243441 204975561977704319864432581)
                  ·
                    refine ⟨38432917870819559974581109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204975561977704319864432581 38432917870819559974581109)
                    ·
                      refine ⟨3603086050389333747616979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38432917870819559974581109 3603086050389333747616979)
                      ·
                        rfl

theorem cell23_7016985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_7016985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7016985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7016985 prefixEnd_7016985 := by exact prefixLift 7016985
  have htrace : WordTrace (prefixWord ++ tailWord_7016985) baseStart_7016985 baseEnd_7016985 := by
    simpa [prefixWord, tailWord_7016985, baseEnd_7016985] using wordTrace_append hprefix tailTrace_7016985
  have hstable : (prefixWord ++ tailWord_7016985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016985).length < 2 ^ (prefixWord ++ tailWord_7016985).sum := by decide
  have hdescent : baseEnd_7016985 < baseStart_7016985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017029 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 4]
def baseStart_7017029 : Nat := 118140960795 + 7017029 * 2 ^ 59
def prefixEnd_7017029 : Nat := 4983230072969 + 3 ^ 40 * 7017029 * 2
def baseEnd_7017029 : Nat := 3603108643538131575466777

theorem tailTrace_7017029 : CollatzResearch.WordTrace tailWord_7017029 prefixEnd_7017029 3603108643538131575466777 := by
  unfold tailWord_7017029
  simp only [CollatzResearch.WordTrace]
  refine ⟨255932073295509820987766141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170621382197006547325177427 255932073295509820987766141)
  ·
    refine ⟨95974527485816182870412303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255932073295509820987766141 95974527485816182870412303)
    ·
      refine ⟨143961791228724274305618455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95974527485816182870412303 143961791228724274305618455)
      ·
        refine ⟨215942686843086411458427683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143961791228724274305618455 215942686843086411458427683)
        ·
          refine ⟨323914030264629617187641525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215942686843086411458427683 323914030264629617187641525)
          ·
            refine ⟨30366940337309026611341393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 323914030264629617187641525 30366940337309026611341393)
            ·
              refine ⟨22775205252981769958506045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30366940337309026611341393 22775205252981769958506045)
              ·
                refine ⟨8540701969868163734439767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22775205252981769958506045 8540701969868163734439767)
                ·
                  refine ⟨12811052954802245601659651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8540701969868163734439767 12811052954802245601659651)
                  ·
                    refine ⟨19216579432203368402489477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12811052954802245601659651 19216579432203368402489477)
                    ·
                      refine ⟨3603108643538131575466777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19216579432203368402489477 3603108643538131575466777)
                      ·
                        rfl

theorem cell23_7017029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_7017029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017029 prefixEnd_7017029 := by exact prefixLift 7017029
  have htrace : WordTrace (prefixWord ++ tailWord_7017029) baseStart_7017029 baseEnd_7017029 := by
    simpa [prefixWord, tailWord_7017029, baseEnd_7017029] using wordTrace_append hprefix tailTrace_7017029
  have hstable : (prefixWord ++ tailWord_7017029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017029).length < 2 ^ (prefixWord ++ tailWord_7017029).sum := by decide
  have hdescent : baseEnd_7017029 < baseStart_7017029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017035 : List Nat := [1, 1, 1, 1, 3, 1, 15]
def baseStart_7017035 : Nat := 118140960795 + 7017035 * 2 ^ 59
def prefixEnd_7017035 : Nat := 4983230072969 + 3 ^ 40 * 7017035 * 2
def baseEnd_7017035 : Nat := 44482860795334056197429

theorem tailTrace_7017035 : CollatzResearch.WordTrace tailWord_7017035 prefixEnd_7017035 44482860795334056197429 := by
  unfold tailWord_7017035
  simp only [CollatzResearch.WordTrace]
  refine ⟨255932292133488084012484559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170621528088992056008323039 255932292133488084012484559)
  ·
    refine ⟨383898438200232126018726839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255932292133488084012484559 383898438200232126018726839)
    ·
      refine ⟨575847657300348189028090259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383898438200232126018726839 575847657300348189028090259)
      ·
        refine ⟨863771485950522283542135389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575847657300348189028090259 863771485950522283542135389)
        ·
          refine ⟨323914307231445856328300771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 863771485950522283542135389 323914307231445856328300771)
          ·
            refine ⟨485871460847168784492451157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323914307231445856328300771 485871460847168784492451157)
            ·
              refine ⟨44482860795334056197429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 485871460847168784492451157 44482860795334056197429)
              ·
                rfl

theorem cell23_7017035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 15].length) (baseStart_7017035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017035 prefixEnd_7017035 := by exact prefixLift 7017035
  have htrace : WordTrace (prefixWord ++ tailWord_7017035) baseStart_7017035 baseEnd_7017035 := by
    simpa [prefixWord, tailWord_7017035, baseEnd_7017035] using wordTrace_append hprefix tailTrace_7017035
  have hstable : (prefixWord ++ tailWord_7017035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017035).length < 2 ^ (prefixWord ++ tailWord_7017035).sum := by decide
  have hdescent : baseEnd_7017035 < baseStart_7017035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017042 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_7017042 : Nat := 118140960795 + 7017042 * 2 ^ 59
def prefixEnd_7017042 : Nat := 4983230072969 + 3 ^ 40 * 7017042 * 2
def baseEnd_7017042 : Nat := 3603115318786640024604217

theorem tailTrace_7017042 : CollatzResearch.WordTrace tailWord_7017042 prefixEnd_7017042 3603115318786640024604217 := by
  unfold tailWord_7017042
  simp only [CollatzResearch.WordTrace]
  refine ⟨63983136861115681051997345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170621698296308482805326253 63983136861115681051997345)
  ·
    refine ⟨47987352645836760788998009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63983136861115681051997345 47987352645836760788998009)
    ·
      refine ⟨35990514484377570591748507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47987352645836760788998009 35990514484377570591748507)
      ·
        refine ⟨53985771726566355887622761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35990514484377570591748507 53985771726566355887622761)
        ·
          refine ⟨40489328794924766915717071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53985771726566355887622761 40489328794924766915717071)
          ·
            refine ⟨60733993192387150373575607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40489328794924766915717071 60733993192387150373575607)
            ·
              refine ⟨91100989788580725560363411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60733993192387150373575607 91100989788580725560363411)
              ·
                refine ⟨136651484682871088340545117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91100989788580725560363411 136651484682871088340545117)
                ·
                  refine ⟨51244306756076658127704419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136651484682871088340545117 51244306756076658127704419)
                  ·
                    refine ⟨76866460134114987191556629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51244306756076658127704419 76866460134114987191556629)
                    ·
                      refine ⟨3603115318786640024604217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76866460134114987191556629 3603115318786640024604217)
                      ·
                        rfl

theorem cell23_7017042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_7017042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017042 prefixEnd_7017042 := by exact prefixLift 7017042
  have htrace : WordTrace (prefixWord ++ tailWord_7017042) baseStart_7017042 baseEnd_7017042 := by
    simpa [prefixWord, tailWord_7017042, baseEnd_7017042] using wordTrace_append hprefix tailTrace_7017042
  have hstable : (prefixWord ++ tailWord_7017042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017042).length < 2 ^ (prefixWord ++ tailWord_7017042).sum := by decide
  have hdescent : baseEnd_7017042 < baseStart_7017042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017056 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 2, 4]
def baseStart_7017056 : Nat := 118140960795 + 7017056 * 2 ^ 59
def prefixEnd_7017056 : Nat := 4983230072969 + 3 ^ 40 * 7017056 * 2
def baseEnd_7017056 : Nat := 1201040835838600989943051

theorem tailTrace_7017056 : CollatzResearch.WordTrace tailWord_7017056 prefixEnd_7017056 1201040835838600989943051 := by
  unfold tailWord_7017056
  simp only [CollatzResearch.WordTrace]
  refine ⟨127966529033206002299499511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170622038710941336399332681 127966529033206002299499511)
  ·
    refine ⟨191949793549809003449249267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127966529033206002299499511 191949793549809003449249267)
    ·
      refine ⟨287924690324713505173873901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191949793549809003449249267 287924690324713505173873901)
      ·
        refine ⟨107971758871767564440202713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287924690324713505173873901 107971758871767564440202713)
        ·
          refine ⟨80978819153825673330152035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107971758871767564440202713 80978819153825673330152035)
          ·
            refine ⟨121468228730738509995228053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80978819153825673330152035 121468228730738509995228053)
            ·
              refine ⟨5693823221753367656026315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121468228730738509995228053 5693823221753367656026315)
              ·
                refine ⟨8540734832630051484039473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5693823221753367656026315 8540734832630051484039473)
                ·
                  refine ⟨6405551124472538613029605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8540734832630051484039473 6405551124472538613029605)
                  ·
                    refine ⟨1201040835838600989943051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6405551124472538613029605 1201040835838600989943051)
                    ·
                      rfl

theorem cell23_7017056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 2, 4].length) (baseStart_7017056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017056 prefixEnd_7017056 := by exact prefixLift 7017056
  have htrace : WordTrace (prefixWord ++ tailWord_7017056) baseStart_7017056 baseEnd_7017056 := by
    simpa [prefixWord, tailWord_7017056, baseEnd_7017056] using wordTrace_append hprefix tailTrace_7017056
  have hstable : (prefixWord ++ tailWord_7017056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017056).length < 2 ^ (prefixWord ++ tailWord_7017056).sum := by decide
  have hdescent : baseEnd_7017056 < baseStart_7017056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017079 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 6, 1, 3]
def baseStart_7017079 : Nat := 118140960795 + 7017079 * 2 ^ 59
def prefixEnd_7017079 : Nat := 4983230072969 + 3 ^ 40 * 7017079 * 2
def baseEnd_7017079 : Nat := 3603134317570856379841547

theorem tailTrace_7017079 : CollatzResearch.WordTrace tailWord_7017079 prefixEnd_7017079 3603134317570856379841547 := by
  unfold tailWord_7017079
  simp only [CollatzResearch.WordTrace]
  refine ⟨255933896945328679527086291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170622597963552453018057527 255933896945328679527086291)
  ·
    refine ⟨383900845417993019290629437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255933896945328679527086291 383900845417993019290629437)
    ·
      refine ⟨143962817031747382233986039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383900845417993019290629437 143962817031747382233986039)
      ·
        refine ⟨215944225547621073350979059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143962817031747382233986039 215944225547621073350979059)
        ·
          refine ⟨323916338321431610026468589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215944225547621073350979059 323916338321431610026468589)
          ·
            refine ⟨121468626870536853759925721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323916338321431610026468589 121468626870536853759925721)
            ·
              refine ⟨91101470152902640319944291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121468626870536853759925721 91101470152902640319944291)
              ·
                refine ⟨136652205229353960479916437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91101470152902640319944291 136652205229353960479916437)
                ·
                  refine ⟨6405572120125966897496083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136652205229353960479916437 6405572120125966897496083)
                  ·
                    refine ⟨9608358180188950346244125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6405572120125966897496083 9608358180188950346244125)
                    ·
                      refine ⟨3603134317570856379841547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9608358180188950346244125 3603134317570856379841547)
                      ·
                        rfl

theorem cell23_7017079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_7017079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017079 prefixEnd_7017079 := by exact prefixLift 7017079
  have htrace : WordTrace (prefixWord ++ tailWord_7017079) baseStart_7017079 baseEnd_7017079 := by
    simpa [prefixWord, tailWord_7017079, baseEnd_7017079] using wordTrace_append hprefix tailTrace_7017079
  have hstable : (prefixWord ++ tailWord_7017079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017079).length < 2 ^ (prefixWord ++ tailWord_7017079).sum := by decide
  have hdescent : baseEnd_7017079 < baseStart_7017079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017136 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 4, 2, 2]
def baseStart_7017136 : Nat := 118140960795 + 7017136 * 2 ^ 59
def prefixEnd_7017136 : Nat := 4983230072969 + 3 ^ 40 * 7017136 * 2
def baseEnd_7017136 : Nat := 3603163585968162656828785

theorem tailTrace_7017136 : CollatzResearch.WordTrace tailWord_7017136 prefixEnd_7017136 3603163585968162656828785 := by
  unfold tailWord_7017136
  simp only [CollatzResearch.WordTrace]
  refine ⟨127967987953061089130955631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170623983937414785507940841 127967987953061089130955631)
  ·
    refine ⟨191951981929591633696433447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127967987953061089130955631 191951981929591633696433447)
    ·
      refine ⟨287927972894387450544650171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191951981929591633696433447 287927972894387450544650171)
      ·
        refine ⟨431891959341581175816975257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287927972894387450544650171 431891959341581175816975257)
        ·
          refine ⟨323918969506185881862731443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431891959341581175816975257 323918969506185881862731443)
          ·
            refine ⟨485878454259278822794097165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323918969506185881862731443 485878454259278822794097165)
            ·
              refine ⟨182204420347229558547786437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485878454259278822794097165 182204420347229558547786437)
              ·
                refine ⟨34163328815105542227709957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182204420347229558547786437 34163328815105542227709957)
                ·
                  refine ⟨6405624152832289167695617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34163328815105542227709957 6405624152832289167695617)
                  ·
                    refine ⟨4804218114624216875771713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6405624152832289167695617 4804218114624216875771713)
                    ·
                      refine ⟨3603163585968162656828785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4804218114624216875771713 3603163585968162656828785)
                      ·
                        rfl

theorem cell23_7017136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4, 2, 2].length) (baseStart_7017136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017136 prefixEnd_7017136 := by exact prefixLift 7017136
  have htrace : WordTrace (prefixWord ++ tailWord_7017136) baseStart_7017136 baseEnd_7017136 := by
    simpa [prefixWord, tailWord_7017136, baseEnd_7017136] using wordTrace_append hprefix tailTrace_7017136
  have hstable : (prefixWord ++ tailWord_7017136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017136).length < 2 ^ (prefixWord ++ tailWord_7017136).sum := by decide
  have hdescent : baseEnd_7017136 < baseStart_7017136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017149 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_7017149 : Nat := 118140960795 + 7017149 * 2 ^ 59
def prefixEnd_7017149 : Nat := 4983230072969 + 3 ^ 40 * 7017149 * 2
def baseEnd_7017149 : Nat := 3603170261216671105966225

theorem tailTrace_7017149 : CollatzResearch.WordTrace tailWord_7017149 prefixEnd_7017149 3603170261216671105966225 := by
  unfold tailWord_7017149
  simp only [CollatzResearch.WordTrace]
  refine ⟨255936450055075081482134501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170624300036716720988089667 255936450055075081482134501)
  ·
    refine ⟨47988084385326577777900219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255936450055075081482134501 47988084385326577777900219)
    ·
      refine ⟨71982126577989866666850329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47988084385326577777900219 71982126577989866666850329)
      ·
        refine ⟨53986594933492400000137747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71982126577989866666850329 53986594933492400000137747)
        ·
          refine ⟨80979892400238600000206621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53986594933492400000137747 80979892400238600000206621)
          ·
            refine ⟨30367459650089475000077483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80979892400238600000206621 30367459650089475000077483)
            ·
              refine ⟨45551189475134212500116225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30367459650089475000077483 45551189475134212500116225)
              ·
                refine ⟨34163392106350659375087169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45551189475134212500116225 34163392106350659375087169)
                ·
                  refine ⟨25622544079762994531315377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34163392106350659375087169 25622544079762994531315377)
                  ·
                    refine ⟨19216908059822245898486533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25622544079762994531315377 19216908059822245898486533)
                    ·
                      refine ⟨3603170261216671105966225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19216908059822245898486533 3603170261216671105966225)
                      ·
                        rfl

theorem cell23_7017149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_7017149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017149 prefixEnd_7017149 := by exact prefixLift 7017149
  have htrace : WordTrace (prefixWord ++ tailWord_7017149) baseStart_7017149 baseEnd_7017149 := by
    simpa [prefixWord, tailWord_7017149, baseEnd_7017149] using wordTrace_append hprefix tailTrace_7017149
  have hstable : (prefixWord ++ tailWord_7017149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017149).length < 2 ^ (prefixWord ++ tailWord_7017149).sum := by decide
  have hdescent : baseEnd_7017149 < baseStart_7017149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017169 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 2, 3, 3]
def baseStart_7017169 : Nat := 118140960795 + 7017169 * 2 ^ 59
def prefixEnd_7017169 : Nat := 4983230072969 + 3 ^ 40 * 7017169 * 2
def baseEnd_7017169 : Nat := 3603180530829761027716133

theorem tailTrace_7017169 : CollatzResearch.WordTrace tailWord_7017169 prefixEnd_7017169 3603180530829761027716133 := by
  unfold tailWord_7017169
  simp only [CollatzResearch.WordTrace]
  refine ⟨255937179515002624897862561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170624786343335083265241707 255937179515002624897862561)
  ·
    refine ⟨191952884636251968673396921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255937179515002624897862561 191952884636251968673396921)
    ·
      refine ⟨143964663477188976505047691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191952884636251968673396921 143964663477188976505047691)
      ·
        refine ⟨215946995215783464757571537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143964663477188976505047691 215946995215783464757571537)
        ·
          refine ⟨161960246411837598568178653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215946995215783464757571537 161960246411837598568178653)
          ·
            refine ⟨60735092404439099463066995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161960246411837598568178653 60735092404439099463066995)
            ·
              refine ⟨91102638606658649194600493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60735092404439099463066995 91102638606658649194600493)
              ·
                refine ⟨34163489477496993447975185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91102638606658649194600493 34163489477496993447975185)
                ·
                  refine ⟨25622617108122745085981389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34163489477496993447975185 25622617108122745085981389)
                  ·
                    refine ⟨9608481415546029407243021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25622617108122745085981389 9608481415546029407243021)
                    ·
                      refine ⟨3603180530829761027716133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9608481415546029407243021 3603180530829761027716133)
                      ·
                        rfl

theorem cell23_7017169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_7017169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017169 prefixEnd_7017169 := by exact prefixLift 7017169
  have htrace : WordTrace (prefixWord ++ tailWord_7017169) baseStart_7017169 baseEnd_7017169 := by
    simpa [prefixWord, tailWord_7017169, baseEnd_7017169] using wordTrace_append hprefix tailTrace_7017169
  have hstable : (prefixWord ++ tailWord_7017169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017169).length < 2 ^ (prefixWord ++ tailWord_7017169).sum := by decide
  have hdescent : baseEnd_7017169 < baseStart_7017169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017170 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_7017170 : Nat := 118140960795 + 7017170 * 2 ^ 59
def prefixEnd_7017170 : Nat := 4983230072969 + 3 ^ 40 * 7017170 * 2
def baseEnd_7017170 : Nat := 3603181044310415523803629

theorem tailTrace_7017170 : CollatzResearch.WordTrace tailWord_7017170 prefixEnd_7017170 3603181044310415523803629 := by
  unfold tailWord_7017170
  simp only [CollatzResearch.WordTrace]
  refine ⟨63984303996999750517162241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170624810658666001379099309 63984303996999750517162241)
  ·
    refine ⟨47988227997749812887871681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63984303996999750517162241 47988227997749812887871681)
    ·
      refine ⟨35991170998312359665903761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47988227997749812887871681 35991170998312359665903761)
      ·
        refine ⟨26993378248734269749427821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35991170998312359665903761 26993378248734269749427821)
        ·
          refine ⟨10122516843275351156035433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26993378248734269749427821 10122516843275351156035433)
          ·
            refine ⟨7591887632456513367026575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10122516843275351156035433 7591887632456513367026575)
            ·
              refine ⟨11387831448684770050539863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7591887632456513367026575 11387831448684770050539863)
              ·
                refine ⟨17081747173027155075809795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11387831448684770050539863 17081747173027155075809795)
                ·
                  refine ⟨25622620759540732613714693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17081747173027155075809795 25622620759540732613714693)
                  ·
                    refine ⟨4804241392413887365071505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25622620759540732613714693 4804241392413887365071505)
                    ·
                      refine ⟨3603181044310415523803629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4804241392413887365071505 3603181044310415523803629)
                      ·
                        rfl

theorem cell23_7017170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_7017170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017170 prefixEnd_7017170 := by exact prefixLift 7017170
  have htrace : WordTrace (prefixWord ++ tailWord_7017170) baseStart_7017170 baseEnd_7017170 := by
    simpa [prefixWord, tailWord_7017170, baseEnd_7017170] using wordTrace_append hprefix tailTrace_7017170
  have hstable : (prefixWord ++ tailWord_7017170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017170).length < 2 ^ (prefixWord ++ tailWord_7017170).sum := by decide
  have hdescent : baseEnd_7017170 < baseStart_7017170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017189 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_7017189 : Nat := 118140960795 + 7017189 * 2 ^ 59
def prefixEnd_7017189 : Nat := 4983230072969 + 3 ^ 40 * 7017189 * 2
def baseEnd_7017189 : Nat := 1201063600147616983155347

theorem tailTrace_7017189 : CollatzResearch.WordTrace tailWord_7017189 prefixEnd_7017189 1201063600147616983155347 := by
  unfold tailWord_7017189
  simp only [CollatzResearch.WordTrace]
  refine ⟨255937908974930168313590621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170625272649953445542393747 255937908974930168313590621)
  ·
    refine ⟨95976715865598813117596483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255937908974930168313590621 95976715865598813117596483)
    ·
      refine ⟨143965073798398219676394725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95976715865598813117596483 143965073798398219676394725)
      ·
        refine ⟨26993451337199666189324011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143965073798398219676394725 26993451337199666189324011)
        ·
          refine ⟨40490177005799499283986017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26993451337199666189324011 40490177005799499283986017)
          ·
            refine ⟨30367632754349624462989513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40490177005799499283986017 30367632754349624462989513)
            ·
              refine ⟨22775724565762218347242135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30367632754349624462989513 22775724565762218347242135)
              ·
                refine ⟨34163586848643327520863203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22775724565762218347242135 34163586848643327520863203)
                ·
                  refine ⟨51245380272964991281294805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34163586848643327520863203 51245380272964991281294805)
                  ·
                    refine ⟨1201063600147616983155347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51245380272964991281294805 1201063600147616983155347)
                    ·
                      rfl

theorem cell23_7017189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_7017189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017189 prefixEnd_7017189 := by exact prefixLift 7017189
  have htrace : WordTrace (prefixWord ++ tailWord_7017189) baseStart_7017189 baseEnd_7017189 := by
    simpa [prefixWord, tailWord_7017189, baseEnd_7017189] using wordTrace_append hprefix tailTrace_7017189
  have hstable : (prefixWord ++ tailWord_7017189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017189).length < 2 ^ (prefixWord ++ tailWord_7017189).sum := by decide
  have hdescent : baseEnd_7017189 < baseStart_7017189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017206 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_7017206 : Nat := 118140960795 + 7017206 * 2 ^ 59
def prefixEnd_7017206 : Nat := 4983230072969 + 3 ^ 40 * 7017206 * 2
def baseEnd_7017206 : Nat := 1201066509871325794317821

theorem tailTrace_7017206 : CollatzResearch.WordTrace tailWord_7017206 prefixEnd_7017206 1201066509871325794317821 := by
  unfold tailWord_7017206
  simp only [CollatzResearch.WordTrace]
  refine ⟨15996158063491786263559967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170625686010579053477972981 15996158063491786263559967)
  ·
    refine ⟨23994237095237679395339951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15996158063491786263559967 23994237095237679395339951)
    ·
      refine ⟨35991355642856519093009927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23994237095237679395339951 35991355642856519093009927)
      ·
        refine ⟨53987033464284778639514891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35991355642856519093009927 53987033464284778639514891)
        ·
          refine ⟨80980550196427167959272337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53987033464284778639514891 80980550196427167959272337)
          ·
            refine ⟨60735412647320375969454253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80980550196427167959272337 60735412647320375969454253)
            ·
              refine ⟨22775779742745140988545345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60735412647320375969454253 22775779742745140988545345)
              ·
                refine ⟨17081834807058855741409009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22775779742745140988545345 17081834807058855741409009)
                ·
                  refine ⟨12811376105294141806056757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17081834807058855741409009 12811376105294141806056757)
                  ·
                    refine ⟨1201066509871325794317821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12811376105294141806056757 1201066509871325794317821)
                    ·
                      rfl

theorem cell23_7017206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_7017206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017206 prefixEnd_7017206 := by exact prefixLift 7017206
  have htrace : WordTrace (prefixWord ++ tailWord_7017206) baseStart_7017206 baseEnd_7017206 := by
    simpa [prefixWord, tailWord_7017206, baseEnd_7017206] using wordTrace_append hprefix tailTrace_7017206
  have hstable : (prefixWord ++ tailWord_7017206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017206).length < 2 ^ (prefixWord ++ tailWord_7017206).sum := by decide
  have hdescent : baseEnd_7017206 < baseStart_7017206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017226 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2]
def baseStart_7017226 : Nat := 118140960795 + 7017226 * 2 ^ 59
def prefixEnd_7017226 : Nat := 4983230072969 + 3 ^ 40 * 7017226 * 2
def baseEnd_7017226 : Nat := 3603209799227067304703371

theorem tailTrace_7017226 : CollatzResearch.WordTrace tailWord_7017226 prefixEnd_7017226 3603209799227067304703371 := by
  unfold tailWord_7017226
  simp only [CollatzResearch.WordTrace]
  refine ⟨63984814618949030908171883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170626172317197415755125021 63984814618949030908171883)
  ·
    refine ⟨95977221928423546362257825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63984814618949030908171883 95977221928423546362257825)
    ·
      refine ⟨71982916446317659771693369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95977221928423546362257825 71982916446317659771693369)
      ·
        refine ⟨53987187334738244828770027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71982916446317659771693369 53987187334738244828770027)
        ·
          refine ⟨80980781002107367243155041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53987187334738244828770027 80980781002107367243155041)
          ·
            refine ⟨60735585751580525432366281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80980781002107367243155041 60735585751580525432366281)
            ·
              refine ⟨45551689313685394074274711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60735585751580525432366281 45551689313685394074274711)
              ·
                refine ⟨68327533970528091111412067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45551689313685394074274711 68327533970528091111412067)
                ·
                  refine ⟨102491300955792136667118101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68327533970528091111412067 102491300955792136667118101)
                  ·
                    refine ⟨4804279732302756406271161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102491300955792136667118101 4804279732302756406271161)
                    ·
                      refine ⟨3603209799227067304703371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4804279732302756406271161 3603209799227067304703371)
                      ·
                        rfl

theorem cell23_7017226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_7017226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017226 prefixEnd_7017226 := by exact prefixLift 7017226
  have htrace : WordTrace (prefixWord ++ tailWord_7017226) baseStart_7017226 baseEnd_7017226 := by
    simpa [prefixWord, tailWord_7017226, baseEnd_7017226] using wordTrace_append hprefix tailTrace_7017226
  have hstable : (prefixWord ++ tailWord_7017226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017226).length < 2 ^ (prefixWord ++ tailWord_7017226).sum := by decide
  have hdescent : baseEnd_7017226 < baseStart_7017226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017253 : List Nat := [1, 3, 1, 2, 3, 1, 2, 5, 1, 4]
def baseStart_7017253 : Nat := 118140960795 + 7017253 * 2 ^ 59
def prefixEnd_7017253 : Nat := 4983230072969 + 3 ^ 40 * 7017253 * 2
def baseEnd_7017253 : Nat := 1201074554401579566355249

theorem tailTrace_7017253 : CollatzResearch.WordTrace tailWord_7017253 prefixEnd_7017253 1201074554401579566355249 := by
  unfold tailWord_7017253
  simp only [CollatzResearch.WordTrace]
  refine ⟨255940243246698307243920413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170626828831132204829280275 255940243246698307243920413)
  ·
    refine ⟨95977591217511865216470155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255940243246698307243920413 95977591217511865216470155)
    ·
      refine ⟨143966386826267797824705233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95977591217511865216470155 143966386826267797824705233)
      ·
        refine ⟨107974790119700848368528925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143966386826267797824705233 107974790119700848368528925)
        ·
          refine ⟨40490546294887818138198347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107974790119700848368528925 40490546294887818138198347)
          ·
            refine ⟨60735819442331727207297521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40490546294887818138198347 60735819442331727207297521)
            ·
              refine ⟨45551864581748795405473141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60735819442331727207297521 45551864581748795405473141)
              ·
                refine ⟨4270487304538949569263107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45551864581748795405473141 4270487304538949569263107)
                ·
                  refine ⟨6405730956808424353894661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270487304538949569263107 6405730956808424353894661)
                  ·
                    refine ⟨1201074554401579566355249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6405730956808424353894661 1201074554401579566355249)
                    ·
                      rfl

theorem cell23_7017253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_7017253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017253 prefixEnd_7017253 := by exact prefixLift 7017253
  have htrace : WordTrace (prefixWord ++ tailWord_7017253) baseStart_7017253 baseEnd_7017253 := by
    simpa [prefixWord, tailWord_7017253, baseEnd_7017253] using wordTrace_append hprefix tailTrace_7017253
  have hstable : (prefixWord ++ tailWord_7017253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017253).length < 2 ^ (prefixWord ++ tailWord_7017253).sum := by decide
  have hdescent : baseEnd_7017253 < baseStart_7017253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017266 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 6]
def baseStart_7017266 : Nat := 118140960795 + 7017266 * 2 ^ 59
def prefixEnd_7017266 : Nat := 4983230072969 + 3 ^ 40 * 7017266 * 2
def baseEnd_7017266 : Nat := 400358926494805238689243

theorem tailTrace_7017266 : CollatzResearch.WordTrace tailWord_7017266 prefixEnd_7017266 400358926494805238689243 := by
  unfold tailWord_7017266
  simp only [CollatzResearch.WordTrace]
  refine ⟨63985179348912802616035913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170627144930434140309429101 63985179348912802616035913)
  ·
    refine ⟨47988884511684601962026935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63985179348912802616035913 47988884511684601962026935)
    ·
      refine ⟨71983326767526902943040403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47988884511684601962026935 71983326767526902943040403)
      ·
        refine ⟨107974990151290354414560605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71983326767526902943040403 107974990151290354414560605)
        ·
          refine ⟨40490621306733882905460227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107974990151290354414560605 40490621306733882905460227)
          ·
            refine ⟨60735931960100824358190341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40490621306733882905460227 60735931960100824358190341)
            ·
              refine ⟨11387987242518904567160689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60735931960100824358190341 11387987242518904567160689)
              ·
                refine ⟨8540990431889178425370517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11387987242518904567160689 8540990431889178425370517)
                ·
                  refine ⟨400358926494805238689243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8540990431889178425370517 400358926494805238689243)
                  ·
                    rfl

theorem cell23_7017266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_7017266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017266 prefixEnd_7017266 := by exact prefixLift 7017266
  have htrace : WordTrace (prefixWord ++ tailWord_7017266) baseStart_7017266 baseEnd_7017266 := by
    simpa [prefixWord, tailWord_7017266, baseEnd_7017266] using wordTrace_append hprefix tailTrace_7017266
  have hstable : (prefixWord ++ tailWord_7017266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017266).length < 2 ^ (prefixWord ++ tailWord_7017266).sum := by decide
  have hdescent : baseEnd_7017266 < baseStart_7017266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017303 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 1, 5, 2]
def baseStart_7017303 : Nat := 118140960795 + 7017303 * 2 ^ 59
def prefixEnd_7017303 : Nat := 4983230072969 + 3 ^ 40 * 7017303 * 2
def baseEnd_7017303 : Nat := 3603249337237463503440517

theorem tailTrace_7017303 : CollatzResearch.WordTrace tailWord_7017303 prefixEnd_7017303 3603249337237463503440517 := by
  unfold tailWord_7017303
  simp only [CollatzResearch.WordTrace]
  refine ⟨255942066896517165783240563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170628044597678110522160375 255942066896517165783240563)
  ·
    refine ⟨383913100344775748674860845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255942066896517165783240563 383913100344775748674860845)
    ·
      refine ⟨143967412629290905753072817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383913100344775748674860845 143967412629290905753072817)
      ·
        refine ⟨107975559471968179314804613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143967412629290905753072817 107975559471968179314804613)
        ·
          refine ⟨20245417400994033621525865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107975559471968179314804613 20245417400994033621525865)
          ·
            refine ⟨15184063050745525216144399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20245417400994033621525865 15184063050745525216144399)
            ·
              refine ⟨22776094576118287824216599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15184063050745525216144399 22776094576118287824216599)
              ·
                refine ⟨34164141864177431736324899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22776094576118287824216599 34164141864177431736324899)
                ·
                  refine ⟨51246212796266147604487349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34164141864177431736324899 51246212796266147604487349)
                  ·
                    refine ⟨4804332449649951337920689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51246212796266147604487349 4804332449649951337920689)
                    ·
                      refine ⟨3603249337237463503440517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4804332449649951337920689 3603249337237463503440517)
                      ·
                        rfl

theorem cell23_7017303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_7017303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017303 prefixEnd_7017303 := by exact prefixLift 7017303
  have htrace : WordTrace (prefixWord ++ tailWord_7017303) baseStart_7017303 baseEnd_7017303 := by
    simpa [prefixWord, tailWord_7017303, baseEnd_7017303] using wordTrace_append hprefix tailTrace_7017303
  have hstable : (prefixWord ++ tailWord_7017303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017303).length < 2 ^ (prefixWord ++ tailWord_7017303).sum := by decide
  have hdescent : baseEnd_7017303 < baseStart_7017303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017336 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 3, 2, 3]
def baseStart_7017336 : Nat := 118140960795 + 7017336 * 2 ^ 59
def prefixEnd_7017336 : Nat := 4983230072969 + 3 ^ 40 * 7017336 * 2
def baseEnd_7017336 : Nat := 3603266282099061874327865

theorem tailTrace_7017336 : CollatzResearch.WordTrace tailWord_7017336 prefixEnd_7017336 3603266282099061874327865 := by
  unfold tailWord_7017336
  simp only [CollatzResearch.WordTrace]
  refine ⟨127971635252698806209595931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170628847003598408279461241 127971635252698806209595931)
  ·
    refine ⟨191957452879048209314393897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127971635252698806209595931 191957452879048209314393897)
    ·
      refine ⟨143968089659286156985795423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191957452879048209314393897 143968089659286156985795423)
      ·
        refine ⟨215952134488929235478693135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143968089659286156985795423 215952134488929235478693135)
        ·
          refine ⟨323928201733393853218039703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215952134488929235478693135 323928201733393853218039703)
          ·
            refine ⟨485892302600090779827059555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323928201733393853218039703 485892302600090779827059555)
            ·
              refine ⟨728838453900136169740589333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485892302600090779827059555 728838453900136169740589333)
              ·
                refine ⟨34164302526568882956590125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 728838453900136169740589333 34164302526568882956590125)
                ·
                  refine ⟨12811613447463331108721297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34164302526568882956590125 12811613447463331108721297)
                  ·
                    refine ⟨9608710085597498331540973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12811613447463331108721297 9608710085597498331540973)
                    ·
                      refine ⟨3603266282099061874327865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9608710085597498331540973 3603266282099061874327865)
                      ·
                        rfl

theorem cell23_7017336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_7017336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017336 prefixEnd_7017336 := by exact prefixLift 7017336
  have htrace : WordTrace (prefixWord ++ tailWord_7017336) baseStart_7017336 baseEnd_7017336 := by
    simpa [prefixWord, tailWord_7017336, baseEnd_7017336] using wordTrace_append hprefix tailTrace_7017336
  have hstable : (prefixWord ++ tailWord_7017336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017336).length < 2 ^ (prefixWord ++ tailWord_7017336).sum := by decide
  have hdescent : baseEnd_7017336 < baseStart_7017336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017353 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 1, 2, 3]
def baseStart_7017353 : Nat := 118140960795 + 7017353 * 2 ^ 59
def prefixEnd_7017353 : Nat := 4983230072969 + 3 ^ 40 * 7017353 * 2
def baseEnd_7017353 : Nat := 3603275011270188307815287

theorem tailTrace_7017353 : CollatzResearch.WordTrace tailWord_7017353 prefixEnd_7017353 3603275011270188307815287 := by
  unfold tailWord_7017353
  simp only [CollatzResearch.WordTrace]
  refine ⟨255943890546336024322560713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170629260364224016215040475 255943890546336024322560713)
  ·
    refine ⟨191957917909752018241920535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255943890546336024322560713 191957917909752018241920535)
    ·
      refine ⟨287936876864628027362880803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191957917909752018241920535 287936876864628027362880803)
      ·
        refine ⟨431905315296942041044321205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287936876864628027362880803 431905315296942041044321205)
        ·
          refine ⟨40491123309088316347905113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 431905315296942041044321205 40491123309088316347905113)
          ·
            refine ⟨30368342481816237260928835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40491123309088316347905113 30368342481816237260928835)
            ·
              refine ⟨45552513722724355891393253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30368342481816237260928835 45552513722724355891393253)
              ·
                refine ⟨8541096323010816729636235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45552513722724355891393253 8541096323010816729636235)
                ·
                  refine ⟨12811644484516225094454353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8541096323010816729636235 12811644484516225094454353)
                  ·
                    refine ⟨9608733363387168820840765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12811644484516225094454353 9608733363387168820840765)
                    ·
                      refine ⟨3603275011270188307815287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9608733363387168820840765 3603275011270188307815287)
                      ·
                        rfl

theorem cell23_7017353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 2, 3].length) (baseStart_7017353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017353 prefixEnd_7017353 := by exact prefixLift 7017353
  have htrace : WordTrace (prefixWord ++ tailWord_7017353) baseStart_7017353 baseEnd_7017353 := by
    simpa [prefixWord, tailWord_7017353, baseEnd_7017353] using wordTrace_append hprefix tailTrace_7017353
  have hstable : (prefixWord ++ tailWord_7017353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017353).length < 2 ^ (prefixWord ++ tailWord_7017353).sum := by decide
  have hdescent : baseEnd_7017353 < baseStart_7017353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017356 : List Nat := [2, 2, 1, 2, 1, 2, 6, 7]
def baseStart_7017356 : Nat := 118140960795 + 7017356 * 2 ^ 59
def prefixEnd_7017356 : Nat := 4983230072969 + 3 ^ 40 * 7017356 * 2
def baseEnd_7017356 : Nat := 133454687100450066521399

theorem tailTrace_7017356 : CollatzResearch.WordTrace tailWord_7017356 prefixEnd_7017356 133454687100450066521399 := by
  unfold tailWord_7017356
  simp only [CollatzResearch.WordTrace]
  refine ⟨127971999982662577917459961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170629333310216770556613281 127971999982662577917459961)
  ·
    refine ⟨95978999986996933438094971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127971999982662577917459961 95978999986996933438094971)
    ·
      refine ⟨143968499980495400157142457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95978999986996933438094971 143968499980495400157142457)
      ·
        refine ⟨107976374985371550117856843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143968499980495400157142457 107976374985371550117856843)
        ·
          refine ⟨161964562478057325176785265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107976374985371550117856843 161964562478057325176785265)
          ·
            refine ⟨121473421858542993882588949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161964562478057325176785265 121473421858542993882588949)
            ·
              refine ⟨5694066649619202838246357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121473421858542993882588949 5694066649619202838246357)
              ·
                refine ⟨133454687100450066521399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5694066649619202838246357 133454687100450066521399)
                ·
                  rfl

theorem cell23_7017356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 7].length) (baseStart_7017356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017356 prefixEnd_7017356 := by exact prefixLift 7017356
  have htrace : WordTrace (prefixWord ++ tailWord_7017356) baseStart_7017356 baseEnd_7017356 := by
    simpa [prefixWord, tailWord_7017356, baseEnd_7017356] using wordTrace_append hprefix tailTrace_7017356
  have hstable : (prefixWord ++ tailWord_7017356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017356).length < 2 ^ (prefixWord ++ tailWord_7017356).sum := by decide
  have hdescent : baseEnd_7017356 < baseStart_7017356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017369 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 1, 9]
def baseStart_7017369 : Nat := 118140960795 + 7017369 * 2 ^ 59
def prefixEnd_7017369 : Nat := 4983230072969 + 3 ^ 40 * 7017369 * 2
def baseEnd_7017369 : Nat := 1201094408986886748405071

theorem tailTrace_7017369 : CollatzResearch.WordTrace tailWord_7017369 prefixEnd_7017369 1201094408986886748405071 := by
  unfold tailWord_7017369
  simp only [CollatzResearch.WordTrace]
  refine ⟨255944474114278059055143161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170629649409518706036762107 255944474114278059055143161)
  ·
    refine ⟨191958355585708544291357371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255944474114278059055143161 191958355585708544291357371)
    ·
      refine ⟨287937533378562816437036057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191958355585708544291357371 287937533378562816437036057)
      ·
        refine ⟨215953150033922112327777043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287937533378562816437036057 215953150033922112327777043)
        ·
          refine ⟨323929725050883168491665565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215953150033922112327777043 323929725050883168491665565)
          ·
            refine ⟨121473646894081188184374587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323929725050883168491665565 121473646894081188184374587)
            ·
              refine ⟨182210470341121782276561881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121473646894081188184374587 182210470341121782276561881)
              ·
                refine ⟨136657852755841336707421411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182210470341121782276561881 136657852755841336707421411)
                ·
                  refine ⟨204986779133762005061132117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136657852755841336707421411 204986779133762005061132117)
                  ·
                    refine ⟨1201094408986886748405071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 204986779133762005061132117 1201094408986886748405071)
                    ·
                      rfl

theorem cell23_7017369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_7017369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017369 prefixEnd_7017369 := by exact prefixLift 7017369
  have htrace : WordTrace (prefixWord ++ tailWord_7017369) baseStart_7017369 baseEnd_7017369 := by
    simpa [prefixWord, tailWord_7017369, baseEnd_7017369] using wordTrace_append hprefix tailTrace_7017369
  have hstable : (prefixWord ++ tailWord_7017369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017369).length < 2 ^ (prefixWord ++ tailWord_7017369).sum := by decide
  have hdescent : baseEnd_7017369 < baseStart_7017369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017400 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 2, 1, 3]
def baseStart_7017400 : Nat := 118140960795 + 7017400 * 2 ^ 59
def prefixEnd_7017400 : Nat := 4983230072969 + 3 ^ 40 * 7017400 * 2
def baseEnd_7017400 : Nat := 3603299144860949623927571

theorem tailTrace_7017400 : CollatzResearch.WordTrace tailWord_7017400 prefixEnd_7017400 3603299144860949623927571 := by
  unfold tailWord_7017400
  simp only [CollatzResearch.WordTrace]
  refine ⟨127972802388582875674760827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170630403184777167566347769 127972802388582875674760827)
  ·
    refine ⟨191959203582874313512141241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127972802388582875674760827 191959203582874313512141241)
    ·
      refine ⟨143969402687155735134105931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191959203582874313512141241 143969402687155735134105931)
      ·
        refine ⟨215954104030733602701158897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143969402687155735134105931 215954104030733602701158897)
        ·
          refine ⟨161965578023050202025869173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215954104030733602701158897 161965578023050202025869173)
          ·
            refine ⟨15184272939660956439925235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161965578023050202025869173 15184272939660956439925235)
            ·
              refine ⟨22776409409491434659887853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15184272939660956439925235 22776409409491434659887853)
              ·
                refine ⟨8541153528559287997457945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22776409409491434659887853 8541153528559287997457945)
                ·
                  refine ⟨6405865146419465998093459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8541153528559287997457945 6405865146419465998093459)
                  ·
                    refine ⟨9608797719629198997140189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6405865146419465998093459 9608797719629198997140189)
                    ·
                      refine ⟨3603299144860949623927571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9608797719629198997140189 3603299144860949623927571)
                      ·
                        rfl

theorem cell23_7017400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_7017400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017400 prefixEnd_7017400 := by exact prefixLift 7017400
  have htrace : WordTrace (prefixWord ++ tailWord_7017400) baseStart_7017400 baseEnd_7017400 := by
    simpa [prefixWord, tailWord_7017400, baseEnd_7017400] using wordTrace_append hprefix tailTrace_7017400
  have hstable : (prefixWord ++ tailWord_7017400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017400).length < 2 ^ (prefixWord ++ tailWord_7017400).sum := by decide
  have hdescent : baseEnd_7017400 < baseStart_7017400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017421 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7017421 : Nat := 118140960795 + 7017421 * 2 ^ 59
def prefixEnd_7017421 : Nat := 4983230072969 + 3 ^ 40 * 7017421 * 2
def baseEnd_7017421 : Nat := 3603309927954694041764975

theorem tailTrace_7017421 : CollatzResearch.WordTrace tailWord_7017421 prefixEnd_7017421 3603309927954694041764975 := by
  unfold tailWord_7017421
  simp only [CollatzResearch.WordTrace]
  refine ⟨255946370710089671936036117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170630913806726447957357411 255946370710089671936036117)
  ·
    refine ⟨11997486127035453372001693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 255946370710089671936036117 11997486127035453372001693)
    ·
      refine ⟨4499057297638295014500635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11997486127035453372001693 4499057297638295014500635)
      ·
        refine ⟨6748585946457442521750953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4499057297638295014500635 6748585946457442521750953)
        ·
          refine ⟨5061439459843081891313215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6748585946457442521750953 5061439459843081891313215)
          ·
            refine ⟨7592159189764622836969823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5061439459843081891313215 7592159189764622836969823)
            ·
              refine ⟨11388238784646934255454735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7592159189764622836969823 11388238784646934255454735)
              ·
                refine ⟨17082358176970401383182103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11388238784646934255454735 17082358176970401383182103)
                ·
                  refine ⟨25623537265455602074773155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17082358176970401383182103 25623537265455602074773155)
                  ·
                    refine ⟨38435305898183403112159733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25623537265455602074773155 38435305898183403112159733)
                    ·
                      refine ⟨3603309927954694041764975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38435305898183403112159733 3603309927954694041764975)
                      ·
                        rfl

theorem cell23_7017421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7017421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017421 prefixEnd_7017421 := by exact prefixLift 7017421
  have htrace : WordTrace (prefixWord ++ tailWord_7017421) baseStart_7017421 baseEnd_7017421 := by
    simpa [prefixWord, tailWord_7017421, baseEnd_7017421] using wordTrace_append hprefix tailTrace_7017421
  have hstable : (prefixWord ++ tailWord_7017421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017421).length < 2 ^ (prefixWord ++ tailWord_7017421).sum := by decide
  have hdescent : baseEnd_7017421 < baseStart_7017421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017423 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 3, 4, 2]
def baseStart_7017423 : Nat := 118140960795 + 7017423 * 2 ^ 59
def prefixEnd_7017423 : Nat := 4983230072969 + 3 ^ 40 * 7017423 * 2
def baseEnd_7017423 : Nat := 3603310954916003033939965

theorem tailTrace_7017423 : CollatzResearch.WordTrace tailWord_7017423 prefixEnd_7017423 3603310954916003033939965 := by
  unfold tailWord_7017423
  simp only [CollatzResearch.WordTrace]
  refine ⟨255946443656082426277608923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170630962437388284185072615 255946443656082426277608923)
  ·
    refine ⟨383919665484123639416413385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255946443656082426277608923 383919665484123639416413385)
    ·
      refine ⟨287939749113092729562310039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383919665484123639416413385 287939749113092729562310039)
      ·
        refine ⟨431909623669639094343465059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287939749113092729562310039 431909623669639094343465059)
        ·
          refine ⟨647864435504458641515197589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431909623669639094343465059 647864435504458641515197589)
          ·
            refine ⟨30368645414271498821024887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 647864435504458641515197589 30368645414271498821024887)
            ·
              refine ⟨45552968121407248231537331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30368645414271498821024887 45552968121407248231537331)
              ·
                refine ⟨68329452182110872347305997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45552968121407248231537331 68329452182110872347305997)
                ·
                  refine ⟨25623544568291577130239749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68329452182110872347305997 25623544568291577130239749)
                  ·
                    refine ⟨4804414606554670711919953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25623544568291577130239749 4804414606554670711919953)
                    ·
                      refine ⟨3603310954916003033939965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4804414606554670711919953 3603310954916003033939965)
                      ·
                        rfl

theorem cell23_7017423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 4, 2].length) (baseStart_7017423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017423 prefixEnd_7017423 := by exact prefixLift 7017423
  have htrace : WordTrace (prefixWord ++ tailWord_7017423) baseStart_7017423 baseEnd_7017423 := by
    simpa [prefixWord, tailWord_7017423, baseEnd_7017423] using wordTrace_append hprefix tailTrace_7017423
  have hstable : (prefixWord ++ tailWord_7017423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017423).length < 2 ^ (prefixWord ++ tailWord_7017423).sum := by decide
  have hdescent : baseEnd_7017423 < baseStart_7017423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017457 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 2, 2, 2]
def baseStart_7017457 : Nat := 118140960795 + 7017457 * 2 ^ 59
def prefixEnd_7017457 : Nat := 4983230072969 + 3 ^ 40 * 7017457 * 2
def baseEnd_7017457 : Nat := 3603328413258255900914809

theorem tailTrace_7017457 : CollatzResearch.WordTrace tailWord_7017457 prefixEnd_7017457 3603328413258255900914809 := by
  unfold tailWord_7017457
  simp only [CollatzResearch.WordTrace]
  refine ⟨255947683737959250084346625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170631789158639500056231083 255947683737959250084346625)
  ·
    refine ⟨191960762803469437563259969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255947683737959250084346625 191960762803469437563259969)
    ·
      refine ⟨143970572102602078172444977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191960762803469437563259969 143970572102602078172444977)
      ·
        refine ⟨107977929076951558629333733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143970572102602078172444977 107977929076951558629333733)
        ·
          refine ⟨20245861701928417243000075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107977929076951558629333733 20245861701928417243000075)
          ·
            refine ⟨30368792552892625864500113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20245861701928417243000075 30368792552892625864500113)
            ·
              refine ⟨22776594414669469398375085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30368792552892625864500113 22776594414669469398375085)
              ·
                refine ⟨8541222905501051024390657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22776594414669469398375085 8541222905501051024390657)
                ·
                  refine ⟨6405917179125788268292993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8541222905501051024390657 6405917179125788268292993)
                  ·
                    refine ⟨4804437884344341201219745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6405917179125788268292993 4804437884344341201219745)
                    ·
                      refine ⟨3603328413258255900914809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4804437884344341201219745 3603328413258255900914809)
                      ·
                        rfl

theorem cell23_7017457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_7017457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017457 prefixEnd_7017457 := by exact prefixLift 7017457
  have htrace : WordTrace (prefixWord ++ tailWord_7017457) baseStart_7017457 baseEnd_7017457 := by
    simpa [prefixWord, tailWord_7017457, baseEnd_7017457] using wordTrace_append hprefix tailTrace_7017457
  have hstable : (prefixWord ++ tailWord_7017457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017457).length < 2 ^ (prefixWord ++ tailWord_7017457).sum := by decide
  have hdescent : baseEnd_7017457 < baseStart_7017457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017480 : List Nat := [2, 1, 3, 2, 1, 4, 2, 3, 5]
def baseStart_7017480 : Nat := 118140960795 + 7017480 * 2 ^ 59
def prefixEnd_7017480 : Nat := 4983230072969 + 3 ^ 40 * 7017480 * 2
def baseEnd_7017480 : Nat := 400371135923701034547467

theorem tailTrace_7017480 : CollatzResearch.WordTrace tailWord_7017480 prefixEnd_7017480 400371135923701034547467 := by
  unfold tailWord_7017480
  simp only [CollatzResearch.WordTrace]
  refine ⟨127974261308437962506216947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170632348411250616674955929 127974261308437962506216947)
  ·
    refine ⟨191961391962656943759325421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127974261308437962506216947 191961391962656943759325421)
    ·
      refine ⟨71985521985996353909747033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191961391962656943759325421 71985521985996353909747033)
      ·
        refine ⟨53989141489497265432310275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71985521985996353909747033 53989141489497265432310275)
        ·
          refine ⟨80983712234245898148465413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53989141489497265432310275 80983712234245898148465413)
          ·
            refine ⟨15184446043921105902837265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80983712234245898148465413 15184446043921105902837265)
            ·
              refine ⟨11388334532940829427127949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15184446043921105902837265 11388334532940829427127949)
              ·
                refine ⟨4270625449852811035172981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11388334532940829427127949 4270625449852811035172981)
                ·
                  refine ⟨400371135923701034547467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4270625449852811035172981 400371135923701034547467)
                  ·
                    rfl

theorem cell23_7017480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 5].length) (baseStart_7017480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017480 prefixEnd_7017480 := by exact prefixLift 7017480
  have htrace : WordTrace (prefixWord ++ tailWord_7017480) baseStart_7017480 baseEnd_7017480 := by
    simpa [prefixWord, tailWord_7017480, baseEnd_7017480] using wordTrace_append hprefix tailTrace_7017480
  have hstable : (prefixWord ++ tailWord_7017480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017480).length < 2 ^ (prefixWord ++ tailWord_7017480).sum := by decide
  have hdescent : baseEnd_7017480 < baseStart_7017480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017536 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 10]
def baseStart_7017536 : Nat := 118140960795 + 7017536 * 2 ^ 59
def prefixEnd_7017536 : Nat := 4983230072969 + 3 ^ 40 * 7017536 * 2
def baseEnd_7017536 : Nat := 400374330914440121314105

theorem tailTrace_7017536 : CollatzResearch.WordTrace tailWord_7017536 prefixEnd_7017536 400374330914440121314105 := by
  unfold tailWord_7017536
  simp only [CollatzResearch.WordTrace]
  refine ⟨127975282552336523288236231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170633710069782031050981641 127975282552336523288236231)
  ·
    refine ⟨191962923828504784932354347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127975282552336523288236231 191962923828504784932354347)
    ·
      refine ⟨287944385742757177398531521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191962923828504784932354347 287944385742757177398531521)
      ·
        refine ⟨215958289307067883048898641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287944385742757177398531521 215958289307067883048898641)
        ·
          refine ⟨161968716980300912286673981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215958289307067883048898641 161968716980300912286673981)
          ·
            refine ⟨60738268867612842107502743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161968716980300912286673981 60738268867612842107502743)
            ·
              refine ⟨91107403301419263161254115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60738268867612842107502743 91107403301419263161254115)
              ·
                refine ⟨136661104952128894741881173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91107403301419263161254115 136661104952128894741881173)
                ·
                  refine ⟨400374330914440121314105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 136661104952128894741881173 400374330914440121314105)
                  ·
                    rfl

theorem cell23_7017536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 10].length) (baseStart_7017536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017536 prefixEnd_7017536 := by exact prefixLift 7017536
  have htrace : WordTrace (prefixWord ++ tailWord_7017536) baseStart_7017536 baseEnd_7017536 := by
    simpa [prefixWord, tailWord_7017536, baseEnd_7017536] using wordTrace_append hprefix tailTrace_7017536
  have hstable : (prefixWord ++ tailWord_7017536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017536).length < 2 ^ (prefixWord ++ tailWord_7017536).sum := by decide
  have hdescent : baseEnd_7017536 < baseStart_7017536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017550 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_7017550 : Nat := 118140960795 + 7017550 * 2 ^ 59
def prefixEnd_7017550 : Nat := 4983230072969 + 3 ^ 40 * 7017550 * 2
def baseEnd_7017550 : Nat := 3603376166959124037051881

theorem tailTrace_7017550 : CollatzResearch.WordTrace tailWord_7017550 prefixEnd_7017550 3603376166959124037051881 := by
  unfold tailWord_7017550
  simp only [CollatzResearch.WordTrace]
  refine ⟨31993884465827790870935263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170634050484414884644988069 31993884465827790870935263)
  ·
    refine ⟨47990826698741686306402895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31993884465827790870935263 47990826698741686306402895)
    ·
      refine ⟨71986240048112529459604343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47990826698741686306402895 71986240048112529459604343)
      ·
        refine ⟨107979360072168794189406515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71986240048112529459604343 107979360072168794189406515)
        ·
          refine ⟨161969040108253191284109773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107979360072168794189406515 161969040108253191284109773)
          ·
            refine ⟨60738390040594946731541165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161969040108253191284109773 60738390040594946731541165)
            ·
              refine ⟨22776896265223105024327937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60738390040594946731541165 22776896265223105024327937)
              ·
                refine ⟨17082672198917328768245953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22776896265223105024327937 17082672198917328768245953)
                ·
                  refine ⟨12812004149187996576184465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17082672198917328768245953 12812004149187996576184465)
                  ·
                    refine ⟨9609003111890997432138349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12812004149187996576184465 9609003111890997432138349)
                    ·
                      refine ⟨3603376166959124037051881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9609003111890997432138349 3603376166959124037051881)
                      ·
                        rfl

theorem cell23_7017550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_7017550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017550 prefixEnd_7017550 := by exact prefixLift 7017550
  have htrace : WordTrace (prefixWord ++ tailWord_7017550) baseStart_7017550 baseEnd_7017550 := by
    simpa [prefixWord, tailWord_7017550, baseEnd_7017550] using wordTrace_append hprefix tailTrace_7017550
  have hstable : (prefixWord ++ tailWord_7017550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017550).length < 2 ^ (prefixWord ++ tailWord_7017550).sum := by decide
  have hdescent : baseEnd_7017550 < baseStart_7017550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017580 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 3]
def baseStart_7017580 : Nat := 118140960795 + 7017580 * 2 ^ 59
def prefixEnd_7017580 : Nat := 4983230072969 + 3 ^ 40 * 7017580 * 2
def baseEnd_7017580 : Nat := 3603391571378758919676743

theorem tailTrace_7017580 : CollatzResearch.WordTrace tailWord_7017580 prefixEnd_7017580 3603391571378758919676743 := by
  unfold tailWord_7017580
  simp only [CollatzResearch.WordTrace]
  refine ⟨127976084958256821045537097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170634779944342428060716129 127976084958256821045537097)
  ·
    refine ⟨95982063718692615784152823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127976084958256821045537097 95982063718692615784152823)
    ·
      refine ⟨143973095578038923676229235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95982063718692615784152823 143973095578038923676229235)
      ·
        refine ⟨215959643367058385514343853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143973095578038923676229235 215959643367058385514343853)
        ·
          refine ⟨80984866262646894567878945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215959643367058385514343853 80984866262646894567878945)
          ·
            refine ⟨60738649696985170925909209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80984866262646894567878945 60738649696985170925909209)
            ·
              refine ⟨45553987272738878194431907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60738649696985170925909209 45553987272738878194431907)
              ·
                refine ⟨68330980909108317291647861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45553987272738878194431907 68330980909108317291647861)
                ·
                  refine ⟨6406029460228904746091987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68330980909108317291647861 6406029460228904746091987)
                  ·
                    refine ⟨9609044190343357119137981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6406029460228904746091987 9609044190343357119137981)
                    ·
                      refine ⟨3603391571378758919676743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9609044190343357119137981 3603391571378758919676743)
                      ·
                        rfl

theorem cell23_7017580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_7017580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017580 prefixEnd_7017580 := by exact prefixLift 7017580
  have htrace : WordTrace (prefixWord ++ tailWord_7017580) baseStart_7017580 baseEnd_7017580 := by
    simpa [prefixWord, tailWord_7017580, baseEnd_7017580] using wordTrace_append hprefix tailTrace_7017580
  have hstable : (prefixWord ++ tailWord_7017580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017580).length < 2 ^ (prefixWord ++ tailWord_7017580).sum := by decide
  have hdescent : baseEnd_7017580 < baseStart_7017580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017583 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 3, 5]
def baseStart_7017583 : Nat := 118140960795 + 7017583 * 2 ^ 59
def prefixEnd_7017583 : Nat := 4983230072969 + 3 ^ 40 * 7017583 * 2
def baseEnd_7017583 : Nat := 1201131037273574135979743

theorem tailTrace_7017583 : CollatzResearch.WordTrace tailWord_7017583 prefixEnd_7017583 1201131037273574135979743 := by
  unfold tailWord_7017583
  simp only [CollatzResearch.WordTrace]
  refine ⟨255952279335502773603433403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170634852890335182402288935 255952279335502773603433403)
  ·
    refine ⟨383928419003254160405150105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255952279335502773603433403 383928419003254160405150105)
    ·
      refine ⟨287946314252440620303862579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383928419003254160405150105 287946314252440620303862579)
      ·
        refine ⟨431919471378660930455793869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287946314252440620303862579 431919471378660930455793869)
        ·
          refine ⟨161969801766997848920922701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431919471378660930455793869 161969801766997848920922701)
          ·
            refine ⟨60738675662624193345346013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161969801766997848920922701 60738675662624193345346013)
            ·
              refine ⟨22777003373484072504504755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60738675662624193345346013 22777003373484072504504755)
              ·
                refine ⟨34165505060226108756757133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22777003373484072504504755 34165505060226108756757133)
                ·
                  refine ⟨12812064397584790783783925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34165505060226108756757133 12812064397584790783783925)
                  ·
                    refine ⟨1201131037273574135979743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12812064397584790783783925 1201131037273574135979743)
                    ·
                      rfl

theorem cell23_7017583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_7017583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017583 prefixEnd_7017583 := by exact prefixLift 7017583
  have htrace : WordTrace (prefixWord ++ tailWord_7017583) baseStart_7017583 baseEnd_7017583 := by
    simpa [prefixWord, tailWord_7017583, baseEnd_7017583] using wordTrace_append hprefix tailTrace_7017583
  have hstable : (prefixWord ++ tailWord_7017583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017583).length < 2 ^ (prefixWord ++ tailWord_7017583).sum := by decide
  have hdescent : baseEnd_7017583 < baseStart_7017583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017608 : List Nat := [2, 1, 3, 4, 3, 1, 2, 2, 1, 4]
def baseStart_7017608 : Nat := 118140960795 + 7017608 * 2 ^ 59
def prefixEnd_7017608 : Nat := 4983230072969 + 3 ^ 40 * 7017608 * 2
def baseEnd_7017608 : Nat := 1201135316279028270042205

theorem tailTrace_7017608 : CollatzResearch.WordTrace tailWord_7017608 prefixEnd_7017608 1201135316279028270042205 := by
  unfold tailWord_7017608
  simp only [CollatzResearch.WordTrace]
  refine ⟨127976595580206101436546739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170635460773608135248728985 127976595580206101436546739)
  ·
    refine ⟨191964893370309152154820109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127976595580206101436546739 191964893370309152154820109)
    ·
      refine ⟨71986835013865932058057541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191964893370309152154820109 71986835013865932058057541)
      ·
        refine ⟨13497531565099862260885789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71986835013865932058057541 13497531565099862260885789)
        ·
          refine ⟨5061574336912448347832171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13497531565099862260885789 5061574336912448347832171)
          ·
            refine ⟨7592361505368672521748257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5061574336912448347832171 7592361505368672521748257)
            ·
              refine ⟨5694271129026504391311193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7592361505368672521748257 5694271129026504391311193)
              ·
                refine ⟨4270703346769878293483395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5694271129026504391311193 4270703346769878293483395)
                ·
                  refine ⟨6406055020154817440225093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270703346769878293483395 6406055020154817440225093)
                  ·
                    refine ⟨1201135316279028270042205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6406055020154817440225093 1201135316279028270042205)
                    ·
                      rfl

theorem cell23_7017608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_7017608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017608 prefixEnd_7017608 := by exact prefixLift 7017608
  have htrace : WordTrace (prefixWord ++ tailWord_7017608) baseStart_7017608 baseEnd_7017608 := by
    simpa [prefixWord, tailWord_7017608, baseEnd_7017608] using wordTrace_append hprefix tailTrace_7017608
  have hstable : (prefixWord ++ tailWord_7017608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017608).length < 2 ^ (prefixWord ++ tailWord_7017608).sum := by decide
  have hdescent : baseEnd_7017608 < baseStart_7017608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017637 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 5, 2, 2]
def baseStart_7017637 : Nat := 118140960795 + 7017637 * 2 ^ 59
def prefixEnd_7017637 : Nat := 4983230072969 + 3 ^ 40 * 7017637 * 2
def baseEnd_7017637 : Nat := 3603420839776065196663981

theorem tailTrace_7017637 : CollatzResearch.WordTrace tailWord_7017637 prefixEnd_7017637 3603420839776065196663981 := by
  unfold tailWord_7017637
  simp only [CollatzResearch.WordTrace]
  refine ⟨255954248877307140825899165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170636165918204760550599443 255954248877307140825899165)
  ·
    refine ⟨95982843328990177809712187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255954248877307140825899165 95982843328990177809712187)
    ·
      refine ⟨143974264993485266714568281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95982843328990177809712187 143974264993485266714568281)
      ·
        refine ⟨107980698745113950035926211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143974264993485266714568281 107980698745113950035926211)
        ·
          refine ⟨161971048117670925053889317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107980698745113950035926211 161971048117670925053889317)
          ·
            refine ⟨30369571522063298447604247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161971048117670925053889317 30369571522063298447604247)
            ·
              refine ⟨45554357283094947671406371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30369571522063298447604247 45554357283094947671406371)
              ·
                refine ⟨68331535924642421507109557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45554357283094947671406371 68331535924642421507109557)
                ·
                  refine ⟨6406081492935227016291521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68331535924642421507109557 6406081492935227016291521)
                  ·
                    refine ⟨4804561119701420262218641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6406081492935227016291521 4804561119701420262218641)
                    ·
                      refine ⟨3603420839776065196663981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4804561119701420262218641 3603420839776065196663981)
                      ·
                        rfl

theorem cell23_7017637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_7017637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017637 prefixEnd_7017637 := by exact prefixLift 7017637
  have htrace : WordTrace (prefixWord ++ tailWord_7017637) baseStart_7017637 baseEnd_7017637 := by
    simpa [prefixWord, tailWord_7017637, baseEnd_7017637] using wordTrace_append hprefix tailTrace_7017637
  have hstable : (prefixWord ++ tailWord_7017637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017637).length < 2 ^ (prefixWord ++ tailWord_7017637).sum := by decide
  have hdescent : baseEnd_7017637 < baseStart_7017637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017650 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_7017650 : Nat := 118140960795 + 7017650 * 2 ^ 59
def prefixEnd_7017650 : Nat := 4983230072969 + 3 ^ 40 * 7017650 * 2
def baseEnd_7017650 : Nat := 3603427515024573645801421

theorem tailTrace_7017650 : CollatzResearch.WordTrace tailWord_7017650 prefixEnd_7017650 3603427515024573645801421 := by
  unfold tailWord_7017650
  simp only [CollatzResearch.WordTrace]
  refine ⟨63988680756565011011530601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170636482017506696030748269 63988680756565011011530601)
  ·
    refine ⟨47991510567423758258647951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63988680756565011011530601 47991510567423758258647951)
    ·
      refine ⟨71987265851135637387971927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47991510567423758258647951 71987265851135637387971927)
      ·
        refine ⟨107980898776703456081957891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71987265851135637387971927 107980898776703456081957891)
        ·
          refine ⟨161971348165055184122936837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107980898776703456081957891 161971348165055184122936837)
          ·
            refine ⟨30369627780947847023050657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161971348165055184122936837 30369627780947847023050657)
            ·
              refine ⟨22777220835710885267287993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30369627780947847023050657 22777220835710885267287993)
              ·
                refine ⟨17082915626783163950465995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22777220835710885267287993 17082915626783163950465995)
                ·
                  refine ⟨25624373440174745925698993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17082915626783163950465995 25624373440174745925698993)
                  ·
                    refine ⟨19218280080131059444274245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25624373440174745925698993 19218280080131059444274245)
                    ·
                      refine ⟨3603427515024573645801421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19218280080131059444274245 3603427515024573645801421)
                      ·
                        rfl

theorem cell23_7017650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_7017650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017650 prefixEnd_7017650 := by exact prefixLift 7017650
  have htrace : WordTrace (prefixWord ++ tailWord_7017650) baseStart_7017650 baseEnd_7017650 := by
    simpa [prefixWord, tailWord_7017650, baseEnd_7017650] using wordTrace_append hprefix tailTrace_7017650
  have hstable : (prefixWord ++ tailWord_7017650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017650).length < 2 ^ (prefixWord ++ tailWord_7017650).sum := by decide
  have hdescent : baseEnd_7017650 < baseStart_7017650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017657 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 1, 2, 3]
def baseStart_7017657 : Nat := 118140960795 + 7017657 * 2 ^ 59
def prefixEnd_7017657 : Nat := 4983230072969 + 3 ^ 40 * 7017657 * 2
def baseEnd_7017657 : Nat := 3603431109389155118413889

theorem tailTrace_7017657 : CollatzResearch.WordTrace tailWord_7017657 prefixEnd_7017657 3603431109389155118413889 := by
  unfold tailWord_7017657
  simp only [CollatzResearch.WordTrace]
  refine ⟨255954978337234684241627225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170636652224823122827751483 255954978337234684241627225)
  ·
    refine ⟨191966233752926013181220419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255954978337234684241627225 191966233752926013181220419)
    ·
      refine ⟨287949350629389019771830629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191966233752926013181220419 287949350629389019771830629)
      ·
        refine ⟨53990503243010441207218243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287949350629389019771830629 53990503243010441207218243)
        ·
          refine ⟨80985754864515661810827365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53990503243010441207218243 80985754864515661810827365)
          ·
            refine ⟨15184829037096686589530131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80985754864515661810827365 15184829037096686589530131)
            ·
              refine ⟨22777243555645029884295197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15184829037096686589530131 22777243555645029884295197)
              ·
                refine ⟨8541466333366886206610699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22777243555645029884295197 8541466333366886206610699)
                ·
                  refine ⟨12812199500050329309916049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8541466333366886206610699 12812199500050329309916049)
                  ·
                    refine ⟨9609149625037746982437037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12812199500050329309916049 9609149625037746982437037)
                    ·
                      refine ⟨3603431109389155118413889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9609149625037746982437037 3603431109389155118413889)
                      ·
                        rfl

theorem cell23_7017657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_7017657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017657 prefixEnd_7017657 := by exact prefixLift 7017657
  have htrace : WordTrace (prefixWord ++ tailWord_7017657) baseStart_7017657 baseEnd_7017657 := by
    simpa [prefixWord, tailWord_7017657, baseEnd_7017657] using wordTrace_append hprefix tailTrace_7017657
  have hstable : (prefixWord ++ tailWord_7017657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017657).length < 2 ^ (prefixWord ++ tailWord_7017657).sum := by decide
  have hdescent : baseEnd_7017657 < baseStart_7017657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017664 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 2, 4]
def baseStart_7017664 : Nat := 118140960795 + 7017664 * 2 ^ 59
def prefixEnd_7017664 : Nat := 4983230072969 + 3 ^ 40 * 7017664 * 2
def baseEnd_7017664 : Nat := 1201144901251245530342119

theorem tailTrace_7017664 : CollatzResearch.WordTrace tailWord_7017664 prefixEnd_7017664 1201144901251245530342119 := by
  unfold tailWord_7017664
  simp only [CollatzResearch.WordTrace]
  refine ⟨127977616824104662218566023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170636822432139549624754697 127977616824104662218566023)
  ·
    refine ⟨191966425236156993327849035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127977616824104662218566023 191966425236156993327849035)
    ·
      refine ⟨287949637854235489991773553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191966425236156993327849035 287949637854235489991773553)
      ·
        refine ⟨215962228390676617493830165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287949637854235489991773553 215962228390676617493830165)
        ·
          refine ⟨10123229455812966445023289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 215962228390676617493830165 10123229455812966445023289)
          ·
            refine ⟨7592422091859724833767467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10123229455812966445023289 7592422091859724833767467)
            ·
              refine ⟨11388633137789587250651201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7592422091859724833767467 11388633137789587250651201)
              ·
                refine ⟨8541474853342190437988401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11388633137789587250651201 8541474853342190437988401)
                ·
                  refine ⟨6406106140006642828491301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8541474853342190437988401 6406106140006642828491301)
                  ·
                    refine ⟨1201144901251245530342119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6406106140006642828491301 1201144901251245530342119)
                    ·
                      rfl

theorem cell23_7017664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2, 4].length) (baseStart_7017664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017664 prefixEnd_7017664 := by exact prefixLift 7017664
  have htrace : WordTrace (prefixWord ++ tailWord_7017664) baseStart_7017664 baseEnd_7017664 := by
    simpa [prefixWord, tailWord_7017664, baseEnd_7017664] using wordTrace_append hprefix tailTrace_7017664
  have hstable : (prefixWord ++ tailWord_7017664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017664).length < 2 ^ (prefixWord ++ tailWord_7017664).sum := by decide
  have hdescent : baseEnd_7017664 < baseStart_7017664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017687 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 2, 1, 3]
def baseStart_7017687 : Nat := 118140960795 + 7017687 * 2 ^ 59
def prefixEnd_7017687 : Nat := 4983230072969 + 3 ^ 40 * 7017687 * 2
def baseEnd_7017687 : Nat := 3603446513808790001038751

theorem tailTrace_7017687 : CollatzResearch.WordTrace tailWord_7017687 prefixEnd_7017687 3603446513808790001038751 := by
  unfold tailWord_7017687
  simp only [CollatzResearch.WordTrace]
  refine ⟨255956072527125999365219315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170637381684750666243479543 255956072527125999365219315)
  ·
    refine ⟨383934108790688999047828973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255956072527125999365219315 383934108790688999047828973)
    ·
      refine ⟨143975290796508374642935865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383934108790688999047828973 143975290796508374642935865)
      ·
        refine ⟨107981468097381280982201899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143975290796508374642935865 107981468097381280982201899)
        ·
          refine ⟨161972202146071921473302849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107981468097381280982201899 161972202146071921473302849)
          ·
            refine ⟨121479151609553941104977137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161972202146071921473302849 121479151609553941104977137)
            ·
              refine ⟨91109363707165455828732853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121479151609553941104977137 91109363707165455828732853)
              ·
                refine ⟨8541502847546761483943705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91109363707165455828732853 8541502847546761483943705)
                ·
                  refine ⟨6406127135660071112957779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8541502847546761483943705 6406127135660071112957779)
                  ·
                    refine ⟨9609190703490106669436669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6406127135660071112957779 9609190703490106669436669)
                    ·
                      refine ⟨3603446513808790001038751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9609190703490106669436669 3603446513808790001038751)
                      ·
                        rfl

theorem cell23_7017687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_7017687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017687 prefixEnd_7017687 := by exact prefixLift 7017687
  have htrace : WordTrace (prefixWord ++ tailWord_7017687) baseStart_7017687 baseEnd_7017687 := by
    simpa [prefixWord, tailWord_7017687, baseEnd_7017687] using wordTrace_append hprefix tailTrace_7017687
  have hstable : (prefixWord ++ tailWord_7017687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017687).length < 2 ^ (prefixWord ++ tailWord_7017687).sum := by decide
  have hdescent : baseEnd_7017687 < baseStart_7017687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017753 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_7017753 : Nat := 118140960795 + 7017753 * 2 ^ 59
def prefixEnd_7017753 : Nat := 4983230072969 + 3 ^ 40 * 7017753 * 2
def baseEnd_7017753 : Nat := 3603480403531986742813447

theorem tailTrace_7017753 : CollatzResearch.WordTrace tailWord_7017753 prefixEnd_7017753 3603480403531986742813447 := by
  unfold tailWord_7017753
  simp only [CollatzResearch.WordTrace]
  refine ⟨255958479744886892637121913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170638986496591261758081275 255958479744886892637121913)
  ·
    refine ⟨191968859808665169477841435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255958479744886892637121913 191968859808665169477841435)
    ·
      refine ⟨287953289712997754216762153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191968859808665169477841435 287953289712997754216762153)
      ·
        refine ⟨215964967284748315662571615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287953289712997754216762153 215964967284748315662571615)
        ·
          refine ⟨323947450927122473493857423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215964967284748315662571615 323947450927122473493857423)
          ·
            refine ⟨485921176390683710240786135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323947450927122473493857423 485921176390683710240786135)
            ·
              refine ⟨728881764586025565361179203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485921176390683710240786135 728881764586025565361179203)
              ·
                refine ⟨1093322646879038348041768805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728881764586025565361179203 1093322646879038348041768805)
                ·
                  refine ⟨204997996289819690257831651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1093322646879038348041768805 204997996289819690257831651)
                  ·
                    refine ⟨307496994434729535386747477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204997996289819690257831651 307496994434729535386747477)
                    ·
                      refine ⟨3603480403531986742813447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 307496994434729535386747477 3603480403531986742813447)
                      ·
                        rfl

theorem cell23_7017753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_7017753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017753 prefixEnd_7017753 := by exact prefixLift 7017753
  have htrace : WordTrace (prefixWord ++ tailWord_7017753) baseStart_7017753 baseEnd_7017753 := by
    simpa [prefixWord, tailWord_7017753, baseEnd_7017753] using wordTrace_append hprefix tailTrace_7017753
  have hstable : (prefixWord ++ tailWord_7017753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017753).length < 2 ^ (prefixWord ++ tailWord_7017753).sum := by decide
  have hdescent : baseEnd_7017753 < baseStart_7017753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017800 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_7017800 : Nat := 118140960795 + 7017800 * 2 ^ 59
def prefixEnd_7017800 : Nat := 4983230072969 + 3 ^ 40 * 7017800 * 2
def baseEnd_7017800 : Nat := 3603504537122748058925731

theorem tailTrace_7017800 : CollatzResearch.WordTrace tailWord_7017800 prefixEnd_7017800 3603504537122748058925731 := by
  unfold tailWord_7017800
  simp only [CollatzResearch.WordTrace]
  refine ⟨127980096987858309832041427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170640129317144413109388569 127980096987858309832041427)
  ·
    refine ⟨191970145481787464748062141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127980096987858309832041427 191970145481787464748062141)
    ·
      refine ⟨71988804555670299280523303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191970145481787464748062141 71988804555670299280523303)
      ·
        refine ⟨107983206833505448920784955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71988804555670299280523303 107983206833505448920784955)
        ·
          refine ⟨161974810250258173381177433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107983206833505448920784955 161974810250258173381177433)
          ·
            refine ⟨121481107687693630035883075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161974810250258173381177433 121481107687693630035883075)
            ·
              refine ⟨182221661531540445053824613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121481107687693630035883075 182221661531540445053824613)
              ·
                refine ⟨34166561537163833447592115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182221661531540445053824613 34166561537163833447592115)
                ·
                  refine ⟨51249842305745750171388173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34166561537163833447592115 51249842305745750171388173)
                  ·
                    refine ⟨19218690864654656314270565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51249842305745750171388173 19218690864654656314270565)
                    ·
                      refine ⟨3603504537122748058925731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19218690864654656314270565 3603504537122748058925731)
                      ·
                        rfl

theorem cell23_7017800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_7017800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017800 prefixEnd_7017800 := by exact prefixLift 7017800
  have htrace : WordTrace (prefixWord ++ tailWord_7017800) baseStart_7017800 baseEnd_7017800 := by
    simpa [prefixWord, tailWord_7017800, baseEnd_7017800] using wordTrace_append hprefix tailTrace_7017800
  have hstable : (prefixWord ++ tailWord_7017800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017800).length < 2 ^ (prefixWord ++ tailWord_7017800).sum := by decide
  have hdescent : baseEnd_7017800 < baseStart_7017800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017817 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 4]
def baseStart_7017817 : Nat := 118140960795 + 7017817 * 2 ^ 59
def prefixEnd_7017817 : Nat := 4983230072969 + 3 ^ 40 * 7017817 * 2
def baseEnd_7017817 : Nat := 3603513266293874492413153

theorem tailTrace_7017817 : CollatzResearch.WordTrace tailWord_7017817 prefixEnd_7017817 3603513266293874492413153 := by
  unfold tailWord_7017817
  simp only [CollatzResearch.WordTrace]
  refine ⟨255960814016655031567451705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170640542677770021044967803 255960814016655031567451705)
  ·
    refine ⟨191970610512491273675588779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255960814016655031567451705 191970610512491273675588779)
    ·
      refine ⟨287955915768736910513383169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191970610512491273675588779 287955915768736910513383169)
      ·
        refine ⟨215966936826552682885037377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287955915768736910513383169 215966936826552682885037377)
        ·
          refine ⟨161975202619914512163778033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215966936826552682885037377 161975202619914512163778033)
          ·
            refine ⟨121481401964935884122833525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161975202619914512163778033 121481401964935884122833525)
            ·
              refine ⟨11388881434212739136515643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121481401964935884122833525 11388881434212739136515643)
              ·
                refine ⟨17083322151319108704773465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11388881434212739136515643 17083322151319108704773465)
                ·
                  refine ⟨12812491613489331528580099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17083322151319108704773465 12812491613489331528580099)
                  ·
                    refine ⟨19218737420233997292870149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12812491613489331528580099 19218737420233997292870149)
                    ·
                      refine ⟨3603513266293874492413153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19218737420233997292870149 3603513266293874492413153)
                      ·
                        rfl

theorem cell23_7017817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_7017817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017817 prefixEnd_7017817 := by exact prefixLift 7017817
  have htrace : WordTrace (prefixWord ++ tailWord_7017817) baseStart_7017817 baseEnd_7017817 := by
    simpa [prefixWord, tailWord_7017817, baseEnd_7017817] using wordTrace_append hprefix tailTrace_7017817
  have hstable : (prefixWord ++ tailWord_7017817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017817).length < 2 ^ (prefixWord ++ tailWord_7017817).sum := by decide
  have hdescent : baseEnd_7017817 < baseStart_7017817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017840 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 8]
def baseStart_7017840 : Nat := 118140960795 + 7017840 * 2 ^ 59
def prefixEnd_7017840 : Nat := 4983230072969 + 3 ^ 40 * 7017840 * 2
def baseEnd_7017840 : Nat := 400391675149880878047283

theorem tailTrace_7017840 : CollatzResearch.WordTrace tailWord_7017840 prefixEnd_7017840 400391675149880878047283 := by
  unfold tailWord_7017840
  simp only [CollatzResearch.WordTrace]
  refine ⟨127980826447785853247769487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170641101930381137663692649 127980826447785853247769487)
  ·
    refine ⟨191971239671678779871654231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127980826447785853247769487 191971239671678779871654231)
    ·
      refine ⟨287956859507518169807481347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191971239671678779871654231 287956859507518169807481347)
      ·
        refine ⟨431935289261277254711222021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287956859507518169807481347 431935289261277254711222021)
        ·
          refine ⟨80987866736489485258354129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431935289261277254711222021 80987866736489485258354129)
          ·
            refine ⟨60740900052367113943765597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80987866736489485258354129 60740900052367113943765597)
            ·
              refine ⟨22777837519637667728912099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60740900052367113943765597 22777837519637667728912099)
              ·
                refine ⟨34166756279456501593368149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22777837519637667728912099 34166756279456501593368149)
                ·
                  refine ⟨400391675149880878047283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34166756279456501593368149 400391675149880878047283)
                  ·
                    rfl

theorem cell23_7017840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 8].length) (baseStart_7017840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017840 prefixEnd_7017840 := by exact prefixLift 7017840
  have htrace : WordTrace (prefixWord ++ tailWord_7017840) baseStart_7017840 baseEnd_7017840 := by
    simpa [prefixWord, tailWord_7017840, baseEnd_7017840] using wordTrace_append hprefix tailTrace_7017840
  have hstable : (prefixWord ++ tailWord_7017840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017840).length < 2 ^ (prefixWord ++ tailWord_7017840).sum := by decide
  have hdescent : baseEnd_7017840 < baseStart_7017840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017917 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_7017917 : Nat := 118140960795 + 7017917 * 2 ^ 59
def prefixEnd_7017917 : Nat := 4983230072969 + 3 ^ 40 * 7017917 * 2
def baseEnd_7017917 : Nat := 1201188204786441367054231

theorem tailTrace_7017917 : CollatzResearch.WordTrace tailWord_7017917 prefixEnd_7017917 1201188204786441367054231 := by
  unfold tailWord_7017917
  simp only [CollatzResearch.WordTrace]
  refine ⟨255964461316292748646092005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170642974210861832430728003 255964461316292748646092005)
  ·
    refine ⟨47993336496804890371142251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255964461316292748646092005 47993336496804890371142251)
    ·
      refine ⟨71990004745207335556713377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47993336496804890371142251 71990004745207335556713377)
      ·
        refine ⟨53992503558905501667535033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71990004745207335556713377 53992503558905501667535033)
        ·
          refine ⟨40494377669179126250651275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53992503558905501667535033 40494377669179126250651275)
          ·
            refine ⟨60741566503768689375976913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40494377669179126250651275 60741566503768689375976913)
            ·
              refine ⟨45556174877826517031982685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60741566503768689375976913 45556174877826517031982685)
              ·
                refine ⟨17083565579184943886993507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45556174877826517031982685 17083565579184943886993507)
                ·
                  refine ⟨25625348368777415830490261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17083565579184943886993507 25625348368777415830490261)
                  ·
                    refine ⟨1201188204786441367054231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25625348368777415830490261 1201188204786441367054231)
                    ·
                      rfl

theorem cell23_7017917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_7017917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017917 prefixEnd_7017917 := by exact prefixLift 7017917
  have htrace : WordTrace (prefixWord ++ tailWord_7017917) baseStart_7017917 baseEnd_7017917 := by
    simpa [prefixWord, tailWord_7017917, baseEnd_7017917] using wordTrace_append hprefix tailTrace_7017917
  have hstable : (prefixWord ++ tailWord_7017917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017917).length < 2 ^ (prefixWord ++ tailWord_7017917).sum := by decide
  have hdescent : baseEnd_7017917 < baseStart_7017917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017922 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_7017922 : Nat := 118140960795 + 7017922 * 2 ^ 59
def prefixEnd_7017922 : Nat := 4983230072969 + 3 ^ 40 * 7017922 * 2
def baseEnd_7017922 : Nat := 3603567181762596581600171

theorem tailTrace_7017922 : CollatzResearch.WordTrace tailWord_7017922 prefixEnd_7017922 3603567181762596581600171 := by
  unfold tailWord_7017922
  simp only [CollatzResearch.WordTrace]
  refine ⟨63991160920318658625006005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170643095787516423000016013 63991160920318658625006005)
  ·
    refine ⟨5999171336279874246094313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63991160920318658625006005 5999171336279874246094313)
    ·
      refine ⟨4499378502209905684570735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5999171336279874246094313 4499378502209905684570735)
      ·
        refine ⟨6749067753314858526856103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4499378502209905684570735 6749067753314858526856103)
        ·
          refine ⟨10123601629972287790284155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749067753314858526856103 10123601629972287790284155)
          ·
            refine ⟨15185402444958431685426233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10123601629972287790284155 15185402444958431685426233)
            ·
              refine ⟨11389051833718823764069675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15185402444958431685426233 11389051833718823764069675)
              ·
                refine ⟨17083577750578235646104513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11389051833718823764069675 17083577750578235646104513)
                ·
                  refine ⟨12812683312933676734578385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17083577750578235646104513 12812683312933676734578385)
                  ·
                    refine ⟨9609512484700257550933789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12812683312933676734578385 9609512484700257550933789)
                    ·
                      refine ⟨3603567181762596581600171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9609512484700257550933789 3603567181762596581600171)
                      ·
                        rfl

theorem cell23_7017922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_7017922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017922 prefixEnd_7017922 := by exact prefixLift 7017922
  have htrace : WordTrace (prefixWord ++ tailWord_7017922) baseStart_7017922 baseEnd_7017922 := by
    simpa [prefixWord, tailWord_7017922, baseEnd_7017922] using wordTrace_append hprefix tailTrace_7017922
  have hstable : (prefixWord ++ tailWord_7017922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017922).length < 2 ^ (prefixWord ++ tailWord_7017922).sum := by decide
  have hdescent : baseEnd_7017922 < baseStart_7017922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017941 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 1, 1, 4]
def baseStart_7017941 : Nat := 118140960795 + 7017941 * 2 ^ 59
def prefixEnd_7017941 : Nat := 4983230072969 + 3 ^ 40 * 7017941 * 2
def baseEnd_7017941 : Nat := 3603576937895032007262583

theorem tailTrace_7017941 : CollatzResearch.WordTrace tailWord_7017941 prefixEnd_7017941 3603576937895032007262583 := by
  unfold tailWord_7017941
  simp only [CollatzResearch.WordTrace]
  refine ⟨255965336668205800744965677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170643557778803867163310451 255965336668205800744965677)
  ·
    refine ⟨95987001250577175279362129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255965336668205800744965677 95987001250577175279362129)
    ·
      refine ⟨71990250937932881459521597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95987001250577175279362129 71990250937932881459521597)
      ·
        refine ⟨26996344101724830547320599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71990250937932881459521597 26996344101724830547320599)
        ·
          refine ⟨40494516152587245820980899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26996344101724830547320599 40494516152587245820980899)
          ·
            refine ⟨60741774228880868731471349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40494516152587245820980899 60741774228880868731471349)
            ·
              refine ⟨5694541333957581443575439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60741774228880868731471349 5694541333957581443575439)
              ·
                refine ⟨8541812000936372165363159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5694541333957581443575439 8541812000936372165363159)
                ·
                  refine ⟨12812718001404558248044739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8541812000936372165363159 12812718001404558248044739)
                  ·
                    refine ⟨19219077002106837372067109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12812718001404558248044739 19219077002106837372067109)
                    ·
                      refine ⟨3603576937895032007262583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19219077002106837372067109 3603576937895032007262583)
                      ·
                        rfl

theorem cell23_7017941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_7017941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017941 prefixEnd_7017941 := by exact prefixLift 7017941
  have htrace : WordTrace (prefixWord ++ tailWord_7017941) baseStart_7017941 baseEnd_7017941 := by
    simpa [prefixWord, tailWord_7017941, baseEnd_7017941] using wordTrace_append hprefix tailTrace_7017941
  have hstable : (prefixWord ++ tailWord_7017941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017941).length < 2 ^ (prefixWord ++ tailWord_7017941).sum := by decide
  have hdescent : baseEnd_7017941 < baseStart_7017941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017944 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 1, 2, 3]
def baseStart_7017944 : Nat := 118140960795 + 7017944 * 2 ^ 59
def prefixEnd_7017944 : Nat := 4983230072969 + 3 ^ 40 * 7017944 * 2
def baseEnd_7017944 : Nat := 3603578478336995495525069

theorem tailTrace_7017944 : CollatzResearch.WordTrace tailWord_7017944 prefixEnd_7017944 3603578478336995495525069 := by
  unfold tailWord_7017944
  simp only [CollatzResearch.WordTrace]
  refine ⟨127982723043597466128662443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170643630724796621504883257 127982723043597466128662443)
  ·
    refine ⟨191974084565396199192993665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127982723043597466128662443 191974084565396199192993665)
    ·
      refine ⟨143980563424047149394745249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191974084565396199192993665 143980563424047149394745249)
      ·
        refine ⟨107985422568035362046058937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143980563424047149394745249 107985422568035362046058937)
        ·
          refine ⟨80989066926026521534544203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107985422568035362046058937 80989066926026521534544203)
          ·
            refine ⟨121483600389039782301816305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80989066926026521534544203 121483600389039782301816305)
            ·
              refine ⟨91112700291779836726362229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121483600389039782301816305 91112700291779836726362229)
              ·
                refine ⟨8541815652354359693096459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91112700291779836726362229 8541815652354359693096459)
                ·
                  refine ⟨12812723478531539539644689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8541815652354359693096459 12812723478531539539644689)
                  ·
                    refine ⟨9609542608898654654733517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12812723478531539539644689 9609542608898654654733517)
                    ·
                      refine ⟨3603578478336995495525069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9609542608898654654733517 3603578478336995495525069)
                      ·
                        rfl

theorem cell23_7017944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_7017944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017944 prefixEnd_7017944 := by exact prefixLift 7017944
  have htrace : WordTrace (prefixWord ++ tailWord_7017944) baseStart_7017944 baseEnd_7017944 := by
    simpa [prefixWord, tailWord_7017944, baseEnd_7017944] using wordTrace_append hprefix tailTrace_7017944
  have hstable : (prefixWord ++ tailWord_7017944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017944).length < 2 ^ (prefixWord ++ tailWord_7017944).sum := by decide
  have hdescent : baseEnd_7017944 < baseStart_7017944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7017995 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 1, 2, 3]
def baseStart_7017995 : Nat := 118140960795 + 7017995 * 2 ^ 59
def prefixEnd_7017995 : Nat := 4983230072969 + 3 ^ 40 * 7017995 * 2
def baseEnd_7017995 : Nat := 3603604665850374795987335

theorem tailTrace_7017995 : CollatzResearch.WordTrace tailWord_7017995 prefixEnd_7017995 3603604665850374795987335 := by
  unfold tailWord_7017995
  simp only [CollatzResearch.WordTrace]
  refine ⟨255967306210010167967431439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170644870806673445311620959 255967306210010167967431439)
  ·
    refine ⟨383950959315015251951147159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255967306210010167967431439 383950959315015251951147159)
    ·
      refine ⟨575926438972522877926720739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383950959315015251951147159 575926438972522877926720739)
      ·
        refine ⟨863889658458784316890081109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575926438972522877926720739 863889658458784316890081109)
        ·
          refine ⟨5061853467531939356777819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 863889658458784316890081109 5061853467531939356777819)
          ·
            refine ⟨7592780201297909035166729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5061853467531939356777819 7592780201297909035166729)
            ·
              refine ⟨5694585150973431776375047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7592780201297909035166729 5694585150973431776375047)
              ·
                refine ⟨8541877726460147664562571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5694585150973431776375047 8541877726460147664562571)
                ·
                  refine ⟨12812816589690221496843857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8541877726460147664562571 12812816589690221496843857)
                  ·
                    refine ⟨9609612442267666122632893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12812816589690221496843857 9609612442267666122632893)
                    ·
                      refine ⟨3603604665850374795987335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9609612442267666122632893 3603604665850374795987335)
                      ·
                        rfl

theorem cell23_7017995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 2, 3].length) (baseStart_7017995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7017995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7017995 prefixEnd_7017995 := by exact prefixLift 7017995
  have htrace : WordTrace (prefixWord ++ tailWord_7017995) baseStart_7017995 baseEnd_7017995 := by
    simpa [prefixWord, tailWord_7017995, baseEnd_7017995] using wordTrace_append hprefix tailTrace_7017995
  have hstable : (prefixWord ++ tailWord_7017995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7017995).length < 2 ^ (prefixWord ++ tailWord_7017995).sum := by decide
  have hdescent : baseEnd_7017995 < baseStart_7017995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7017995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018001 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 1, 3, 2]
def baseStart_7018001 : Nat := 118140960795 + 7018001 * 2 ^ 59
def prefixEnd_7018001 : Nat := 4983230072969 + 3 ^ 40 * 7018001 * 2
def baseEnd_7018001 : Nat := 3603607746734301772512307

theorem tailTrace_7018001 : CollatzResearch.WordTrace tailWord_7018001 prefixEnd_7018001 3603607746734301772512307 := by
  unfold tailWord_7018001
  simp only [CollatzResearch.WordTrace]
  refine ⟨255967525047988430992149857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170645016698658953994766571 255967525047988430992149857)
  ·
    refine ⟨191975643785991323244112393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255967525047988430992149857 191975643785991323244112393)
    ·
      refine ⟨143981732839493492433084295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191975643785991323244112393 143981732839493492433084295)
      ·
        refine ⟨215972599259240238649626443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143981732839493492433084295 215972599259240238649626443)
        ·
          refine ⟨323958898888860357974439665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215972599259240238649626443 323958898888860357974439665)
          ·
            refine ⟨242969174166645268480829749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323958898888860357974439665 242969174166645268480829749)
            ·
              refine ⟨22778360078122993920077789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242969174166645268480829749 22778360078122993920077789)
              ·
                refine ⟨8541885029296122720029171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22778360078122993920077789 8541885029296122720029171)
                ·
                  refine ⟨12812827543944184080043757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8541885029296122720029171 12812827543944184080043757)
                  ·
                    refine ⟨4804810328979069030016409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12812827543944184080043757 4804810328979069030016409)
                    ·
                      refine ⟨3603607746734301772512307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4804810328979069030016409 3603607746734301772512307)
                      ·
                        rfl

theorem cell23_7018001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_7018001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018001 prefixEnd_7018001 := by exact prefixLift 7018001
  have htrace : WordTrace (prefixWord ++ tailWord_7018001) baseStart_7018001 baseEnd_7018001 := by
    simpa [prefixWord, tailWord_7018001, baseEnd_7018001] using wordTrace_append hprefix tailTrace_7018001
  have hstable : (prefixWord ++ tailWord_7018001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018001).length < 2 ^ (prefixWord ++ tailWord_7018001).sum := by decide
  have hdescent : baseEnd_7018001 < baseStart_7018001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018097 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 2, 8]
def baseStart_7018097 : Nat := 118140960795 + 7018097 * 2 ^ 59
def prefixEnd_7018097 : Nat := 4983230072969 + 3 ^ 40 * 7018097 * 2
def baseEnd_7018097 : Nat := 1201219013625711132303955

theorem tailTrace_7018097 : CollatzResearch.WordTrace tailWord_7018097 prefixEnd_7018097 1201219013625711132303955 := by
  unfold tailWord_7018097
  simp only [CollatzResearch.WordTrace]
  refine ⟨255971026455640639387644545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170647350970427092925096363 255971026455640639387644545)
  ·
    refine ⟨191978269841730479540733409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255971026455640639387644545 191978269841730479540733409)
    ·
      refine ⟨143983702381297859655550057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191978269841730479540733409 143983702381297859655550057)
      ·
        refine ⟨107987776785973394741662543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143983702381297859655550057 107987776785973394741662543)
        ·
          refine ⟨161981665178960092112493815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107987776785973394741662543 161981665178960092112493815)
          ·
            refine ⟨242972497768440138168740723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161981665178960092112493815 242972497768440138168740723)
            ·
              refine ⟨364458746652660207253111085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242972497768440138168740723 364458746652660207253111085)
              ·
                refine ⟨136672029994747577719916657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364458746652660207253111085 136672029994747577719916657)
                ·
                  refine ⟨102504022496060683289937493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136672029994747577719916657 102504022496060683289937493)
                  ·
                    refine ⟨1201219013625711132303955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102504022496060683289937493 1201219013625711132303955)
                    ·
                      rfl

theorem cell23_7018097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_7018097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018097 prefixEnd_7018097 := by exact prefixLift 7018097
  have htrace : WordTrace (prefixWord ++ tailWord_7018097) baseStart_7018097 baseEnd_7018097 := by
    simpa [prefixWord, tailWord_7018097, baseEnd_7018097] using wordTrace_append hprefix tailTrace_7018097
  have hstable : (prefixWord ++ tailWord_7018097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018097).length < 2 ^ (prefixWord ++ tailWord_7018097).sum := by decide
  have hdescent : baseEnd_7018097 < baseStart_7018097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018101 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_7018101 : Nat := 118140960795 + 7018101 * 2 ^ 59
def prefixEnd_7018101 : Nat := 4983230072969 + 3 ^ 40 * 7018101 * 2
def baseEnd_7018101 : Nat := 1201219698266583793753949

theorem tailTrace_7018101 : CollatzResearch.WordTrace tailWord_7018101 prefixEnd_7018101 1201219698266583793753949 := by
  unfold tailWord_7018101
  simp only [CollatzResearch.WordTrace]
  refine ⟨255971172347626148070790157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170647448231750765380526771 255971172347626148070790157)
  ·
    refine ⟨95989189630359805526546309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255971172347626148070790157 95989189630359805526546309)
    ·
      refine ⟨17997973055692463536227433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95989189630359805526546309 17997973055692463536227433)
      ·
        refine ⟨13498479791769347652170575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17997973055692463536227433 13498479791769347652170575)
        ·
          refine ⟨20247719687654021478255863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13498479791769347652170575 20247719687654021478255863)
          ·
            refine ⟨30371579531481032217383795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20247719687654021478255863 30371579531481032217383795)
            ·
              refine ⟨45557369297221548326075693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30371579531481032217383795 45557369297221548326075693)
              ·
                refine ⟨17084013486458080622278385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45557369297221548326075693 17084013486458080622278385)
                ·
                  refine ⟨12813010114843560466708789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17084013486458080622278385 12813010114843560466708789)
                  ·
                    refine ⟨1201219698266583793753949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12813010114843560466708789 1201219698266583793753949)
                    ·
                      rfl

theorem cell23_7018101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_7018101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018101 prefixEnd_7018101 := by exact prefixLift 7018101
  have htrace : WordTrace (prefixWord ++ tailWord_7018101) baseStart_7018101 baseEnd_7018101 := by
    simpa [prefixWord, tailWord_7018101, baseEnd_7018101] using wordTrace_append hprefix tailTrace_7018101
  have hstable : (prefixWord ++ tailWord_7018101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018101).length < 2 ^ (prefixWord ++ tailWord_7018101).sum := by decide
  have hdescent : baseEnd_7018101 < baseStart_7018101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018152 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 2, 5]
def baseStart_7018152 : Nat := 118140960795 + 7018152 * 2 ^ 59
def prefixEnd_7018152 : Nat := 4983230072969 + 3 ^ 40 * 7018152 * 2
def baseEnd_7018152 : Nat := 1201228427437710227241371

theorem tailTrace_7018152 : CollatzResearch.WordTrace tailWord_7018152 prefixEnd_7018152 1201228427437710227241371 := by
  unfold tailWord_7018152
  simp only [CollatzResearch.WordTrace]
  refine ⟨127986516235220691890448355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170648688313627589187264473 127986516235220691890448355)
  ·
    refine ⟨191979774352831037835672533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127986516235220691890448355 191979774352831037835672533)
    ·
      refine ⟨4499525961394477449273575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 191979774352831037835672533 4499525961394477449273575)
      ·
        refine ⟨6749288942091716173910363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4499525961394477449273575 6749288942091716173910363)
        ·
          refine ⟨10123933413137574260865545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749288942091716173910363 10123933413137574260865545)
          ·
            refine ⟨7592950059853180695649159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10123933413137574260865545 7592950059853180695649159)
            ·
              refine ⟨11389425089779771043473739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7592950059853180695649159 11389425089779771043473739)
              ·
                refine ⟨17084137634669656565210609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11389425089779771043473739 17084137634669656565210609)
                ·
                  refine ⟨12813103226002242423907957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17084137634669656565210609 12813103226002242423907957)
                  ·
                    refine ⟨1201228427437710227241371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12813103226002242423907957 1201228427437710227241371)
                    ·
                      rfl

theorem cell23_7018152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_7018152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018152 prefixEnd_7018152 := by exact prefixLift 7018152
  have htrace : WordTrace (prefixWord ++ tailWord_7018152) baseStart_7018152 baseEnd_7018152 := by
    simpa [prefixWord, tailWord_7018152, baseEnd_7018152] using wordTrace_append hprefix tailTrace_7018152
  have hstable : (prefixWord ++ tailWord_7018152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018152).length < 2 ^ (prefixWord ++ tailWord_7018152).sum := by decide
  have hdescent : baseEnd_7018152 < baseStart_7018152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018182 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_7018182 : Nat := 118140960795 + 7018182 * 2 ^ 59
def prefixEnd_7018182 : Nat := 4983230072969 + 3 ^ 40 * 7018182 * 2
def baseEnd_7018182 : Nat := 1201233562244255188116325

theorem tailTrace_7018182 : CollatzResearch.WordTrace tailWord_7018182 prefixEnd_7018182 1201233562244255188116325 := by
  unfold tailWord_7018182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7999191458135396840765275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170649417773555132602992533 7999191458135396840765275)
  ·
    refine ⟨11998787187203095261147913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7999191458135396840765275 11998787187203095261147913)
    ·
      refine ⟨8999090390402321445860935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11998787187203095261147913 8999090390402321445860935)
      ·
        refine ⟨13498635585603482168791403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8999090390402321445860935 13498635585603482168791403)
        ·
          refine ⟨20247953378405223253187105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13498635585603482168791403 20247953378405223253187105)
          ·
            refine ⟨15185965033803917439890329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20247953378405223253187105 15185965033803917439890329)
            ·
              refine ⟨11389473775352938079917747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15185965033803917439890329 11389473775352938079917747)
              ·
                refine ⟨17084210663029407119876621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11389473775352938079917747 17084210663029407119876621)
                ·
                  refine ⟨6406578998636027669953733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17084210663029407119876621 6406578998636027669953733)
                  ·
                    refine ⟨1201233562244255188116325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6406578998636027669953733 1201233562244255188116325)
                    ·
                      rfl

theorem cell23_7018182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_7018182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018182 prefixEnd_7018182 := by exact prefixLift 7018182
  have htrace : WordTrace (prefixWord ++ tailWord_7018182) baseStart_7018182 baseEnd_7018182 := by
    simpa [prefixWord, tailWord_7018182, baseEnd_7018182] using wordTrace_append hprefix tailTrace_7018182
  have hstable : (prefixWord ++ tailWord_7018182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018182).length < 2 ^ (prefixWord ++ tailWord_7018182).sum := by decide
  have hdescent : baseEnd_7018182 < baseStart_7018182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018258 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7018258 : Nat := 118140960795 + 7018258 * 2 ^ 59
def prefixEnd_7018258 : Nat := 4983230072969 + 3 ^ 40 * 7018258 * 2
def baseEnd_7018258 : Nat := 3603739711262507266998625

theorem tailTrace_7018258 : CollatzResearch.WordTrace tailWord_7018258 prefixEnd_7018258 3603739711262507266998625 := by
  unfold tailWord_7018258
  simp only [CollatzResearch.WordTrace]
  refine ⟨63994224652014340971063857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170651265738704909256170285 63994224652014340971063857)
  ·
    refine ⟨47995668489010755728297893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63994224652014340971063857 47995668489010755728297893)
    ·
      refine ⟨8999187841689516699055855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47995668489010755728297893 8999187841689516699055855)
      ·
        refine ⟨13498781762534275048583783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8999187841689516699055855 13498781762534275048583783)
        ·
          refine ⟨20248172643801412572875675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13498781762534275048583783 20248172643801412572875675)
          ·
            refine ⟨30372258965702118859313513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20248172643801412572875675 30372258965702118859313513)
            ·
              refine ⟨22779194224276589144485135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30372258965702118859313513 22779194224276589144485135)
              ·
                refine ⟨34168791336414883716727703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22779194224276589144485135 34168791336414883716727703)
                ·
                  refine ⟨51253187004622325575091555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34168791336414883716727703 51253187004622325575091555)
                  ·
                    refine ⟨76879780506933488362637333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51253187004622325575091555 76879780506933488362637333)
                    ·
                      refine ⟨3603739711262507266998625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76879780506933488362637333 3603739711262507266998625)
                      ·
                        rfl

theorem cell23_7018258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7018258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018258 prefixEnd_7018258 := by exact prefixLift 7018258
  have htrace : WordTrace (prefixWord ++ tailWord_7018258) baseStart_7018258 baseEnd_7018258 := by
    simpa [prefixWord, tailWord_7018258, baseEnd_7018258] using wordTrace_append hprefix tailTrace_7018258
  have hstable : (prefixWord ++ tailWord_7018258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018258).length < 2 ^ (prefixWord ++ tailWord_7018258).sum := by decide
  have hdescent : baseEnd_7018258 < baseStart_7018258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018339 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 1, 3, 2]
def baseStart_7018339 : Nat := 118140960795 + 7018339 * 2 ^ 59
def prefixEnd_7018339 : Nat := 4983230072969 + 3 ^ 40 * 7018339 * 2
def baseEnd_7018339 : Nat := 3603781303195521450085753

theorem tailTrace_7018339 : CollatzResearch.WordTrace tailWord_7018339 prefixEnd_7018339 3603781303195521450085753 := by
  unfold tailWord_7018339
  simp only [CollatzResearch.WordTrace]
  refine ⟨255979852920763914717954071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170653235280509276478636047 255979852920763914717954071)
  ·
    refine ⟨383969779381145872076931107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255979852920763914717954071 383969779381145872076931107)
    ·
      refine ⟨575954669071718808115396661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383969779381145872076931107 575954669071718808115396661)
      ·
        refine ⟨53995750225473638260818437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 575954669071718808115396661 53995750225473638260818437)
        ·
          refine ⟨10124203167276307173903457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53995750225473638260818437 10124203167276307173903457)
          ·
            refine ⟨7593152375457230380427593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10124203167276307173903457 7593152375457230380427593)
            ·
              refine ⟨5694864281592922785320695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7593152375457230380427593 5694864281592922785320695)
              ·
                refine ⟨8542296422389384177981043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5694864281592922785320695 8542296422389384177981043)
                ·
                  refine ⟨12813444633584076266971565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8542296422389384177981043 12813444633584076266971565)
                  ·
                    refine ⟨4805041737594028600114337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12813444633584076266971565 4805041737594028600114337)
                    ·
                      refine ⟨3603781303195521450085753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4805041737594028600114337 3603781303195521450085753)
                      ·
                        rfl

theorem cell23_7018339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_7018339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018339 prefixEnd_7018339 := by exact prefixLift 7018339
  have htrace : WordTrace (prefixWord ++ tailWord_7018339) baseStart_7018339 baseEnd_7018339 := by
    simpa [prefixWord, tailWord_7018339, baseEnd_7018339] using wordTrace_append hprefix tailTrace_7018339
  have hstable : (prefixWord ++ tailWord_7018339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018339).length < 2 ^ (prefixWord ++ tailWord_7018339).sum := by decide
  have hdescent : baseEnd_7018339 < baseStart_7018339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018346 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_7018346 : Nat := 118140960795 + 7018346 * 2 ^ 59
def prefixEnd_7018346 : Nat := 4983230072969 + 3 ^ 40 * 7018346 * 2
def baseEnd_7018346 : Nat := 3603784897560102922698221

theorem tailTrace_7018346 : CollatzResearch.WordTrace tailWord_7018346 prefixEnd_7018346 3603784897560102922698221 := by
  unfold tailWord_7018346
  simp only [CollatzResearch.WordTrace]
  refine ⟨63995027057934638728364723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170653405487825703275639261 63995027057934638728364723)
  ·
    refine ⟨95992540586901958092547085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63995027057934638728364723 95992540586901958092547085)
    ·
      refine ⟨35997202720088234284705157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95992540586901958092547085 35997202720088234284705157)
      ·
        refine ⟨6749475510016543928382217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35997202720088234284705157 6749475510016543928382217)
        ·
          refine ⟨5062106632512407946286663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6749475510016543928382217 5062106632512407946286663)
          ·
            refine ⟨7593159948768611919429995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062106632512407946286663 7593159948768611919429995)
            ·
              refine ⟨11389739923152917879144993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593159948768611919429995 11389739923152917879144993)
              ·
                refine ⟨8542304942364688409358745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11389739923152917879144993 8542304942364688409358745)
                ·
                  refine ⟨6406728706773516307019059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8542304942364688409358745 6406728706773516307019059)
                  ·
                    refine ⟨9610093060160274460528589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6406728706773516307019059 9610093060160274460528589)
                    ·
                      refine ⟨3603784897560102922698221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9610093060160274460528589 3603784897560102922698221)
                      ·
                        rfl

theorem cell23_7018346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_7018346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018346 prefixEnd_7018346 := by exact prefixLift 7018346
  have htrace : WordTrace (prefixWord ++ tailWord_7018346) baseStart_7018346 baseEnd_7018346 := by
    simpa [prefixWord, tailWord_7018346, baseEnd_7018346] using wordTrace_append hprefix tailTrace_7018346
  have hstable : (prefixWord ++ tailWord_7018346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018346).length < 2 ^ (prefixWord ++ tailWord_7018346).sum := by decide
  have hdescent : baseEnd_7018346 < baseStart_7018346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018369 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_7018369 : Nat := 118140960795 + 7018369 * 2 ^ 59
def prefixEnd_7018369 : Nat := 4983230072969 + 3 ^ 40 * 7018369 * 2
def baseEnd_7018369 : Nat := 3603796707615156332710615

theorem tailTrace_7018369 : CollatzResearch.WordTrace tailWord_7018369 prefixEnd_7018369 3603796707615156332710615 := by
  unfold tailWord_7018369
  simp only [CollatzResearch.WordTrace]
  refine ⟨255980947110655229841546161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170653964740436819894364107 255980947110655229841546161)
  ·
    refine ⟨191985710332991422381159621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255980947110655229841546161 191985710332991422381159621)
    ·
      refine ⟨35997320687435891696467429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191985710332991422381159621 35997320687435891696467429)
      ·
        refine ⟨6749497628894229693087643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35997320687435891696467429 6749497628894229693087643)
        ·
          refine ⟨10124246443341344539631465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749497628894229693087643 10124246443341344539631465)
          ·
            refine ⟨7593184832506008404723599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10124246443341344539631465 7593184832506008404723599)
            ·
              refine ⟨11389777248759012607085399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593184832506008404723599 11389777248759012607085399)
              ·
                refine ⟨17084665873138518910628099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11389777248759012607085399 17084665873138518910628099)
                ·
                  refine ⟨25626998809707778365942149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17084665873138518910628099 25626998809707778365942149)
                  ·
                    refine ⟨4805062276820208443614153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25626998809707778365942149 4805062276820208443614153)
                    ·
                      refine ⟨3603796707615156332710615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4805062276820208443614153 3603796707615156332710615)
                      ·
                        rfl

theorem cell23_7018369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_7018369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018369 prefixEnd_7018369 := by exact prefixLift 7018369
  have htrace : WordTrace (prefixWord ++ tailWord_7018369) baseStart_7018369 baseEnd_7018369 := by
    simpa [prefixWord, tailWord_7018369, baseEnd_7018369] using wordTrace_append hprefix tailTrace_7018369
  have hstable : (prefixWord ++ tailWord_7018369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018369).length < 2 ^ (prefixWord ++ tailWord_7018369).sum := by decide
  have hdescent : baseEnd_7018369 < baseStart_7018369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018371 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 1, 7]
def baseStart_7018371 : Nat := 118140960795 + 7018371 * 2 ^ 59
def prefixEnd_7018371 : Nat := 4983230072969 + 3 ^ 40 * 7018371 * 2
def baseEnd_7018371 : Nat := 1201265911525488441628535

theorem tailTrace_7018371 : CollatzResearch.WordTrace tailWord_7018371 prefixEnd_7018371 1201265911525488441628535 := by
  unfold tailWord_7018371
  simp only [CollatzResearch.WordTrace]
  refine ⟨255981020056647984183118967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170654013371098656122079311 255981020056647984183118967)
  ·
    refine ⟨383971530084971976274678451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255981020056647984183118967 383971530084971976274678451)
    ·
      refine ⟨575957295127457964412017677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383971530084971976274678451 575957295127457964412017677)
      ·
        refine ⟨215983985672796736654506629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575957295127457964412017677 215983985672796736654506629)
        ·
          refine ⟨40496997313649388122719993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215983985672796736654506629 40496997313649388122719993)
          ·
            refine ⟨30372747985237041092039995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40496997313649388122719993 30372747985237041092039995)
            ·
              refine ⟨45559121977855561638059993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30372747985237041092039995 45559121977855561638059993)
              ·
                refine ⟨34169341483391671228544995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45559121977855561638059993 34169341483391671228544995)
                ·
                  refine ⟨51254012225087506842817493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34169341483391671228544995 51254012225087506842817493)
                  ·
                    refine ⟨1201265911525488441628535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51254012225087506842817493 1201265911525488441628535)
                    ·
                      rfl

theorem cell23_7018371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 7].length) (baseStart_7018371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018371 prefixEnd_7018371 := by exact prefixLift 7018371
  have htrace : WordTrace (prefixWord ++ tailWord_7018371) baseStart_7018371 baseEnd_7018371 := by
    simpa [prefixWord, tailWord_7018371, baseEnd_7018371] using wordTrace_append hprefix tailTrace_7018371
  have hstable : (prefixWord ++ tailWord_7018371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018371).length < 2 ^ (prefixWord ++ tailWord_7018371).sum := by decide
  have hdescent : baseEnd_7018371 < baseStart_7018371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018388 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_7018388 : Nat := 118140960795 + 7018388 * 2 ^ 59
def prefixEnd_7018388 : Nat := 4983230072969 + 3 ^ 40 * 7018388 * 2
def baseEnd_7018388 : Nat := 1201268821249197252791009

theorem tailTrace_7018388 : CollatzResearch.WordTrace tailWord_7018388 prefixEnd_7018388 1201268821249197252791009 := by
  unfold tailWord_7018388
  simp only [CollatzResearch.WordTrace]
  refine ⟨127990820048793198043243909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170654426731724264057658545 127990820048793198043243909)
  ·
    refine ⟨23998278759148724633108233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127990820048793198043243909 23998278759148724633108233)
    ·
      refine ⟨17998709069361543474831175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23998278759148724633108233 17998709069361543474831175)
      ·
        refine ⟨26998063604042315212246763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17998709069361543474831175 26998063604042315212246763)
        ·
          refine ⟨40497095406063472818370145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26998063604042315212246763 40497095406063472818370145)
          ·
            refine ⟨30372821554547604613777609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40497095406063472818370145 30372821554547604613777609)
            ·
              refine ⟨22779616165910703460333207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30372821554547604613777609 22779616165910703460333207)
              ·
                refine ⟨34169424248866055190499811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22779616165910703460333207 34169424248866055190499811)
                ·
                  refine ⟨51254136373299082785749717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34169424248866055190499811 51254136373299082785749717)
                  ·
                    refine ⟨1201268821249197252791009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51254136373299082785749717 1201268821249197252791009)
                    ·
                      rfl

theorem cell23_7018388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_7018388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018388 prefixEnd_7018388 := by exact prefixLift 7018388
  have htrace : WordTrace (prefixWord ++ tailWord_7018388) baseStart_7018388 baseEnd_7018388 := by
    simpa [prefixWord, tailWord_7018388, baseEnd_7018388] using wordTrace_append hprefix tailTrace_7018388
  have hstable : (prefixWord ++ tailWord_7018388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018388).length < 2 ^ (prefixWord ++ tailWord_7018388).sum := by decide
  have hdescent : baseEnd_7018388 < baseStart_7018388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018420 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_7018420 : Nat := 118140960795 + 7018420 * 2 ^ 59
def prefixEnd_7018420 : Nat := 4983230072969 + 3 ^ 40 * 7018420 * 2
def baseEnd_7018420 : Nat := 3603822895128535633172881

theorem tailTrace_7018420 : CollatzResearch.WordTrace tailWord_7018420 prefixEnd_7018420 3603822895128535633172881 := by
  unfold tailWord_7018420
  simp only [CollatzResearch.WordTrace]
  refine ⟨127991403616735232775826357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170655204822313643701101809 127991403616735232775826357)
  ·
    refine ⟨11999194089068928072733721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127991403616735232775826357 11999194089068928072733721)
    ·
      refine ⟨8999395566801696054550291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11999194089068928072733721 8999395566801696054550291)
      ·
        refine ⟨13499093350202544081825437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8999395566801696054550291 13499093350202544081825437)
        ·
          refine ⟨5062160006325954030684539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13499093350202544081825437 5062160006325954030684539)
          ·
            refine ⟨7593240009488931046026809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062160006325954030684539 7593240009488931046026809)
            ·
              refine ⟨5694930007116698284520107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7593240009488931046026809 5694930007116698284520107)
              ·
                refine ⟨8542395010675047426780161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5694930007116698284520107 8542395010675047426780161)
                ·
                  refine ⟨6406796258006285570085121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8542395010675047426780161 6406796258006285570085121)
                  ·
                    refine ⟨4805097193504714177563841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6406796258006285570085121 4805097193504714177563841)
                    ·
                      refine ⟨3603822895128535633172881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4805097193504714177563841 3603822895128535633172881)
                      ·
                        rfl

theorem cell23_7018420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_7018420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018420 prefixEnd_7018420 := by exact prefixLift 7018420
  have htrace : WordTrace (prefixWord ++ tailWord_7018420) baseStart_7018420 baseEnd_7018420 := by
    simpa [prefixWord, tailWord_7018420, baseEnd_7018420] using wordTrace_append hprefix tailTrace_7018420
  have hstable : (prefixWord ++ tailWord_7018420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018420).length < 2 ^ (prefixWord ++ tailWord_7018420).sum := by decide
  have hdescent : baseEnd_7018420 < baseStart_7018420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018452 : List Nat := [2, 4, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_7018452 : Nat := 118140960795 + 7018452 * 2 ^ 59
def prefixEnd_7018452 : Nat := 4983230072969 + 3 ^ 40 * 7018452 * 2
def baseEnd_7018452 : Nat := 1201279775503159835990911

theorem tailTrace_7018452 : CollatzResearch.WordTrace tailWord_7018452 prefixEnd_7018452 1201279775503159835990911 := by
  unfold tailWord_7018452
  simp only [CollatzResearch.WordTrace]
  refine ⟨127991987184677267508408805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170655982912903023344545073 127991987184677267508408805)
  ·
    refine ⟨23998497597126987657826651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127991987184677267508408805 23998497597126987657826651)
    ·
      refine ⟨35997746395690481486739977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23998497597126987657826651 35997746395690481486739977)
      ·
        refine ⟨26998309796767861115054983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35997746395690481486739977 26998309796767861115054983)
        ·
          refine ⟨40497464695151791672582475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26998309796767861115054983 40497464695151791672582475)
          ·
            refine ⟨60746197042727687508873713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40497464695151791672582475 60746197042727687508873713)
            ·
              refine ⟨45559647782045765631655285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60746197042727687508873713 45559647782045765631655285)
              ·
                refine ⟨4271216979566790527967683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45559647782045765631655285 4271216979566790527967683)
                ·
                  refine ⟨6406825469350185791951525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271216979566790527967683 6406825469350185791951525)
                  ·
                    refine ⟨1201279775503159835990911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6406825469350185791951525 1201279775503159835990911)
                    ·
                      rfl

theorem cell23_7018452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_7018452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018452 prefixEnd_7018452 := by exact prefixLift 7018452
  have htrace : WordTrace (prefixWord ++ tailWord_7018452) baseStart_7018452 baseEnd_7018452 := by
    simpa [prefixWord, tailWord_7018452, baseEnd_7018452] using wordTrace_append hprefix tailTrace_7018452
  have hstable : (prefixWord ++ tailWord_7018452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018452).length < 2 ^ (prefixWord ++ tailWord_7018452).sum := by decide
  have hdescent : baseEnd_7018452 < baseStart_7018452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018508 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_7018508 : Nat := 118140960795 + 7018508 * 2 ^ 59
def prefixEnd_7018508 : Nat := 4983230072969 + 3 ^ 40 * 7018508 * 2
def baseEnd_7018508 : Nat := 1201289360475377096290825

theorem tailTrace_7018508 : CollatzResearch.WordTrace tailWord_7018508 prefixEnd_7018508 1201289360475377096290825 := by
  unfold tailWord_7018508
  simp only [CollatzResearch.WordTrace]
  refine ⟨127993008428575828290428089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170657344571434437720570785 127993008428575828290428089)
  ·
    refine ⟨95994756321431871217821067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127993008428575828290428089 95994756321431871217821067)
    ·
      refine ⟨143992134482147806826731601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95994756321431871217821067 143992134482147806826731601)
      ·
        refine ⟨107994100861610855120048701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143992134482147806826731601 107994100861610855120048701)
        ·
          refine ⟨40497787823104070670018263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107994100861610855120048701 40497787823104070670018263)
          ·
            refine ⟨60746681734656106005027395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40497787823104070670018263 60746681734656106005027395)
            ·
              refine ⟨91120022601984159007541093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60746681734656106005027395 91120022601984159007541093)
              ·
                refine ⟨17085004237872029813913955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91120022601984159007541093 17085004237872029813913955)
                ·
                  refine ⟨25627506356808044720870933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17085004237872029813913955 25627506356808044720870933)
                  ·
                    refine ⟨1201289360475377096290825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25627506356808044720870933 1201289360475377096290825)
                    ·
                      rfl

theorem cell23_7018508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_7018508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018508 prefixEnd_7018508 := by exact prefixLift 7018508
  have htrace : WordTrace (prefixWord ++ tailWord_7018508) baseStart_7018508 baseEnd_7018508 := by
    simpa [prefixWord, tailWord_7018508, baseEnd_7018508] using wordTrace_append hprefix tailTrace_7018508
  have hstable : (prefixWord ++ tailWord_7018508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018508).length < 2 ^ (prefixWord ++ tailWord_7018508).sum := by decide
  have hdescent : baseEnd_7018508 < baseStart_7018508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018516 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 6]
def baseStart_7018516 : Nat := 118140960795 + 7018516 * 2 ^ 59
def prefixEnd_7018516 : Nat := 4983230072969 + 3 ^ 40 * 7018516 * 2
def baseEnd_7018516 : Nat := 400430243252374139730271

theorem tailTrace_7018516 : CollatzResearch.WordTrace tailWord_7018516 prefixEnd_7018516 400430243252374139730271 := by
  unfold tailWord_7018516
  simp only [CollatzResearch.WordTrace]
  refine ⟨127993154320561336973573701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170657539094081782631431601 127993154320561336973573701)
  ·
    refine ⟨23998716435105250682545069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127993154320561336973573701 23998716435105250682545069)
    ·
      refine ⟨8999518663164469005954401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23998716435105250682545069 8999518663164469005954401)
      ·
        refine ⟨6749638997373351754465801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8999518663164469005954401 6749638997373351754465801)
        ·
          refine ⟨5062229248030013815849351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6749638997373351754465801 5062229248030013815849351)
          ·
            refine ⟨7593343872045020723774027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062229248030013815849351 7593343872045020723774027)
            ·
              refine ⟨11390015808067531085661041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593343872045020723774027 11390015808067531085661041)
              ·
                refine ⟨8542511856050648314245781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11390015808067531085661041 8542511856050648314245781)
                ·
                  refine ⟨400430243252374139730271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8542511856050648314245781 400430243252374139730271)
                  ·
                    rfl

theorem cell23_7018516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_7018516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018516 prefixEnd_7018516 := by exact prefixLift 7018516
  have htrace : WordTrace (prefixWord ++ tailWord_7018516) baseStart_7018516 baseEnd_7018516 := by
    simpa [prefixWord, tailWord_7018516, baseEnd_7018516] using wordTrace_append hprefix tailTrace_7018516
  have hstable : (prefixWord ++ tailWord_7018516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018516).length < 2 ^ (prefixWord ++ tailWord_7018516).sum := by decide
  have hdescent : baseEnd_7018516 < baseStart_7018516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018542 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_7018542 : Nat := 118140960795 + 7018542 * 2 ^ 59
def prefixEnd_7018542 : Nat := 4983230072969 + 3 ^ 40 * 7018542 * 2
def baseEnd_7018542 : Nat := 1201295179922794718615773

theorem tailTrace_7018542 : CollatzResearch.WordTrace tailWord_7018542 prefixEnd_7018542 1201295179922794718615773 := by
  unfold tailWord_7018542
  simp only [CollatzResearch.WordTrace]
  refine ⟨31998407117378560048449235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170658171292685653591729253 31998407117378560048449235)
  ·
    refine ⟨47997610676067840072673853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31998407117378560048449235 47997610676067840072673853)
    ·
      refine ⟨17999104003525440027252695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47997610676067840072673853 17999104003525440027252695)
      ·
        refine ⟨26998656005288160040879043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17999104003525440027252695 26998656005288160040879043)
        ·
          refine ⟨40497984007932240061318565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26998656005288160040879043 40497984007932240061318565)
          ·
            refine ⟨7593372001487295011497231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40497984007932240061318565 7593372001487295011497231)
            ·
              refine ⟨11390058002230942517245847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593372001487295011497231 11390058002230942517245847)
              ·
                refine ⟨17085087003346413775868771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11390058002230942517245847 17085087003346413775868771)
                ·
                  refine ⟨25627630505019620663803157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17085087003346413775868771 25627630505019620663803157)
                  ·
                    refine ⟨1201295179922794718615773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25627630505019620663803157 1201295179922794718615773)
                    ·
                      rfl

theorem cell23_7018542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_7018542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018542 prefixEnd_7018542 := by exact prefixLift 7018542
  have htrace : WordTrace (prefixWord ++ tailWord_7018542) baseStart_7018542 baseEnd_7018542 := by
    simpa [prefixWord, tailWord_7018542, baseEnd_7018542] using wordTrace_append hprefix tailTrace_7018542
  have hstable : (prefixWord ++ tailWord_7018542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018542).length < 2 ^ (prefixWord ++ tailWord_7018542).sum := by decide
  have hdescent : baseEnd_7018542 < baseStart_7018542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018545 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 4]
def baseStart_7018545 : Nat := 118140960795 + 7018545 * 2 ^ 59
def prefixEnd_7018545 : Nat := 4983230072969 + 3 ^ 40 * 7018545 * 2
def baseEnd_7018545 : Nat := 3603887080210347644109805

theorem tailTrace_7018545 : CollatzResearch.WordTrace tailWord_7018545 prefixEnd_7018545 3603887080210347644109805 := by
  unfold tailWord_7018545
  simp only [CollatzResearch.WordTrace]
  refine ⟨255987366358017611899953089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170658244238678407933302059 255987366358017611899953089)
  ·
    refine ⟨191990524768513208924964817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255987366358017611899953089 191990524768513208924964817)
    ·
      refine ⟨143992893576384906693723613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191990524768513208924964817 143992893576384906693723613)
      ·
        refine ⟨53997335091144340010146355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143992893576384906693723613 53997335091144340010146355)
        ·
          refine ⟨80996002636716510015219533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53997335091144340010146355 80996002636716510015219533)
          ·
            refine ⟨30373500988768691255707325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80996002636716510015219533 30373500988768691255707325)
            ·
              refine ⟨11390062870788259220890247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30373500988768691255707325 11390062870788259220890247)
              ·
                refine ⟨17085094306182388831335371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11390062870788259220890247 17085094306182388831335371)
                ·
                  refine ⟨25627641459273583247003057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17085094306182388831335371 25627641459273583247003057)
                  ·
                    refine ⟨19220731094455187435252293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25627641459273583247003057 19220731094455187435252293)
                    ·
                      refine ⟨3603887080210347644109805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19220731094455187435252293 3603887080210347644109805)
                      ·
                        rfl

theorem cell23_7018545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_7018545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018545 prefixEnd_7018545 := by exact prefixLift 7018545
  have htrace : WordTrace (prefixWord ++ tailWord_7018545) baseStart_7018545 baseEnd_7018545 := by
    simpa [prefixWord, tailWord_7018545, baseEnd_7018545] using wordTrace_append hprefix tailTrace_7018545
  have hstable : (prefixWord ++ tailWord_7018545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018545).length < 2 ^ (prefixWord ++ tailWord_7018545).sum := by decide
  have hdescent : baseEnd_7018545 < baseStart_7018545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018690 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_7018690 : Nat := 118140960795 + 7018690 * 2 ^ 59
def prefixEnd_7018690 : Nat := 4983230072969 + 3 ^ 40 * 7018690 * 2
def baseEnd_7018690 : Nat := 3603961534905249576796639

theorem tailTrace_7018690 : CollatzResearch.WordTrace tailWord_7018690 prefixEnd_7018690 3603961534905249576796639 := by
  unfold tailWord_7018690
  simp only [CollatzResearch.WordTrace]
  refine ⟨63998163735623075415995381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170661769961661534442654349 63998163735623075415995381)
  ·
    refine ⟨5999827850214663320249567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63998163735623075415995381 5999827850214663320249567)
    ·
      refine ⟨8999741775321994980374351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5999827850214663320249567 8999741775321994980374351)
      ·
        refine ⟨13499612662982992470561527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8999741775321994980374351 13499612662982992470561527)
        ·
          refine ⟨20249418994474488705842291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13499612662982992470561527 20249418994474488705842291)
          ·
            refine ⟨30374128491711733058763437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20249418994474488705842291 30374128491711733058763437)
            ·
              refine ⟨11390298184391899897036289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30374128491711733058763437 11390298184391899897036289)
              ·
                refine ⟨8542723638293924922777217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11390298184391899897036289 8542723638293924922777217)
                ·
                  refine ⟨6407042728720443692082913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8542723638293924922777217 6407042728720443692082913)
                  ·
                    refine ⟨4805282046540332769062185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6407042728720443692082913 4805282046540332769062185)
                    ·
                      refine ⟨3603961534905249576796639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4805282046540332769062185 3603961534905249576796639)
                      ·
                        rfl

theorem cell23_7018690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_7018690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018690 prefixEnd_7018690 := by exact prefixLift 7018690
  have htrace : WordTrace (prefixWord ++ tailWord_7018690) baseStart_7018690 baseEnd_7018690 := by
    simpa [prefixWord, tailWord_7018690, baseEnd_7018690] using wordTrace_append hprefix tailTrace_7018690
  have hstable : (prefixWord ++ tailWord_7018690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018690).length < 2 ^ (prefixWord ++ tailWord_7018690).sum := by decide
  have hdescent : baseEnd_7018690 < baseStart_7018690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018715 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 3]
def baseStart_7018715 : Nat := 118140960795 + 7018715 * 2 ^ 59
def prefixEnd_7018715 : Nat := 4983230072969 + 3 ^ 40 * 7018715 * 2
def baseEnd_7018715 : Nat := 3603974371921611978984023

theorem tailTrace_7018715 : CollatzResearch.WordTrace tailWord_7018715 prefixEnd_7018715 3603974371921611978984023 := by
  unfold tailWord_7018715
  simp only [CollatzResearch.WordTrace]
  refine ⟨255993566767401730933641599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170662377844934487289094399 255993566767401730933641599)
  ·
    refine ⟨383990350151102596400462399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255993566767401730933641599 383990350151102596400462399)
    ·
      refine ⟨575985525226653894600693599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383990350151102596400462399 575985525226653894600693599)
      ·
        refine ⟨863978287839980841901040399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575985525226653894600693599 863978287839980841901040399)
        ·
          refine ⟨1295967431759971262851560599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863978287839980841901040399 1295967431759971262851560599)
          ·
            refine ⟨1943951147639956894277340899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295967431759971262851560599 1943951147639956894277340899)
            ·
              refine ⟨2915926721459935341416011349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1943951147639956894277340899 2915926721459935341416011349)
              ·
                refine ⟨34171016267108617282218883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2915926721459935341416011349 34171016267108617282218883)
                ·
                  refine ⟨51256524400662925923328325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34171016267108617282218883 51256524400662925923328325)
                  ·
                    refine ⟨9610598325124298610624061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51256524400662925923328325 9610598325124298610624061)
                    ·
                      refine ⟨3603974371921611978984023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9610598325124298610624061 3603974371921611978984023)
                      ·
                        rfl

theorem cell23_7018715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 3].length) (baseStart_7018715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018715 prefixEnd_7018715 := by exact prefixLift 7018715
  have htrace : WordTrace (prefixWord ++ tailWord_7018715) baseStart_7018715 baseEnd_7018715 := by
    simpa [prefixWord, tailWord_7018715, baseEnd_7018715] using wordTrace_append hprefix tailTrace_7018715
  have hstable : (prefixWord ++ tailWord_7018715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018715).length < 2 ^ (prefixWord ++ tailWord_7018715).sum := by decide
  have hdescent : baseEnd_7018715 < baseStart_7018715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018732 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 3]
def baseStart_7018732 : Nat := 118140960795 + 7018732 * 2 ^ 59
def prefixEnd_7018732 : Nat := 4983230072969 + 3 ^ 40 * 7018732 * 2
def baseEnd_7018732 : Nat := 3603983101092738412471445

theorem tailTrace_7018732 : CollatzResearch.WordTrace tailWord_7018732 prefixEnd_7018732 3603983101092738412471445 := by
  unfold tailWord_7018732
  simp only [CollatzResearch.WordTrace]
  refine ⟨127997093404170071418505225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170662791205560095224673633 127997093404170071418505225)
  ·
    refine ⟨95997820053127553563878919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127997093404170071418505225 95997820053127553563878919)
    ·
      refine ⟨143996730079691330345818379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95997820053127553563878919 143996730079691330345818379)
      ·
        refine ⟨215995095119536995518727569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143996730079691330345818379 215995095119536995518727569)
        ·
          refine ⟨161996321339652746639045677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215995095119536995518727569 161996321339652746639045677)
          ·
            refine ⟨60748620502369779989642129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161996321339652746639045677 60748620502369779989642129)
            ·
              refine ⟨45561465376777334992231597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60748620502369779989642129 45561465376777334992231597)
              ·
                refine ⟨17085549516291500622086849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45561465376777334992231597 17085549516291500622086849)
                ·
                  refine ⟨12814162137218625466565137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17085549516291500622086849 12814162137218625466565137)
                  ·
                    refine ⟨9610621602913969099923853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12814162137218625466565137 9610621602913969099923853)
                    ·
                      refine ⟨3603983101092738412471445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9610621602913969099923853 3603983101092738412471445)
                      ·
                        rfl

theorem cell23_7018732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_7018732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018732 prefixEnd_7018732 := by exact prefixLift 7018732
  have htrace : WordTrace (prefixWord ++ tailWord_7018732) baseStart_7018732 baseEnd_7018732 := by
    simpa [prefixWord, tailWord_7018732, baseEnd_7018732] using wordTrace_append hprefix tailTrace_7018732
  have hstable : (prefixWord ++ tailWord_7018732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018732).length < 2 ^ (prefixWord ++ tailWord_7018732).sum := by decide
  have hdescent : baseEnd_7018732 < baseStart_7018732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018735 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 8]
def baseStart_7018735 : Nat := 118140960795 + 7018735 * 2 ^ 59
def prefixEnd_7018735 : Nat := 4983230072969 + 3 ^ 40 * 7018735 * 2
def baseEnd_7018735 : Nat := 400442737948300211192659

theorem tailTrace_7018735 : CollatzResearch.WordTrace tailWord_7018735 prefixEnd_7018735 400442737948300211192659 := by
  unfold tailWord_7018735
  simp only [CollatzResearch.WordTrace]
  refine ⟨255994296227329274349369659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170662864151552849566246439 255994296227329274349369659)
  ·
    refine ⟨383991444340993911524054489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255994296227329274349369659 383991444340993911524054489)
    ·
      refine ⟨287993583255745433643040867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383991444340993911524054489 287993583255745433643040867)
      ·
        refine ⟨431990374883618150464561301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287993583255745433643040867 431990374883618150464561301)
        ·
          refine ⟨20249548822669600803026311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 431990374883618150464561301 20249548822669600803026311)
          ·
            refine ⟨30374323234004401204539467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20249548822669600803026311 30374323234004401204539467)
            ·
              refine ⟨45561484851006601806809201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30374323234004401204539467 45561484851006601806809201)
              ·
                refine ⟨34171113638254951355106901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45561484851006601806809201 34171113638254951355106901)
                ·
                  refine ⟨400442737948300211192659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34171113638254951355106901 400442737948300211192659)
                  ·
                    rfl

theorem cell23_7018735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 8].length) (baseStart_7018735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018735 prefixEnd_7018735 := by exact prefixLift 7018735
  have htrace : WordTrace (prefixWord ++ tailWord_7018735) baseStart_7018735 baseEnd_7018735 := by
    simpa [prefixWord, tailWord_7018735, baseEnd_7018735] using wordTrace_append hprefix tailTrace_7018735
  have hstable : (prefixWord ++ tailWord_7018735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018735).length < 2 ^ (prefixWord ++ tailWord_7018735).sum := by decide
  have hdescent : baseEnd_7018735 < baseStart_7018735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018756 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_7018756 : Nat := 118140960795 + 7018756 * 2 ^ 59
def prefixEnd_7018756 : Nat := 4983230072969 + 3 ^ 40 * 7018756 * 2
def baseEnd_7018756 : Nat := 1201331808209482106190445

theorem tailTrace_7018756 : CollatzResearch.WordTrace tailWord_7018756 prefixEnd_7018756 1201331808209482106190445 := by
  unfold tailWord_7018756
  simp only [CollatzResearch.WordTrace]
  refine ⟨127997531080126597467942061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170663374773502129957256081 127997531080126597467942061)
  ·
    refine ⟨47999074155047474050478273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127997531080126597467942061 47999074155047474050478273)
    ·
      refine ⟨35999305616285605537858705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47999074155047474050478273 35999305616285605537858705)
      ·
        refine ⟨26999479212214204153394029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35999305616285605537858705 26999479212214204153394029)
        ·
          refine ⟨10124804704580326557522761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26999479212214204153394029 10124804704580326557522761)
          ·
            refine ⟨7593603528435244918142071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10124804704580326557522761 7593603528435244918142071)
            ·
              refine ⟨11390405292652867377213107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593603528435244918142071 11390405292652867377213107)
              ·
                refine ⟨17085607938979301065819661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11390405292652867377213107 17085607938979301065819661)
                ·
                  refine ⟨6407102977117237899682373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17085607938979301065819661 6407102977117237899682373)
                  ·
                    refine ⟨1201331808209482106190445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6407102977117237899682373 1201331808209482106190445)
                    ·
                      rfl

theorem cell23_7018756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_7018756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018756 prefixEnd_7018756 := by exact prefixLift 7018756
  have htrace : WordTrace (prefixWord ++ tailWord_7018756) baseStart_7018756 baseEnd_7018756 := by
    simpa [prefixWord, tailWord_7018756, baseEnd_7018756] using wordTrace_append hprefix tailTrace_7018756
  have hstable : (prefixWord ++ tailWord_7018756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018756).length < 2 ^ (prefixWord ++ tailWord_7018756).sum := by decide
  have hdescent : baseEnd_7018756 < baseStart_7018756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018769 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 6]
def baseStart_7018769 : Nat := 118140960795 + 7018769 * 2 ^ 59
def prefixEnd_7018769 : Nat := 4983230072969 + 3 ^ 40 * 7018769 * 2
def baseEnd_7018769 : Nat := 400444677764106085300975

theorem tailTrace_7018769 : CollatzResearch.WordTrace tailWord_7018769 prefixEnd_7018769 400444677764106085300975 := by
  unfold tailWord_7018769
  simp only [CollatzResearch.WordTrace]
  refine ⟨255995536309206098156107361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170663690872804065437404907 255995536309206098156107361)
  ·
    refine ⟨191996652231904573617080521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255995536309206098156107361 191996652231904573617080521)
    ·
      refine ⟨143997489173928430212810391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191996652231904573617080521 143997489173928430212810391)
      ·
        refine ⟨215996233760892645319215587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143997489173928430212810391 215996233760892645319215587)
        ·
          refine ⟨323994350641338967978823381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215996233760892645319215587 323994350641338967978823381)
          ·
            refine ⟨7593617593156382062003673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 323994350641338967978823381 7593617593156382062003673)
            ·
              refine ⟨5695213194867286546502755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7593617593156382062003673 5695213194867286546502755)
              ·
                refine ⟨8542819792300929819754133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5695213194867286546502755 8542819792300929819754133)
                ·
                  refine ⟨400444677764106085300975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8542819792300929819754133 400444677764106085300975)
                  ·
                    rfl

theorem cell23_7018769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 6].length) (baseStart_7018769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018769 prefixEnd_7018769 := by exact prefixLift 7018769
  have htrace : WordTrace (prefixWord ++ tailWord_7018769) baseStart_7018769 baseEnd_7018769 := by
    simpa [prefixWord, tailWord_7018769, baseEnd_7018769] using wordTrace_append hprefix tailTrace_7018769
  have hstable : (prefixWord ++ tailWord_7018769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018769).length < 2 ^ (prefixWord ++ tailWord_7018769).sum := by decide
  have hdescent : baseEnd_7018769 < baseStart_7018769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018832 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 4]
def baseStart_7018832 : Nat := 118140960795 + 7018832 * 2 ^ 59
def prefixEnd_7018832 : Nat := 4983230072969 + 3 ^ 40 * 7018832 * 2
def baseEnd_7018832 : Nat := 3604034449158188021220985

theorem tailTrace_7018832 : CollatzResearch.WordTrace tailWord_7018832 prefixEnd_7018832 3604034449158188021220985 := by
  unfold tailWord_7018832
  simp only [CollatzResearch.WordTrace]
  refine ⟨127998917053988929957825375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170665222738651906610433833 127998917053988929957825375)
  ·
    refine ⟨191998375580983394936738063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127998917053988929957825375 191998375580983394936738063)
    ·
      refine ⟨287997563371475092405107095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191998375580983394936738063 287997563371475092405107095)
      ·
        refine ⟨431996345057212638607660643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287997563371475092405107095 431996345057212638607660643)
        ·
          refine ⟨647994517585818957911490965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431996345057212638607660643 647994517585818957911490965)
          ·
            refine ⟨30374743011835263652101139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 647994517585818957911490965 30374743011835263652101139)
            ·
              refine ⟨45562114517752895478151709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30374743011835263652101139 45562114517752895478151709)
              ·
                refine ⟨17085792944157335804306891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45562114517752895478151709 17085792944157335804306891)
                ·
                  refine ⟨25628689416236003706460337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17085792944157335804306891 25628689416236003706460337)
                  ·
                    refine ⟨19221517062177002779845253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25628689416236003706460337 19221517062177002779845253)
                    ·
                      refine ⟨3604034449158188021220985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19221517062177002779845253 3604034449158188021220985)
                      ·
                        rfl

theorem cell23_7018832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_7018832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018832 prefixEnd_7018832 := by exact prefixLift 7018832
  have htrace : WordTrace (prefixWord ++ tailWord_7018832) baseStart_7018832 baseEnd_7018832 := by
    simpa [prefixWord, tailWord_7018832, baseEnd_7018832] using wordTrace_append hprefix tailTrace_7018832
  have hstable : (prefixWord ++ tailWord_7018832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018832).length < 2 ^ (prefixWord ++ tailWord_7018832).sum := by decide
  have hdescent : baseEnd_7018832 < baseStart_7018832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018836 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_7018836 : Nat := 118140960795 + 7018836 * 2 ^ 59
def prefixEnd_7018836 : Nat := 4983230072969 + 3 ^ 40 * 7018836 * 2
def baseEnd_7018836 : Nat := 3604036503080806005570967

theorem tailTrace_7018836 : CollatzResearch.WordTrace tailWord_7018836 prefixEnd_7018836 3604036503080806005570967 := by
  unfold tailWord_7018836
  simp only [CollatzResearch.WordTrace]
  refine ⟨127998989999981684299398181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170665319999975579065864241 127998989999981684299398181)
  ·
    refine ⟨23999810624996565806137159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127998989999981684299398181 23999810624996565806137159)
    ·
      refine ⟨35999715937494848709205739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23999810624996565806137159 35999715937494848709205739)
      ·
        refine ⟨53999573906242273063808609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35999715937494848709205739 53999573906242273063808609)
        ·
          refine ⟨40499680429681704797856457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53999573906242273063808609 40499680429681704797856457)
          ·
            refine ⟨30374760322261278598392343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40499680429681704797856457 30374760322261278598392343)
            ·
              refine ⟨45562140483391917897588515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30374760322261278598392343 45562140483391917897588515)
              ·
                refine ⟨68343210725087876846382773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45562140483391917897588515 68343210725087876846382773)
                ·
                  refine ⟨6407176005476988454348385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68343210725087876846382773 6407176005476988454348385)
                  ·
                    refine ⟨4805382004107741340761289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6407176005476988454348385 4805382004107741340761289)
                    ·
                      refine ⟨3604036503080806005570967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4805382004107741340761289 3604036503080806005570967)
                      ·
                        rfl

theorem cell23_7018836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_7018836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018836 prefixEnd_7018836 := by exact prefixLift 7018836
  have htrace : WordTrace (prefixWord ++ tailWord_7018836) baseStart_7018836 baseEnd_7018836 := by
    simpa [prefixWord, tailWord_7018836, baseEnd_7018836] using wordTrace_append hprefix tailTrace_7018836
  have hstable : (prefixWord ++ tailWord_7018836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018836).length < 2 ^ (prefixWord ++ tailWord_7018836).sum := by decide
  have hdescent : baseEnd_7018836 < baseStart_7018836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018839 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 1, 2, 3]
def baseStart_7018839 : Nat := 118140960795 + 7018839 * 2 ^ 59
def prefixEnd_7018839 : Nat := 4983230072969 + 3 ^ 40 * 7018839 * 2
def baseEnd_7018839 : Nat := 3604038043522769493833453

theorem tailTrace_7018839 : CollatzResearch.WordTrace tailWord_7018839 prefixEnd_7018839 3604038043522769493833453 := by
  unfold tailWord_7018839
  simp only [CollatzResearch.WordTrace]
  refine ⟨255998089418952500111155571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170665392945968333407437047 255998089418952500111155571)
  ·
    refine ⟨383997134128428750166733357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255998089418952500111155571 383997134128428750166733357)
    ·
      refine ⟨143998925298160781312525009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383997134128428750166733357 143998925298160781312525009)
      ·
        refine ⟨107999193973620585984393757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143998925298160781312525009 107999193973620585984393757)
        ·
          refine ⟨40499697740107719744147659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107999193973620585984393757 40499697740107719744147659)
          ·
            refine ⟨60749546610161579616221489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40499697740107719744147659 60749546610161579616221489)
            ·
              refine ⟨45562159957621184712166117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60749546610161579616221489 45562159957621184712166117)
              ·
                refine ⟨8542904992053972133531147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45562159957621184712166117 8542904992053972133531147)
                ·
                  refine ⟨12814357488080958200296721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8542904992053972133531147 12814357488080958200296721)
                  ·
                    refine ⟨9610768116060718650222541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12814357488080958200296721 9610768116060718650222541)
                    ·
                      refine ⟨3604038043522769493833453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9610768116060718650222541 3604038043522769493833453)
                      ·
                        rfl

theorem cell23_7018839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_7018839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018839 prefixEnd_7018839 := by exact prefixLift 7018839
  have htrace : WordTrace (prefixWord ++ tailWord_7018839) baseStart_7018839 baseEnd_7018839 := by
    simpa [prefixWord, tailWord_7018839, baseEnd_7018839] using wordTrace_append hprefix tailTrace_7018839
  have hstable : (prefixWord ++ tailWord_7018839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018839).length < 2 ^ (prefixWord ++ tailWord_7018839).sum := by decide
  have hdescent : baseEnd_7018839 < baseStart_7018839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018853 : List Nat := [1, 3, 1, 3, 1, 3, 1, 5, 1, 2, 2]
def baseStart_7018853 : Nat := 118140960795 + 7018853 * 2 ^ 59
def prefixEnd_7018853 : Nat := 4983230072969 + 3 ^ 40 * 7018853 * 2
def baseEnd_7018853 : Nat := 3604045232251932439058389

theorem tailTrace_7018853 : CollatzResearch.WordTrace tailWord_7018853 prefixEnd_7018853 3604045232251932439058389 := by
  unfold tailWord_7018853
  simp only [CollatzResearch.WordTrace]
  refine ⟨255998600040901780502165213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170665733360601187001443475 255998600040901780502165213)
  ·
    refine ⟨95999475015338167688311955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255998600040901780502165213 95999475015338167688311955)
    ·
      refine ⟨143999212523007251532467933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95999475015338167688311955 143999212523007251532467933)
      ·
        refine ⟨53999704696127719324675475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143999212523007251532467933 53999704696127719324675475)
        ·
          refine ⟨80999557044191578987013213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53999704696127719324675475 80999557044191578987013213)
          ·
            refine ⟨30374833891571842120129955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80999557044191578987013213 30374833891571842120129955)
            ·
              refine ⟨45562250837357763180194933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30374833891571842120129955 45562250837357763180194933)
              ·
                refine ⟨4271461016002290298143275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45562250837357763180194933 4271461016002290298143275)
                ·
                  refine ⟨6407191524003435447214913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271461016002290298143275 6407191524003435447214913)
                  ·
                    refine ⟨4805393643002576585411185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6407191524003435447214913 4805393643002576585411185)
                    ·
                      refine ⟨3604045232251932439058389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4805393643002576585411185 3604045232251932439058389)
                      ·
                        rfl

theorem cell23_7018853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_7018853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018853 prefixEnd_7018853 := by exact prefixLift 7018853
  have htrace : WordTrace (prefixWord ++ tailWord_7018853) baseStart_7018853 baseEnd_7018853 := by
    simpa [prefixWord, tailWord_7018853, baseEnd_7018853] using wordTrace_append hprefix tailTrace_7018853
  have hstable : (prefixWord ++ tailWord_7018853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018853).length < 2 ^ (prefixWord ++ tailWord_7018853).sum := by decide
  have hdescent : baseEnd_7018853 < baseStart_7018853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018856 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_7018856 : Nat := 118140960795 + 7018856 * 2 ^ 59
def prefixEnd_7018856 : Nat := 4983230072969 + 3 ^ 40 * 7018856 * 2
def baseEnd_7018856 : Nat := 3604046772693895927320875

theorem tailTrace_7018856 : CollatzResearch.WordTrace tailWord_7018856 prefixEnd_7018856 3604046772693895927320875 := by
  unfold tailWord_7018856
  simp only [CollatzResearch.WordTrace]
  refine ⟨127999354729945456007262211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170665806306593941343016281 127999354729945456007262211)
  ·
    refine ⟨191999032094918184010893317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127999354729945456007262211 191999032094918184010893317)
    ·
      refine ⟨35999818517797159502042497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191999032094918184010893317 35999818517797159502042497)
      ·
        refine ⟨26999863888347869626531873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35999818517797159502042497 26999863888347869626531873)
        ·
          refine ⟨20249897916260902219898905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26999863888347869626531873 20249897916260902219898905)
          ·
            refine ⟨15187423437195676664924179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20249897916260902219898905 15187423437195676664924179)
            ·
              refine ⟨22781135155793514997386269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15187423437195676664924179 22781135155793514997386269)
              ·
                refine ⟨8542925683422568124019851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22781135155793514997386269 8542925683422568124019851)
                ·
                  refine ⟨12814388525133852186029777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8542925683422568124019851 12814388525133852186029777)
                  ·
                    refine ⟨9610791393850389139522333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12814388525133852186029777 9610791393850389139522333)
                    ·
                      refine ⟨3604046772693895927320875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9610791393850389139522333 3604046772693895927320875)
                      ·
                        rfl

theorem cell23_7018856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_7018856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018856 prefixEnd_7018856 := by exact prefixLift 7018856
  have htrace : WordTrace (prefixWord ++ tailWord_7018856) baseStart_7018856 baseEnd_7018856 := by
    simpa [prefixWord, tailWord_7018856, baseEnd_7018856] using wordTrace_append hprefix tailTrace_7018856
  have hstable : (prefixWord ++ tailWord_7018856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018856).length < 2 ^ (prefixWord ++ tailWord_7018856).sum := by decide
  have hdescent : baseEnd_7018856 < baseStart_7018856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018912 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_7018912 : Nat := 118140960795 + 7018912 * 2 ^ 59
def prefixEnd_7018912 : Nat := 4983230072969 + 3 ^ 40 * 7018912 * 2
def baseEnd_7018912 : Nat := 3604075527610547708220617

theorem tailTrace_7018912 : CollatzResearch.WordTrace tailWord_7018912 prefixEnd_7018912 3604075527610547708220617 := by
  unfold tailWord_7018912
  simp only [CollatzResearch.WordTrace]
  refine ⟨128000375973844016789281495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170667167965125355719041993 128000375973844016789281495)
  ·
    refine ⟨192000563960766025183922243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128000375973844016789281495 192000563960766025183922243)
    ·
      refine ⟨288000845941149037775883365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192000563960766025183922243 288000845941149037775883365)
      ·
        refine ⟨54000158613965444582978131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288000845941149037775883365 54000158613965444582978131)
        ·
          refine ⟨81000237920948166874467197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54000158613965444582978131 81000237920948166874467197)
          ·
            refine ⟨30375089220355562577925199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81000237920948166874467197 30375089220355562577925199)
            ·
              refine ⟨45562633830533343866887799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30375089220355562577925199 45562633830533343866887799)
              ·
                refine ⟨68343950745800015800331699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45562633830533343866887799 68343950745800015800331699)
                ·
                  refine ⟨102515926118700023700497549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68343950745800015800331699 102515926118700023700497549)
                  ·
                    refine ⟨38443472294512508887686581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102515926118700023700497549 38443472294512508887686581)
                    ·
                      refine ⟨3604075527610547708220617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38443472294512508887686581 3604075527610547708220617)
                      ·
                        rfl

theorem cell23_7018912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_7018912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018912 prefixEnd_7018912 := by exact prefixLift 7018912
  have htrace : WordTrace (prefixWord ++ tailWord_7018912) baseStart_7018912 baseEnd_7018912 := by
    simpa [prefixWord, tailWord_7018912, baseEnd_7018912] using wordTrace_append hprefix tailTrace_7018912
  have hstable : (prefixWord ++ tailWord_7018912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018912).length < 2 ^ (prefixWord ++ tailWord_7018912).sum := by decide
  have hdescent : baseEnd_7018912 < baseStart_7018912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7018986 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_7018986 : Nat := 118140960795 + 7018986 * 2 ^ 59
def prefixEnd_7018986 : Nat := 4983230072969 + 3 ^ 40 * 7018986 * 2
def baseEnd_7018986 : Nat := 3604113525178980418695277

theorem tailTrace_7018986 : CollatzResearch.WordTrace tailWord_7018986 prefixEnd_7018986 3604113525178980418695277 := by
  unfold tailWord_7018986
  simp only [CollatzResearch.WordTrace]
  refine ⟨64000862737354986054189203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170668967299613296144504541 64000862737354986054189203)
  ·
    refine ⟨96001294106032479081283805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64000862737354986054189203 96001294106032479081283805)
    ·
      refine ⟨36000485289762179655481427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96001294106032479081283805 36000485289762179655481427)
      ·
        refine ⟨54000727934643269483222141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36000485289762179655481427 54000727934643269483222141)
        ·
          refine ⟨20250272975491226056208303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54000727934643269483222141 20250272975491226056208303)
          ·
            refine ⟨30375409463236839084312455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20250272975491226056208303 30375409463236839084312455)
            ·
              refine ⟨45563114194855258626468683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30375409463236839084312455 45563114194855258626468683)
              ·
                refine ⟨68344671292282887939703025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45563114194855258626468683 68344671292282887939703025)
                ·
                  refine ⟨51258503469212165954777269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68344671292282887939703025 51258503469212165954777269)
                  ·
                    refine ⟨4805484700238640558260369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51258503469212165954777269 4805484700238640558260369)
                    ·
                      refine ⟨3604113525178980418695277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4805484700238640558260369 3604113525178980418695277)
                      ·
                        rfl

theorem cell23_7018986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_7018986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7018986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7018986 prefixEnd_7018986 := by exact prefixLift 7018986
  have htrace : WordTrace (prefixWord ++ tailWord_7018986) baseStart_7018986 baseEnd_7018986 := by
    simpa [prefixWord, tailWord_7018986, baseEnd_7018986] using wordTrace_append hprefix tailTrace_7018986
  have hstable : (prefixWord ++ tailWord_7018986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7018986).length < 2 ^ (prefixWord ++ tailWord_7018986).sum := by decide
  have hdescent : baseEnd_7018986 < baseStart_7018986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7018986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019043 : List Nat := [1, 1, 1, 4, 4, 1, 2, 4, 1, 4]
def baseStart_7019043 : Nat := 118140960795 + 7019043 * 2 ^ 59
def prefixEnd_7019043 : Nat := 4983230072969 + 3 ^ 40 * 7019043 * 2
def baseEnd_7019043 : Nat := 1201380931192095565227505

theorem tailTrace_7019043 : CollatzResearch.WordTrace tailWord_7019043 prefixEnd_7019043 1201380931192095565227505 := by
  unfold tailWord_7019043
  simp only [CollatzResearch.WordTrace]
  refine ⟨256005529910213442951581783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170670353273475628634387855 256005529910213442951581783)
  ·
    refine ⟨384008294865320164427372675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256005529910213442951581783 384008294865320164427372675)
    ·
      refine ⟨576012442297980246641059013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384008294865320164427372675 576012442297980246641059013)
      ·
        refine ⟨108002332930871296245198565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 576012442297980246641059013 108002332930871296245198565)
        ·
          refine ⟨20250437424538368045974731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108002332930871296245198565 20250437424538368045974731)
          ·
            refine ⟨30375656136807552068962097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20250437424538368045974731 30375656136807552068962097)
            ·
              refine ⟨22781742102605664051721573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30375656136807552068962097 22781742102605664051721573)
              ·
                refine ⟨4271576644238562009697795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22781742102605664051721573 4271576644238562009697795)
                ·
                  refine ⟨6407364966357843014546693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271576644238562009697795 6407364966357843014546693)
                  ·
                    refine ⟨1201380931192095565227505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6407364966357843014546693 1201380931192095565227505)
                    ·
                      rfl

theorem cell23_7019043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 1, 4].length) (baseStart_7019043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019043 prefixEnd_7019043 := by exact prefixLift 7019043
  have htrace : WordTrace (prefixWord ++ tailWord_7019043) baseStart_7019043 baseEnd_7019043 := by
    simpa [prefixWord, tailWord_7019043, baseEnd_7019043] using wordTrace_append hprefix tailTrace_7019043
  have hstable : (prefixWord ++ tailWord_7019043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019043).length < 2 ^ (prefixWord ++ tailWord_7019043).sum := by decide
  have hdescent : baseEnd_7019043 < baseStart_7019043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019086 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_7019086 : Nat := 118140960795 + 7019086 * 2 ^ 59
def prefixEnd_7019086 : Nat := 4983230072969 + 3 ^ 40 * 7019086 * 2
def baseEnd_7019086 : Nat := 1201388291081476675814939

theorem tailTrace_7019086 : CollatzResearch.WordTrace tailWord_7019086 prefixEnd_7019086 1201388291081476675814939 := by
  unfold tailWord_7019086
  simp only [CollatzResearch.WordTrace]
  refine ⟨32000887281132207661924639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170671398832705107530264741 32000887281132207661924639)
  ·
    refine ⟨48001330921698311492886959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32000887281132207661924639 48001330921698311492886959)
    ·
      refine ⟨72001996382547467239330439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48001330921698311492886959 72001996382547467239330439)
      ·
        refine ⟨108002994573821200858995659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72001996382547467239330439 108002994573821200858995659)
        ·
          refine ⟨162004491860731801288493489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108002994573821200858995659 162004491860731801288493489)
          ·
            refine ⟨121503368895548850966370117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162004491860731801288493489 121503368895548850966370117)
            ·
              refine ⟨22781881667915409556194397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121503368895548850966370117 22781881667915409556194397)
              ·
                refine ⟨8543205625468278583572899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22781881667915409556194397 8543205625468278583572899)
                ·
                  refine ⟨12814808438202417875359349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8543205625468278583572899 12814808438202417875359349)
                  ·
                    refine ⟨1201388291081476675814939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12814808438202417875359349 1201388291081476675814939)
                    ·
                      rfl

theorem cell23_7019086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_7019086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019086 prefixEnd_7019086 := by exact prefixLift 7019086
  have htrace : WordTrace (prefixWord ++ tailWord_7019086) baseStart_7019086 baseEnd_7019086 := by
    simpa [prefixWord, tailWord_7019086, baseEnd_7019086] using wordTrace_append hprefix tailTrace_7019086
  have hstable : (prefixWord ++ tailWord_7019086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019086).length < 2 ^ (prefixWord ++ tailWord_7019086).sum := by decide
  have hdescent : baseEnd_7019086 < baseStart_7019086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019119 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_7019119 : Nat := 118140960795 + 7019119 * 2 ^ 59
def prefixEnd_7019119 : Nat := 4983230072969 + 3 ^ 40 * 7019119 * 2
def baseEnd_7019119 : Nat := 3604181818106028398332165

theorem tailTrace_7019119 : CollatzResearch.WordTrace tailWord_7019119 prefixEnd_7019119 3604181818106028398332165 := by
  unfold tailWord_7019119
  simp only [CollatzResearch.WordTrace]
  refine ⟨256008301857938107931348411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170672201238625405287565607 256008301857938107931348411)
  ·
    refine ⟨384012452786907161897022617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256008301857938107931348411 384012452786907161897022617)
    ·
      refine ⟨288009339590180371422766963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384012452786907161897022617 288009339590180371422766963)
      ·
        refine ⟨432014009385270557134150445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288009339590180371422766963 432014009385270557134150445)
        ·
          refine ⟨162005253519476458925306417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432014009385270557134150445 162005253519476458925306417)
          ·
            refine ⟨121503940139607344193979813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162005253519476458925306417 121503940139607344193979813)
            ·
              refine ⟨22781988776176377036371215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121503940139607344193979813 22781988776176377036371215)
              ·
                refine ⟨34172983164264565554556823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22781988776176377036371215 34172983164264565554556823)
                ·
                  refine ⟨51259474746396848331835235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34172983164264565554556823 51259474746396848331835235)
                  ·
                    refine ⟨76889212119595272497752853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51259474746396848331835235 76889212119595272497752853)
                    ·
                      refine ⟨3604181818106028398332165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76889212119595272497752853 3604181818106028398332165)
                      ·
                        rfl

theorem cell23_7019119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_7019119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019119 prefixEnd_7019119 := by exact prefixLift 7019119
  have htrace : WordTrace (prefixWord ++ tailWord_7019119) baseStart_7019119 baseEnd_7019119 := by
    simpa [prefixWord, tailWord_7019119, baseEnd_7019119] using wordTrace_append hprefix tailTrace_7019119
  have hstable : (prefixWord ++ tailWord_7019119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019119).length < 2 ^ (prefixWord ++ tailWord_7019119).sum := by decide
  have hdescent : baseEnd_7019119 < baseStart_7019119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019120 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 1, 5]
def baseStart_7019120 : Nat := 118140960795 + 7019120 * 2 ^ 59
def prefixEnd_7019120 : Nat := 4983230072969 + 3 ^ 40 * 7019120 * 2
def baseEnd_7019120 : Nat := 1201394110528894298139887

theorem tailTrace_7019120 : CollatzResearch.WordTrace tailWord_7019120 prefixEnd_7019120 1201394110528894298139887 := by
  unfold tailWord_7019120
  simp only [CollatzResearch.WordTrace]
  refine ⟨128004169165467242551067407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170672225553956323401423209 128004169165467242551067407)
  ·
    refine ⟨192006253748200863826601111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128004169165467242551067407 192006253748200863826601111)
    ·
      refine ⟨288009380622301295739901667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192006253748200863826601111 288009380622301295739901667)
      ·
        refine ⟨432014070933451943609852501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288009380622301295739901667 432014070933451943609852501)
        ·
          refine ⟨5062664893751389964177959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 432014070933451943609852501 5062664893751389964177959)
          ·
            refine ⟨7593997340627084946266939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062664893751389964177959 7593997340627084946266939)
            ·
              refine ⟨11390996010940627419400409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593997340627084946266939 11390996010940627419400409)
              ·
                refine ⟨8543247008205470564550307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11390996010940627419400409 8543247008205470564550307)
                ·
                  refine ⟨12814870512308205846825461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8543247008205470564550307 12814870512308205846825461)
                  ·
                    refine ⟨1201394110528894298139887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12814870512308205846825461 1201394110528894298139887)
                    ·
                      rfl

theorem cell23_7019120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 5].length) (baseStart_7019120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019120 prefixEnd_7019120 := by exact prefixLift 7019120
  have htrace : WordTrace (prefixWord ++ tailWord_7019120) baseStart_7019120 baseEnd_7019120 := by
    simpa [prefixWord, tailWord_7019120, baseEnd_7019120] using wordTrace_append hprefix tailTrace_7019120
  have hstable : (prefixWord ++ tailWord_7019120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019120).length < 2 ^ (prefixWord ++ tailWord_7019120).sum := by decide
  have hdescent : baseEnd_7019120 < baseStart_7019120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019129 : List Nat := [1, 2, 1, 3, 3, 2, 2, 9]
def baseStart_7019129 : Nat := 118140960795 + 7019129 * 2 ^ 59
def prefixEnd_7019129 : Nat := 4983230072969 + 3 ^ 40 * 7019129 * 2
def baseEnd_7019129 : Nat := 133488405663428642933597

theorem tailTrace_7019129 : CollatzResearch.WordTrace tailWord_7019129 prefixEnd_7019129 133488405663428642933597 := by
  unfold tailWord_7019129
  simp only [CollatzResearch.WordTrace]
  refine ⟨256008666587901879639212441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170672444391934586426141627 256008666587901879639212441)
  ·
    refine ⟨192006499940926409729409331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256008666587901879639212441 192006499940926409729409331)
    ·
      refine ⟨288009749911389614594113997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192006499940926409729409331 288009749911389614594113997)
      ·
        refine ⟨108003656216771105472792749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288009749911389614594113997 108003656216771105472792749)
        ·
          refine ⟨40501371081289164552297281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108003656216771105472792749 40501371081289164552297281)
          ·
            refine ⟨30376028310966873414222961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40501371081289164552297281 30376028310966873414222961)
            ·
              refine ⟨22782021233225155060667221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30376028310966873414222961 22782021233225155060667221)
              ·
                refine ⟨133488405663428642933597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22782021233225155060667221 133488405663428642933597)
                ·
                  rfl

theorem cell23_7019129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 9].length) (baseStart_7019129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019129 prefixEnd_7019129 := by exact prefixLift 7019129
  have htrace : WordTrace (prefixWord ++ tailWord_7019129) baseStart_7019129 baseEnd_7019129 := by
    simpa [prefixWord, tailWord_7019129, baseEnd_7019129] using wordTrace_append hprefix tailTrace_7019129
  have hstable : (prefixWord ++ tailWord_7019129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019129).length < 2 ^ (prefixWord ++ tailWord_7019129).sum := by decide
  have hdescent : baseEnd_7019129 < baseStart_7019129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019136 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 4]
def baseStart_7019136 : Nat := 118140960795 + 7019136 * 2 ^ 59
def prefixEnd_7019136 : Nat := 4983230072969 + 3 ^ 40 * 7019136 * 2
def baseEnd_7019136 : Nat := 3604190547277154831819587

theorem tailTrace_7019136 : CollatzResearch.WordTrace tailWord_7019136 prefixEnd_7019136 3604190547277154831819587 := by
  unfold tailWord_7019136
  simp only [CollatzResearch.WordTrace]
  refine ⟨128004460949438259917358631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170672614599251013223144841 128004460949438259917358631)
  ·
    refine ⟨192006691424157389876037947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128004460949438259917358631 192006691424157389876037947)
    ·
      refine ⟨288010037136236084814056921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192006691424157389876037947 288010037136236084814056921)
      ·
        refine ⟨216007527852177063610542691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288010037136236084814056921 216007527852177063610542691)
        ·
          refine ⟨324011291778265595415814037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216007527852177063610542691 324011291778265595415814037)
          ·
            refine ⟨15188029302106199785116283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 324011291778265595415814037 15188029302106199785116283)
            ·
              refine ⟨22782043953159299677674425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15188029302106199785116283 22782043953159299677674425)
              ·
                refine ⟨17086532964869474758255819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22782043953159299677674425 17086532964869474758255819)
                ·
                  refine ⟨25629799447304212137383729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17086532964869474758255819 25629799447304212137383729)
                  ·
                    refine ⟨19222349585478159103037797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25629799447304212137383729 19222349585478159103037797)
                    ·
                      refine ⟨3604190547277154831819587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19222349585478159103037797 3604190547277154831819587)
                      ·
                        rfl

theorem cell23_7019136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_7019136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019136 prefixEnd_7019136 := by exact prefixLift 7019136
  have htrace : WordTrace (prefixWord ++ tailWord_7019136) baseStart_7019136 baseEnd_7019136 := by
    simpa [prefixWord, tailWord_7019136, baseEnd_7019136] using wordTrace_append hprefix tailTrace_7019136
  have hstable : (prefixWord ++ tailWord_7019136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019136).length < 2 ^ (prefixWord ++ tailWord_7019136).sum := by decide
  have hdescent : baseEnd_7019136 < baseStart_7019136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019140 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_7019140 : Nat := 118140960795 + 7019140 * 2 ^ 59
def prefixEnd_7019140 : Nat := 4983230072969 + 3 ^ 40 * 7019140 * 2
def baseEnd_7019140 : Nat := 3604192601199772816169569

theorem tailTrace_7019140 : CollatzResearch.WordTrace tailWord_7019140 prefixEnd_7019140 3604192601199772816169569 := by
  unfold tailWord_7019140
  simp only [CollatzResearch.WordTrace]
  refine ⟨128004533895431014258931437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170672711860574685678575249 128004533895431014258931437)
  ·
    refine ⟨48001700210786630347099289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128004533895431014258931437 48001700210786630347099289)
    ·
      refine ⟨36001275158089972760324467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48001700210786630347099289 36001275158089972760324467)
      ·
        refine ⟨54001912737134959140486701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36001275158089972760324467 54001912737134959140486701)
        ·
          refine ⟨20250717276425609677682513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54001912737134959140486701 20250717276425609677682513)
          ·
            refine ⟨15188037957319207258261885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20250717276425609677682513 15188037957319207258261885)
            ·
              refine ⟨5695514233994702721848207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15188037957319207258261885 5695514233994702721848207)
              ·
                refine ⟨8543271350992054082772311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5695514233994702721848207 8543271350992054082772311)
                ·
                  refine ⟨12814907026488081124158467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8543271350992054082772311 12814907026488081124158467)
                  ·
                    refine ⟨19222360539732121686237701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12814907026488081124158467 19222360539732121686237701)
                    ·
                      refine ⟨3604192601199772816169569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19222360539732121686237701 3604192601199772816169569)
                      ·
                        rfl

theorem cell23_7019140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_7019140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019140 prefixEnd_7019140 := by exact prefixLift 7019140
  have htrace : WordTrace (prefixWord ++ tailWord_7019140) baseStart_7019140 baseEnd_7019140 := by
    simpa [prefixWord, tailWord_7019140, baseEnd_7019140] using wordTrace_append hprefix tailTrace_7019140
  have hstable : (prefixWord ++ tailWord_7019140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019140).length < 2 ^ (prefixWord ++ tailWord_7019140).sum := by decide
  have hdescent : baseEnd_7019140 < baseStart_7019140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019146 : List Nat := [3, 1, 2, 3, 4, 10]
def baseStart_7019146 : Nat := 118140960795 + 7019146 * 2 ^ 59
def prefixEnd_7019146 : Nat := 4983230072969 + 3 ^ 40 * 7019146 * 2
def baseEnd_7019146 : Nat := 14832080996229217253887

theorem tailTrace_7019146 : CollatzResearch.WordTrace tailWord_7019146 prefixEnd_7019146 14832080996229217253887 := by
  unfold tailWord_7019146
  simp only [CollatzResearch.WordTrace]
  refine ⟨64002321657210072885645323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170672857752560194361720861 64002321657210072885645323)
  ·
    refine ⟨96003482485815109328467985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64002321657210072885645323 96003482485815109328467985)
    ·
      refine ⟨72002611864361331996350989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96003482485815109328467985 72002611864361331996350989)
      ·
        refine ⟨27000979449135499498631621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72002611864361331996350989 27000979449135499498631621)
        ·
          refine ⟨5062683646712906155993429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27000979449135499498631621 5062683646712906155993429)
          ·
            refine ⟨14832080996229217253887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5062683646712906155993429 14832080996229217253887)
            ·
              rfl

theorem cell23_7019146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 10].length) (baseStart_7019146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019146 prefixEnd_7019146 := by exact prefixLift 7019146
  have htrace : WordTrace (prefixWord ++ tailWord_7019146) baseStart_7019146 baseEnd_7019146 := by
    simpa [prefixWord, tailWord_7019146, baseEnd_7019146] using wordTrace_append hprefix tailTrace_7019146
  have hstable : (prefixWord ++ tailWord_7019146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019146).length < 2 ^ (prefixWord ++ tailWord_7019146).sum := by decide
  have hdescent : baseEnd_7019146 < baseStart_7019146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019159 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 1, 9]
def baseStart_7019159 : Nat := 118140960795 + 7019159 * 2 ^ 59
def prefixEnd_7019159 : Nat := 4983230072969 + 3 ^ 40 * 7019159 * 2
def baseEnd_7019159 : Nat := 1201400785777402747277327

theorem tailTrace_7019159 : CollatzResearch.WordTrace tailWord_7019159 prefixEnd_7019159 1201400785777402747277327 := by
  unfold tailWord_7019159
  simp only [CollatzResearch.WordTrace]
  refine ⟨256009760777793194762804531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170673173851862129841869687 256009760777793194762804531)
  ·
    refine ⟨384014641166689792144206797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256009760777793194762804531 384014641166689792144206797)
    ·
      refine ⟨144005490437508672054077549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384014641166689792144206797 144005490437508672054077549)
      ·
        refine ⟨54002058914065752020279081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144005490437508672054077549 54002058914065752020279081)
        ·
          refine ⟨40501544185549314015209311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54002058914065752020279081 40501544185549314015209311)
          ·
            refine ⟨60752316278323971022813967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40501544185549314015209311 60752316278323971022813967)
            ·
              refine ⟨91128474417485956534220951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60752316278323971022813967 91128474417485956534220951)
              ·
                refine ⟨136692711626228934801331427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91128474417485956534220951 136692711626228934801331427)
                ·
                  refine ⟨205039067439343402201997141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136692711626228934801331427 205039067439343402201997141)
                  ·
                    refine ⟨1201400785777402747277327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 205039067439343402201997141 1201400785777402747277327)
                    ·
                      rfl

theorem cell23_7019159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_7019159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019159 prefixEnd_7019159 := by exact prefixLift 7019159
  have htrace : WordTrace (prefixWord ++ tailWord_7019159) baseStart_7019159 baseEnd_7019159 := by
    simpa [prefixWord, tailWord_7019159, baseEnd_7019159] using wordTrace_append hprefix tailTrace_7019159
  have hstable : (prefixWord ++ tailWord_7019159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019159).length < 2 ^ (prefixWord ++ tailWord_7019159).sum := by decide
  have hdescent : baseEnd_7019159 < baseStart_7019159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019183 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 3, 3, 2]
def baseStart_7019183 : Nat := 118140960795 + 7019183 * 2 ^ 59
def prefixEnd_7019183 : Nat := 4983230072969 + 3 ^ 40 * 7019183 * 2
def baseEnd_7019183 : Nat := 3604214680867916147931871

theorem tailTrace_7019183 : CollatzResearch.WordTrace tailWord_7019183 prefixEnd_7019183 3604214680867916147931871 := by
  unfold tailWord_7019183
  simp only [CollatzResearch.WordTrace]
  refine ⟨256010636129706246861678203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170673757419804164574452135 256010636129706246861678203)
  ·
    refine ⟨384015954194559370292517305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256010636129706246861678203 384015954194559370292517305)
    ·
      refine ⟨288011965645919527719387979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384015954194559370292517305 288011965645919527719387979)
      ·
        refine ⟨432017948468879291579081969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288011965645919527719387979 432017948468879291579081969)
        ·
          refine ⟨324013461351659468684311477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432017948468879291579081969 324013461351659468684311477)
          ·
            refine ⟨30376262001718075189154201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 324013461351659468684311477 30376262001718075189154201)
            ·
              refine ⟨22782196501288556391865651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30376262001718075189154201 22782196501288556391865651)
              ·
                refine ⟨34173294751932834587798477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22782196501288556391865651 34173294751932834587798477)
                ·
                  refine ⟨12814985531974812970424429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34173294751932834587798477 12814985531974812970424429)
                  ·
                    refine ⟨4805619574490554863909161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12814985531974812970424429 4805619574490554863909161)
                    ·
                      refine ⟨3604214680867916147931871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4805619574490554863909161 3604214680867916147931871)
                      ·
                        rfl

theorem cell23_7019183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 3, 2].length) (baseStart_7019183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019183 prefixEnd_7019183 := by exact prefixLift 7019183
  have htrace : WordTrace (prefixWord ++ tailWord_7019183) baseStart_7019183 baseEnd_7019183 := by
    simpa [prefixWord, tailWord_7019183, baseEnd_7019183] using wordTrace_append hprefix tailTrace_7019183
  have hstable : (prefixWord ++ tailWord_7019183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019183).length < 2 ^ (prefixWord ++ tailWord_7019183).sum := by decide
  have hdescent : baseEnd_7019183 < baseStart_7019183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019200 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 1, 3, 2]
def baseStart_7019200 : Nat := 118140960795 + 7019200 * 2 ^ 59
def prefixEnd_7019200 : Nat := 4983230072969 + 3 ^ 40 * 7019200 * 2
def baseEnd_7019200 : Nat := 3604223410039042581419293

theorem tailTrace_7019200 : CollatzResearch.WordTrace tailWord_7019200 prefixEnd_7019200 3604223410039042581419293 := by
  unfold tailWord_7019200
  simp only [CollatzResearch.WordTrace]
  refine ⟨128005628085322329382523527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170674170780429772510031369 128005628085322329382523527)
  ·
    refine ⟨192008442127983494073785291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128005628085322329382523527 192008442127983494073785291)
    ·
      refine ⟨288012663191975241110677937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192008442127983494073785291 288012663191975241110677937)
      ·
        refine ⟨216009497393981430833008453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288012663191975241110677937 216009497393981430833008453)
        ·
          refine ⟨40501780761371518281189085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216009497393981430833008453 40501780761371518281189085)
          ·
            refine ⟨15188167785514319355445907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40501780761371518281189085 15188167785514319355445907)
            ·
              refine ⟨22782251678271479033168861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15188167785514319355445907 22782251678271479033168861)
              ·
                refine ⟨8543344379351804637438323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22782251678271479033168861 8543344379351804637438323)
                ·
                  refine ⟨12815016569027706956157485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8543344379351804637438323 12815016569027706956157485)
                  ·
                    refine ⟨4805631213385390108559057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12815016569027706956157485 4805631213385390108559057)
                    ·
                      refine ⟨3604223410039042581419293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4805631213385390108559057 3604223410039042581419293)
                      ·
                        rfl

theorem cell23_7019200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_7019200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019200 prefixEnd_7019200 := by exact prefixLift 7019200
  have htrace : WordTrace (prefixWord ++ tailWord_7019200) baseStart_7019200 baseEnd_7019200 := by
    simpa [prefixWord, tailWord_7019200, baseEnd_7019200] using wordTrace_append hprefix tailTrace_7019200
  have hstable : (prefixWord ++ tailWord_7019200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019200).length < 2 ^ (prefixWord ++ tailWord_7019200).sum := by decide
  have hdescent : baseEnd_7019200 < baseStart_7019200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019226 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_7019226 : Nat := 118140960795 + 7019226 * 2 ^ 59
def prefixEnd_7019226 : Nat := 4983230072969 + 3 ^ 40 * 7019226 * 2
def baseEnd_7019226 : Nat := 3604236760536059479694173

theorem tailTrace_7019226 : CollatzResearch.WordTrace tailWord_7019226 prefixEnd_7019226 3604236760536059479694173 := by
  unfold tailWord_7019226
  simp only [CollatzResearch.WordTrace]
  refine ⟨64003051117137616301373383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170674802979033643470329021 64003051117137616301373383)
  ·
    refine ⟨96004576675706424452060075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64003051117137616301373383 96004576675706424452060075)
    ·
      refine ⟨144006865013559636678090113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96004576675706424452060075 144006865013559636678090113)
      ·
        refine ⟨108005148760169727508567585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144006865013559636678090113 108005148760169727508567585)
        ·
          refine ⟨81003861570127295631425689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108005148760169727508567585 81003861570127295631425689)
          ·
            refine ⟨60752896177595471723569267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81003861570127295631425689 60752896177595471723569267)
            ·
              refine ⟨91129344266393207585353901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60752896177595471723569267 91129344266393207585353901)
              ·
                refine ⟨34173504099897452844507713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91129344266393207585353901 34173504099897452844507713)
                ·
                  refine ⟨25630128074923089633380785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34173504099897452844507713 25630128074923089633380785)
                  ·
                    refine ⟨19222596056192317225035589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25630128074923089633380785 19222596056192317225035589)
                    ·
                      refine ⟨3604236760536059479694173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19222596056192317225035589 3604236760536059479694173)
                      ·
                        rfl

theorem cell23_7019226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_7019226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019226 prefixEnd_7019226 := by exact prefixLift 7019226
  have htrace : WordTrace (prefixWord ++ tailWord_7019226) baseStart_7019226 baseEnd_7019226 := by
    simpa [prefixWord, tailWord_7019226, baseEnd_7019226] using wordTrace_append hprefix tailTrace_7019226
  have hstable : (prefixWord ++ tailWord_7019226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019226).length < 2 ^ (prefixWord ++ tailWord_7019226).sum := by decide
  have hdescent : baseEnd_7019226 < baseStart_7019226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019236 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 7]
def baseStart_7019236 : Nat := 118140960795 + 7019236 * 2 ^ 59
def prefixEnd_7019236 : Nat := 4983230072969 + 3 ^ 40 * 7019236 * 2
def baseEnd_7019236 : Nat := 400471321704733826729903

theorem tailTrace_7019236 : CollatzResearch.WordTrace tailWord_7019236 prefixEnd_7019236 400471321704733826729903 := by
  unfold tailWord_7019236
  simp only [CollatzResearch.WordTrace]
  refine ⟨128006284599257118456678781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170675046132342824608905041 128006284599257118456678781)
  ·
    refine ⟨48002356724721419421254543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128006284599257118456678781 48002356724721419421254543)
    ·
      refine ⟨72003535087082129131881815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48002356724721419421254543 72003535087082129131881815)
      ·
        refine ⟨108005302630623193697822723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72003535087082129131881815 108005302630623193697822723)
        ·
          refine ⟨162007953945934790546734085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108005302630623193697822723 162007953945934790546734085)
          ·
            refine ⟨30376491364862773227512641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162007953945934790546734085 30376491364862773227512641)
            ·
              refine ⟨22782368523647079920634481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30376491364862773227512641 22782368523647079920634481)
              ·
                refine ⟨17086776392735309940475861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22782368523647079920634481 17086776392735309940475861)
                ·
                  refine ⟨400471321704733826729903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17086776392735309940475861 400471321704733826729903)
                  ·
                    rfl

theorem cell23_7019236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_7019236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019236 prefixEnd_7019236 := by exact prefixLift 7019236
  have htrace : WordTrace (prefixWord ++ tailWord_7019236) baseStart_7019236 baseEnd_7019236 := by
    simpa [prefixWord, tailWord_7019236, baseEnd_7019236] using wordTrace_append hprefix tailTrace_7019236
  have hstable : (prefixWord ++ tailWord_7019236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019236).length < 2 ^ (prefixWord ++ tailWord_7019236).sum := by decide
  have hdescent : baseEnd_7019236 < baseStart_7019236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019300 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_7019300 : Nat := 118140960795 + 7019300 * 2 ^ 59
def prefixEnd_7019300 : Nat := 4983230072969 + 3 ^ 40 * 7019300 * 2
def baseEnd_7019300 : Nat := 1201424919368164063389611

theorem tailTrace_7019300 : CollatzResearch.WordTrace tailWord_7019300 prefixEnd_7019300 1201424919368164063389611 := by
  unfold tailWord_7019300
  simp only [CollatzResearch.WordTrace]
  refine ⟨128007451735141187921843677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170676602313521583895791569 128007451735141187921843677)
  ·
    refine ⟨48002794400677945470691379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128007451735141187921843677 48002794400677945470691379)
    ·
      refine ⟨72004191601016918206037069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48002794400677945470691379 72004191601016918206037069)
      ·
        refine ⟨27001571850381344327263901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72004191601016918206037069 27001571850381344327263901)
        ·
          refine ⟨10125589443893004122723963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27001571850381344327263901 10125589443893004122723963)
          ·
            refine ⟨15188384165839506184085945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10125589443893004122723963 15188384165839506184085945)
            ·
              refine ⟨11391288124379629638064459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15188384165839506184085945 11391288124379629638064459)
              ·
                refine ⟨17086932186569444457096689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11391288124379629638064459 17086932186569444457096689)
                ·
                  refine ⟨12815199139927083342822517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17086932186569444457096689 12815199139927083342822517)
                  ·
                    refine ⟨1201424919368164063389611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12815199139927083342822517 1201424919368164063389611)
                    ·
                      rfl

theorem cell23_7019300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_7019300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019300 prefixEnd_7019300 := by exact prefixLift 7019300
  have htrace : WordTrace (prefixWord ++ tailWord_7019300) baseStart_7019300 baseEnd_7019300 := by
    simpa [prefixWord, tailWord_7019300, baseEnd_7019300] using wordTrace_append hprefix tailTrace_7019300
  have hstable : (prefixWord ++ tailWord_7019300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019300).length < 2 ^ (prefixWord ++ tailWord_7019300).sum := by decide
  have hdescent : baseEnd_7019300 < baseStart_7019300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019387 : List Nat := [1, 1, 1, 1, 1, 5, 4, 4, 1, 1, 3]
def baseStart_7019387 : Nat := 118140960795 + 7019387 * 2 ^ 59
def prefixEnd_7019387 : Nat := 4983230072969 + 3 ^ 40 * 7019387 * 2
def baseEnd_7019387 : Nat := 3604319430921433349780933

theorem tailTrace_7019387 : CollatzResearch.WordTrace tailWord_7019387 prefixEnd_7019387 3604319430921433349780933 := by
  unfold tailWord_7019387
  simp only [CollatzResearch.WordTrace]
  refine ⟨256018076620967189702104415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170678717747311459801402943 256018076620967189702104415)
  ·
    refine ⟨384027114931450784553156623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256018076620967189702104415 384027114931450784553156623)
    ·
      refine ⟨576040672397176176829734935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384027114931450784553156623 576040672397176176829734935)
      ·
        refine ⟨864061008595764265244602403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576040672397176176829734935 864061008595764265244602403)
        ·
          refine ⟨1296091512893646397866903605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864061008595764265244602403 1296091512893646397866903605)
          ·
            refine ⟨121508579333779349800022213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1296091512893646397866903605 121508579333779349800022213)
            ·
              refine ⟨22782858625083628087504165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121508579333779349800022213 22782858625083628087504165)
              ·
                refine ⟨4271785992203180266407031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22782858625083628087504165 4271785992203180266407031)
                ·
                  refine ⟨6407678988304770399610547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271785992203180266407031 6407678988304770399610547)
                  ·
                    refine ⟨9611518482457155599415821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6407678988304770399610547 9611518482457155599415821)
                    ·
                      refine ⟨3604319430921433349780933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9611518482457155599415821 3604319430921433349780933)
                      ·
                        rfl

theorem cell23_7019387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 1, 1, 3].length) (baseStart_7019387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019387 prefixEnd_7019387 := by exact prefixLift 7019387
  have htrace : WordTrace (prefixWord ++ tailWord_7019387) baseStart_7019387 baseEnd_7019387 := by
    simpa [prefixWord, tailWord_7019387, baseEnd_7019387] using wordTrace_append hprefix tailTrace_7019387
  have hstable : (prefixWord ++ tailWord_7019387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019387).length < 2 ^ (prefixWord ++ tailWord_7019387).sum := by decide
  have hdescent : baseEnd_7019387 < baseStart_7019387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019403 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 1, 6]
def baseStart_7019403 : Nat := 118140960795 + 7019403 * 2 ^ 59
def prefixEnd_7019403 : Nat := 4983230072969 + 3 ^ 40 * 7019403 * 2
def baseEnd_7019403 : Nat := 1201442548870635095726953

theorem tailTrace_7019403 : CollatzResearch.WordTrace tailWord_7019403 prefixEnd_7019403 1201442548870635095726953 := by
  unfold tailWord_7019403
  simp only [CollatzResearch.WordTrace]
  refine ⟨256018660188909224434686863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170679106792606149623124575 256018660188909224434686863)
  ·
    refine ⟨384027990283363836652030295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256018660188909224434686863 384027990283363836652030295)
    ·
      refine ⟨576041985425045754978045443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384027990283363836652030295 576041985425045754978045443)
      ·
        refine ⟨864062978137568632467068165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576041985425045754978045443 864062978137568632467068165)
        ·
          refine ⟨162011808400794118587575281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 864062978137568632467068165 162011808400794118587575281)
          ·
            refine ⟨121508856300595588940681461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162011808400794118587575281 121508856300595588940681461)
            ·
              refine ⟨11391455278180836463188887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121508856300595588940681461 11391455278180836463188887)
              ·
                refine ⟨17087182917271254694783331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11391455278180836463188887 17087182917271254694783331)
                ·
                  refine ⟨25630774375906882042174997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17087182917271254694783331 25630774375906882042174997)
                  ·
                    refine ⟨1201442548870635095726953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25630774375906882042174997 1201442548870635095726953)
                    ·
                      rfl

theorem cell23_7019403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 6].length) (baseStart_7019403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019403 prefixEnd_7019403 := by exact prefixLift 7019403
  have htrace : WordTrace (prefixWord ++ tailWord_7019403) baseStart_7019403 baseEnd_7019403 := by
    simpa [prefixWord, tailWord_7019403, baseEnd_7019403] using wordTrace_append hprefix tailTrace_7019403
  have hstable : (prefixWord ++ tailWord_7019403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019403).length < 2 ^ (prefixWord ++ tailWord_7019403).sum := by decide
  have hdescent : baseEnd_7019403 < baseStart_7019403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019443 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 3]
def baseStart_7019443 : Nat := 118140960795 + 7019443 * 2 ^ 59
def prefixEnd_7019443 : Nat := 4983230072969 + 3 ^ 40 * 7019443 * 2
def baseEnd_7019443 : Nat := 3604348185838085130680675

theorem tailTrace_7019443 : CollatzResearch.WordTrace tailWord_7019443 prefixEnd_7019443 3604348185838085130680675 := by
  unfold tailWord_7019443
  simp only [CollatzResearch.WordTrace]
  refine ⟨256020119108764311266142983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170680079405842874177428655 256020119108764311266142983)
  ·
    refine ⟨384030178663146466899214475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256020119108764311266142983 384030178663146466899214475)
    ·
      refine ⟨576045267994719700348821713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384030178663146466899214475 576045267994719700348821713)
      ·
        refine ⟨432033950996039775261616285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576045267994719700348821713 432033950996039775261616285)
        ·
          refine ⟨162012731623514915723106107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432033950996039775261616285 162012731623514915723106107)
          ·
            refine ⟨243019097435272373584659161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162012731623514915723106107 243019097435272373584659161)
            ·
              refine ⟨182264323076454280188494371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243019097435272373584659161 182264323076454280188494371)
              ·
                refine ⟨273396484614681420282741557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182264323076454280188494371 273396484614681420282741557)
                ·
                  refine ⟨25630920432626383151507021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273396484614681420282741557 25630920432626383151507021)
                  ·
                    refine ⟨9611595162234893681815133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25630920432626383151507021 9611595162234893681815133)
                    ·
                      refine ⟨3604348185838085130680675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9611595162234893681815133 3604348185838085130680675)
                      ·
                        rfl

theorem cell23_7019443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 3].length) (baseStart_7019443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019443 prefixEnd_7019443 := by exact prefixLift 7019443
  have htrace : WordTrace (prefixWord ++ tailWord_7019443) baseStart_7019443 baseEnd_7019443 := by
    simpa [prefixWord, tailWord_7019443, baseEnd_7019443] using wordTrace_append hprefix tailTrace_7019443
  have hstable : (prefixWord ++ tailWord_7019443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019443).length < 2 ^ (prefixWord ++ tailWord_7019443).sum := by decide
  have hdescent : baseEnd_7019443 < baseStart_7019443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019464 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_7019464 : Nat := 118140960795 + 7019464 * 2 ^ 59
def prefixEnd_7019464 : Nat := 4983230072969 + 3 ^ 40 * 7019464 * 2
def baseEnd_7019464 : Nat := 3604358968931829548518079

theorem tailTrace_7019464 : CollatzResearch.WordTrace tailWord_7019464 prefixEnd_7019464 3604358968931829548518079 := by
  unfold tailWord_7019464
  simp only [CollatzResearch.WordTrace]
  refine ⟨128010442520844115926328723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170680590027792154568438297 128010442520844115926328723)
  ·
    refine ⟨192015663781266173889493085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128010442520844115926328723 192015663781266173889493085)
    ·
      refine ⟨72005873917974815208559907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192015663781266173889493085 72005873917974815208559907)
      ·
        refine ⟨108008810876962222812839861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72005873917974815208559907 108008810876962222812839861)
        ·
          refine ⟨10125826019715208388703737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108008810876962222812839861 10125826019715208388703737)
          ·
            refine ⟨7594369514786406291527803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10125826019715208388703737 7594369514786406291527803)
            ·
              refine ⟨11391554272179609437291705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7594369514786406291527803 11391554272179609437291705)
              ·
                refine ⟨8543665704134707077968779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11391554272179609437291705 8543665704134707077968779)
                ·
                  refine ⟨12815498556202060616953169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8543665704134707077968779 12815498556202060616953169)
                  ·
                    refine ⟨9611623917151545462714877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12815498556202060616953169 9611623917151545462714877)
                    ·
                      refine ⟨3604358968931829548518079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9611623917151545462714877 3604358968931829548518079)
                      ·
                        rfl

theorem cell23_7019464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_7019464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019464 prefixEnd_7019464 := by exact prefixLift 7019464
  have htrace : WordTrace (prefixWord ++ tailWord_7019464) baseStart_7019464 baseEnd_7019464 := by
    simpa [prefixWord, tailWord_7019464, baseEnd_7019464] using wordTrace_append hprefix tailTrace_7019464
  have hstable : (prefixWord ++ tailWord_7019464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019464).length < 2 ^ (prefixWord ++ tailWord_7019464).sum := by decide
  have hdescent : baseEnd_7019464 < baseStart_7019464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019477 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_7019477 : Nat := 118140960795 + 7019477 * 2 ^ 59
def prefixEnd_7019477 : Nat := 4983230072969 + 3 ^ 40 * 7019477 * 2
def baseEnd_7019477 : Nat := 3604365644180337997655519

theorem tailTrace_7019477 : CollatzResearch.WordTrace tailWord_7019477 prefixEnd_7019477 3604365644180337997655519 := by
  unfold tailWord_7019477
  simp only [CollatzResearch.WordTrace]
  refine ⟨256021359190641135072880685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170680906127094090048587123 256021359190641135072880685)
  ·
    refine ⟨96008009696490425652330257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256021359190641135072880685 96008009696490425652330257)
    ·
      refine ⟨72006007272367819239247693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96008009696490425652330257 72006007272367819239247693)
      ·
        refine ⟨27002252727137932214717885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72006007272367819239247693 27002252727137932214717885)
        ·
          refine ⟨10125844772676724580519207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27002252727137932214717885 10125844772676724580519207)
          ·
            refine ⟨15188767159015086870778811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10125844772676724580519207 15188767159015086870778811)
            ·
              refine ⟨22783150738522630306168217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15188767159015086870778811 22783150738522630306168217)
              ·
                refine ⟨17087363053891972729626163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22783150738522630306168217 17087363053891972729626163)
                ·
                  refine ⟨25631044580837959094439245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17087363053891972729626163 25631044580837959094439245)
                  ·
                    refine ⟨9611641717814234660414717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25631044580837959094439245 9611641717814234660414717)
                    ·
                      refine ⟨3604365644180337997655519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9611641717814234660414717 3604365644180337997655519)
                      ·
                        rfl

theorem cell23_7019477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_7019477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019477 prefixEnd_7019477 := by exact prefixLift 7019477
  have htrace : WordTrace (prefixWord ++ tailWord_7019477) baseStart_7019477 baseEnd_7019477 := by
    simpa [prefixWord, tailWord_7019477, baseEnd_7019477] using wordTrace_append hprefix tailTrace_7019477
  have hstable : (prefixWord ++ tailWord_7019477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019477).length < 2 ^ (prefixWord ++ tailWord_7019477).sum := by decide
  have hdescent : baseEnd_7019477 < baseStart_7019477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019508 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7019508 : Nat := 118140960795 + 7019508 * 2 ^ 59
def prefixEnd_7019508 : Nat := 4983230072969 + 3 ^ 40 * 7019508 * 2
def baseEnd_7019508 : Nat := 3604381562080627376367877

theorem tailTrace_7019508 : CollatzResearch.WordTrace tailWord_7019508 prefixEnd_7019508 3604381562080627376367877 := by
  unfold tailWord_7019508
  simp only [CollatzResearch.WordTrace]
  refine ⟨128011244926764413683629589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170681659902352551578172785 128011244926764413683629589)
  ·
    refine ⟨6000527105942081891420137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128011244926764413683629589 6000527105942081891420137)
    ·
      refine ⟨4500395329456561418565103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6000527105942081891420137 4500395329456561418565103)
      ·
        refine ⟨6750592994184842127847655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4500395329456561418565103 6750592994184842127847655)
        ·
          refine ⟨10125889491277263191771483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6750592994184842127847655 10125889491277263191771483)
          ·
            refine ⟨15188834236915894787657225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10125889491277263191771483 15188834236915894787657225)
            ·
              refine ⟨11391625677686921090742919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15188834236915894787657225 11391625677686921090742919)
              ·
                refine ⟨17087438516530381636114379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11391625677686921090742919 17087438516530381636114379)
                ·
                  refine ⟨25631157774795572454171569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17087438516530381636114379 25631157774795572454171569)
                  ·
                    refine ⟨19223368331096679340628677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25631157774795572454171569 19223368331096679340628677)
                    ·
                      refine ⟨3604381562080627376367877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19223368331096679340628677 3604381562080627376367877)
                      ·
                        rfl

theorem cell23_7019508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7019508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019508 prefixEnd_7019508 := by exact prefixLift 7019508
  have htrace : WordTrace (prefixWord ++ tailWord_7019508) baseStart_7019508 baseEnd_7019508 := by
    simpa [prefixWord, tailWord_7019508, baseEnd_7019508] using wordTrace_append hprefix tailTrace_7019508
  have hstable : (prefixWord ++ tailWord_7019508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019508).length < 2 ^ (prefixWord ++ tailWord_7019508).sum := by decide
  have hdescent : baseEnd_7019508 < baseStart_7019508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019510 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_7019510 : Nat := 118140960795 + 7019510 * 2 ^ 59
def prefixEnd_7019510 : Nat := 4983230072969 + 3 ^ 40 * 7019510 * 2
def baseEnd_7019510 : Nat := 1201460863013978789514289

theorem tailTrace_7019510 : CollatzResearch.WordTrace tailWord_7019510 prefixEnd_7019510 1201460863013978789514289 := by
  unfold tailWord_7019510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16001410174970098856801999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170681708533014387805887989 16001410174970098856801999)
  ·
    refine ⟨24002115262455148285202999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16001410174970098856801999 24002115262455148285202999)
    ·
      refine ⟨36003172893682722427804499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24002115262455148285202999 36003172893682722427804499)
      ·
        refine ⟨54004759340524083641706749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36003172893682722427804499 54004759340524083641706749)
        ·
          refine ⟨20251784752696531365640031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54004759340524083641706749 20251784752696531365640031)
          ·
            refine ⟨30377677129044797048460047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20251784752696531365640031 30377677129044797048460047)
            ·
              refine ⟨45566515693567195572690071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30377677129044797048460047 45566515693567195572690071)
              ·
                refine ⟨68349773540350793359035107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45566515693567195572690071 68349773540350793359035107)
                ·
                  refine ⟨102524660310526190038552661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68349773540350793359035107 102524660310526190038552661)
                  ·
                    refine ⟨1201460863013978789514289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102524660310526190038552661 1201460863013978789514289)
                    ·
                      rfl

theorem cell23_7019510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_7019510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019510 prefixEnd_7019510 := by exact prefixLift 7019510
  have htrace : WordTrace (prefixWord ++ tailWord_7019510) baseStart_7019510 baseEnd_7019510 := by
    simpa [prefixWord, tailWord_7019510, baseEnd_7019510] using wordTrace_append hprefix tailTrace_7019510
  have hstable : (prefixWord ++ tailWord_7019510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019510).length < 2 ^ (prefixWord ++ tailWord_7019510).sum := by decide
  have hdescent : baseEnd_7019510 < baseStart_7019510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019517 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 6, 2, 2]
def baseStart_7019517 : Nat := 118140960795 + 7019517 * 2 ^ 59
def prefixEnd_7019517 : Nat := 4983230072969 + 3 ^ 40 * 7019517 * 2
def baseEnd_7019517 : Nat := 3604386183406517841155335

theorem tailTrace_7019517 : CollatzResearch.WordTrace tailWord_7019517 prefixEnd_7019517 3604386183406517841155335 := by
  unfold tailWord_7019517
  simp only [CollatzResearch.WordTrace]
  refine ⟨256022818110496221904336805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170681878740330814602891203 256022818110496221904336805)
  ·
    refine ⟨48004278395718041607063151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256022818110496221904336805 48004278395718041607063151)
    ·
      refine ⟨72006417593577062410594727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48004278395718041607063151 72006417593577062410594727)
      ·
        refine ⟨108009626390365593615892091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72006417593577062410594727 108009626390365593615892091)
        ·
          refine ⟨162014439585548390423838137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108009626390365593615892091 162014439585548390423838137)
          ·
            refine ⟨121510829689161292817878603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162014439585548390423838137 121510829689161292817878603)
            ·
              refine ⟨182266244533741939226817905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121510829689161292817878603 182266244533741939226817905)
              ·
                refine ⟨136699683400306454420113429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182266244533741939226817905 136699683400306454420113429)
                ·
                  refine ⟨6407797659389365050942817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136699683400306454420113429 6407797659389365050942817)
                  ·
                    refine ⟨4805848244542023788207113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6407797659389365050942817 4805848244542023788207113)
                    ·
                      refine ⟨3604386183406517841155335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4805848244542023788207113 3604386183406517841155335)
                      ·
                        rfl

theorem cell23_7019517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_7019517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019517 prefixEnd_7019517 := by exact prefixLift 7019517
  have htrace : WordTrace (prefixWord ++ tailWord_7019517) baseStart_7019517 baseEnd_7019517 := by
    simpa [prefixWord, tailWord_7019517, baseEnd_7019517] using wordTrace_append hprefix tailTrace_7019517
  have hstable : (prefixWord ++ tailWord_7019517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019517).length < 2 ^ (prefixWord ++ tailWord_7019517).sum := by decide
  have hdescent : baseEnd_7019517 < baseStart_7019517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019551 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 2, 2, 2]
def baseStart_7019551 : Nat := 118140960795 + 7019551 * 2 ^ 59
def prefixEnd_7019551 : Nat := 4983230072969 + 3 ^ 40 * 7019551 * 2
def baseEnd_7019551 : Nat := 3604403641748770708130179

theorem tailTrace_7019551 : CollatzResearch.WordTrace tailWord_7019551 prefixEnd_7019551 3604403641748770708130179 := by
  unfold tailWord_7019551
  simp only [CollatzResearch.WordTrace]
  refine ⟨256024058192373045711074507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170682705461582030474049671 256024058192373045711074507)
  ·
    refine ⟨384036087288559568566611761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256024058192373045711074507 384036087288559568566611761)
    ·
      refine ⟨288027065466419676424958821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384036087288559568566611761 288027065466419676424958821)
      ·
        refine ⟨54005074774953689329679779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288027065466419676424958821 54005074774953689329679779)
        ·
          refine ⟨81007612162430533994519669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54005074774953689329679779 81007612162430533994519669)
          ·
            refine ⟨7594463640227862561986219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81007612162430533994519669 7594463640227862561986219)
            ·
              refine ⟨11391695460341793842979329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7594463640227862561986219 11391695460341793842979329)
              ·
                refine ⟨8543771595256345382234497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11391695460341793842979329 8543771595256345382234497)
                ·
                  refine ⟨6407828696442259036675873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8543771595256345382234497 6407828696442259036675873)
                  ·
                    refine ⟨4805871522331694277506905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6407828696442259036675873 4805871522331694277506905)
                    ·
                      refine ⟨3604403641748770708130179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4805871522331694277506905 3604403641748770708130179)
                      ·
                        rfl

theorem cell23_7019551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_7019551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019551 prefixEnd_7019551 := by exact prefixLift 7019551
  have htrace : WordTrace (prefixWord ++ tailWord_7019551) baseStart_7019551 baseEnd_7019551 := by
    simpa [prefixWord, tailWord_7019551, baseEnd_7019551] using wordTrace_append hprefix tailTrace_7019551
  have hstable : (prefixWord ++ tailWord_7019551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019551).length < 2 ^ (prefixWord ++ tailWord_7019551).sum := by decide
  have hdescent : baseEnd_7019551 < baseStart_7019551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019563 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 7]
def baseStart_7019563 : Nat := 118140960795 + 7019563 * 2 ^ 59
def prefixEnd_7019563 : Nat := 4983230072969 + 3 ^ 40 * 7019563 * 2
def baseEnd_7019563 : Nat := 3604409803516624661180123

theorem tailTrace_7019563 : CollatzResearch.WordTrace tailWord_7019563 prefixEnd_7019563 3604409803516624661180123 := by
  unfold tailWord_7019563
  simp only [CollatzResearch.WordTrace]
  refine ⟨256024495868329571760511343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170682997245553047840340895 256024495868329571760511343)
  ·
    refine ⟨384036743802494357640767015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256024495868329571760511343 384036743802494357640767015)
    ·
      refine ⟨576055115703741536461150523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384036743802494357640767015 576055115703741536461150523)
      ·
        refine ⟨864082673555612304691725785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576055115703741536461150523 864082673555612304691725785)
        ·
          refine ⟨648062005166709228518794339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864082673555612304691725785 648062005166709228518794339)
          ·
            refine ⟨972093007750063842778191509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648062005166709228518794339 972093007750063842778191509)
            ·
              refine ⟨45566859738284242630227727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 972093007750063842778191509 45566859738284242630227727)
              ·
                refine ⟨68350289607426363945341591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45566859738284242630227727 68350289607426363945341591)
                ·
                  refine ⟨102525434411139545918012387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68350289607426363945341591 102525434411139545918012387)
                  ·
                    refine ⟨153788151616709318877018581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102525434411139545918012387 153788151616709318877018581)
                    ·
                      refine ⟨3604409803516624661180123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153788151616709318877018581 3604409803516624661180123)
                      ·
                        rfl

theorem cell23_7019563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_7019563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019563 prefixEnd_7019563 := by exact prefixLift 7019563
  have htrace : WordTrace (prefixWord ++ tailWord_7019563) baseStart_7019563 baseEnd_7019563 := by
    simpa [prefixWord, tailWord_7019563, baseEnd_7019563] using wordTrace_append hprefix tailTrace_7019563
  have hstable : (prefixWord ++ tailWord_7019563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019563).length < 2 ^ (prefixWord ++ tailWord_7019563).sum := by decide
  have hdescent : baseEnd_7019563 < baseStart_7019563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019583 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 1, 10]
def baseStart_7019583 : Nat := 118140960795 + 7019583 * 2 ^ 59
def prefixEnd_7019583 : Nat := 4983230072969 + 3 ^ 40 * 7019583 * 2
def baseEnd_7019583 : Nat := 1201473357709904860976677

theorem tailTrace_7019583 : CollatzResearch.WordTrace tailWord_7019583 prefixEnd_7019583 1201473357709904860976677 := by
  unfold tailWord_7019583
  simp only [CollatzResearch.WordTrace]
  refine ⟨256025225328257115176239403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170683483552171410117492935 256025225328257115176239403)
  ·
    refine ⟨384037837992385672764359105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256025225328257115176239403 384037837992385672764359105)
    ·
      refine ⟨288028378494289254573269329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384037837992385672764359105 288028378494289254573269329)
      ·
        refine ⟨216021283870716940929951997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288028378494289254573269329 216021283870716940929951997)
        ·
          refine ⟨81007981451518852848731999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216021283870716940929951997 81007981451518852848731999)
          ·
            refine ⟨121511972177278279273097999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81007981451518852848731999 121511972177278279273097999)
            ·
              refine ⟨182267958265917418909646999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121511972177278279273097999 182267958265917418909646999)
              ·
                refine ⟨273401937398876128364470499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182267958265917418909646999 273401937398876128364470499)
                ·
                  refine ⟨410102906098314192546705749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273401937398876128364470499 410102906098314192546705749)
                  ·
                    refine ⟨1201473357709904860976677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 410102906098314192546705749 1201473357709904860976677)
                    ·
                      rfl

theorem cell23_7019583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_7019583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019583 prefixEnd_7019583 := by exact prefixLift 7019583
  have htrace : WordTrace (prefixWord ++ tailWord_7019583) baseStart_7019583 baseEnd_7019583 := by
    simpa [prefixWord, tailWord_7019583, baseEnd_7019583] using wordTrace_append hprefix tailTrace_7019583
  have hstable : (prefixWord ++ tailWord_7019583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019583).length < 2 ^ (prefixWord ++ tailWord_7019583).sum := by decide
  have hdescent : baseEnd_7019583 < baseStart_7019583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019600 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 5, 4]
def baseStart_7019600 : Nat := 118140960795 + 7019600 * 2 ^ 59
def prefixEnd_7019600 : Nat := 4983230072969 + 3 ^ 40 * 7019600 * 2
def baseEnd_7019600 : Nat := 1201476267433613672139151

theorem tailTrace_7019600 : CollatzResearch.WordTrace tailWord_7019600 prefixEnd_7019600 1201476267433613672139151 := by
  unfold tailWord_7019600
  simp only [CollatzResearch.WordTrace]
  refine ⟨128012922684597763539804127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170683896912797018053072169 128012922684597763539804127)
  ·
    refine ⟨192019384026896645309706191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128012922684597763539804127 192019384026896645309706191)
    ·
      refine ⟨288029076040344967964559287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192019384026896645309706191 288029076040344967964559287)
      ·
        refine ⟨432043614060517451946838931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288029076040344967964559287 432043614060517451946838931)
        ·
          refine ⟨648065421090776177920258397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432043614060517451946838931 648065421090776177920258397)
          ·
            refine ⟨243024532909041066720096899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 648065421090776177920258397 243024532909041066720096899)
            ·
              refine ⟨364536799363561600080145349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243024532909041066720096899 364536799363561600080145349)
              ·
                refine ⟨68350649880667800015027253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364536799363561600080145349 68350649880667800015027253)
                ·
                  refine ⟨6407873426312606251408805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68350649880667800015027253 6407873426312606251408805)
                  ·
                    refine ⟨1201476267433613672139151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6407873426312606251408805 1201476267433613672139151)
                    ·
                      rfl

theorem cell23_7019600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5, 4].length) (baseStart_7019600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019600 prefixEnd_7019600 := by exact prefixLift 7019600
  have htrace : WordTrace (prefixWord ++ tailWord_7019600) baseStart_7019600 baseEnd_7019600 := by
    simpa [prefixWord, tailWord_7019600, baseEnd_7019600] using wordTrace_append hprefix tailTrace_7019600
  have hstable : (prefixWord ++ tailWord_7019600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019600).length < 2 ^ (prefixWord ++ tailWord_7019600).sum := by decide
  have hdescent : baseEnd_7019600 < baseStart_7019600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019610 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3]
def baseStart_7019610 : Nat := 118140960795 + 7019610 * 2 ^ 59
def prefixEnd_7019610 : Nat := 4983230072969 + 3 ^ 40 * 7019610 * 2
def baseEnd_7019610 : Nat := 3604433937107385977292407

theorem tailTrace_7019610 : CollatzResearch.WordTrace tailWord_7019610 prefixEnd_7019610 3604433937107385977292407 := by
  unfold tailWord_7019610
  simp only [CollatzResearch.WordTrace]
  refine ⟨64006552524789824696868071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170684140066106199191648189 64006552524789824696868071)
  ·
    refine ⟨96009828787184737045302107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64006552524789824696868071 96009828787184737045302107)
    ·
      refine ⟨144014743180777105567953161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96009828787184737045302107 144014743180777105567953161)
      ·
        refine ⟨108011057385582829175964871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144014743180777105567953161 108011057385582829175964871)
        ·
          refine ⟨162016586078374243763947307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108011057385582829175964871 162016586078374243763947307)
          ·
            refine ⟨243024879117561365645920961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162016586078374243763947307 243024879117561365645920961)
            ·
              refine ⟨182268659338171024234440721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243024879117561365645920961 182268659338171024234440721)
              ·
                refine ⟨136701494503628268175830541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182268659338171024234440721 136701494503628268175830541)
                ·
                  refine ⟨51263060438860600565936453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136701494503628268175830541 51263060438860600565936453)
                  ·
                    refine ⟨9611823832286362606113085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51263060438860600565936453 9611823832286362606113085)
                    ·
                      refine ⟨3604433937107385977292407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9611823832286362606113085 3604433937107385977292407)
                      ·
                        rfl

theorem cell23_7019610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_7019610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019610 prefixEnd_7019610 := by exact prefixLift 7019610
  have htrace : WordTrace (prefixWord ++ tailWord_7019610) baseStart_7019610 baseEnd_7019610 := by
    simpa [prefixWord, tailWord_7019610, baseEnd_7019610] using wordTrace_append hprefix tailTrace_7019610
  have hstable : (prefixWord ++ tailWord_7019610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019610).length < 2 ^ (prefixWord ++ tailWord_7019610).sum := by decide
  have hdescent : baseEnd_7019610 < baseStart_7019610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019614 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7019614 : Nat := 118140960795 + 7019614 * 2 ^ 59
def prefixEnd_7019614 : Nat := 4983230072969 + 3 ^ 40 * 7019614 * 2
def baseEnd_7019614 : Nat := 3604435991030003961642389

theorem tailTrace_7019614 : CollatzResearch.WordTrace tailWord_7019614 prefixEnd_7019614 3604435991030003961642389 := by
  unfold tailWord_7019614
  simp only [CollatzResearch.WordTrace]
  refine ⟨32003294498893100933827237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170684237327429871647078597 32003294498893100933827237)
  ·
    refine ⟨6000617718542456425092607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32003294498893100933827237 6000617718542456425092607)
    ·
      refine ⟨9000926577813684637638911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6000617718542456425092607 9000926577813684637638911)
      ·
        refine ⟨13501389866720526956458367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9000926577813684637638911 13501389866720526956458367)
        ·
          refine ⟨20252084800080790434687551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13501389866720526956458367 20252084800080790434687551)
          ·
            refine ⟨30378127200121185652031327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20252084800080790434687551 30378127200121185652031327)
            ·
              refine ⟨45567190800181778478046991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30378127200121185652031327 45567190800181778478046991)
              ·
                refine ⟨68350786200272667717070487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45567190800181778478046991 68350786200272667717070487)
                ·
                  refine ⟨102526179300409001575605731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68350786200272667717070487 102526179300409001575605731)
                  ·
                    refine ⟨153789268950613502363408597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102526179300409001575605731 153789268950613502363408597)
                    ·
                      refine ⟨3604435991030003961642389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153789268950613502363408597 3604435991030003961642389)
                      ·
                        rfl

theorem cell23_7019614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7019614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019614 prefixEnd_7019614 := by exact prefixLift 7019614
  have htrace : WordTrace (prefixWord ++ tailWord_7019614) baseStart_7019614 baseEnd_7019614 := by
    simpa [prefixWord, tailWord_7019614, baseEnd_7019614] using wordTrace_append hprefix tailTrace_7019614
  have hstable : (prefixWord ++ tailWord_7019614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019614).length < 2 ^ (prefixWord ++ tailWord_7019614).sum := by decide
  have hdescent : baseEnd_7019614 < baseStart_7019614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019617 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 3, 4]
def baseStart_7019617 : Nat := 118140960795 + 7019617 * 2 ^ 59
def prefixEnd_7019617 : Nat := 4983230072969 + 3 ^ 40 * 7019617 * 2
def baseEnd_7019617 : Nat := 1201479177157322483301625

theorem tailTrace_7019617 : CollatzResearch.WordTrace tailWord_7019617 prefixEnd_7019617 1201479177157322483301625 := by
  unfold tailWord_7019617
  simp only [CollatzResearch.WordTrace]
  refine ⟨256026465410133938982977105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170684310273422625988651403 256026465410133938982977105)
  ·
    refine ⟨192019849057600454237232829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256026465410133938982977105 192019849057600454237232829)
    ·
      refine ⟨72007443396600170338962311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192019849057600454237232829 72007443396600170338962311)
      ·
        refine ⟨108011165094900255508443467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72007443396600170338962311 108011165094900255508443467)
        ·
          refine ⟨162016747642350383262665201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108011165094900255508443467 162016747642350383262665201)
          ·
            refine ⟨121512560731762787446998901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162016747642350383262665201 121512560731762787446998901)
            ·
              refine ⟨11391802568602761323156147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121512560731762787446998901 11391802568602761323156147)
              ·
                refine ⟨17087703852904141984734221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11391802568602761323156147 17087703852904141984734221)
                ·
                  refine ⟨6407888944839053244275333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17087703852904141984734221 6407888944839053244275333)
                  ·
                    refine ⟨1201479177157322483301625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6407888944839053244275333 1201479177157322483301625)
                    ·
                      rfl

theorem cell23_7019617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_7019617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019617 prefixEnd_7019617 := by exact prefixLift 7019617
  have htrace : WordTrace (prefixWord ++ tailWord_7019617) baseStart_7019617 baseEnd_7019617 := by
    simpa [prefixWord, tailWord_7019617, baseEnd_7019617] using wordTrace_append hprefix tailTrace_7019617
  have hstable : (prefixWord ++ tailWord_7019617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019617).length < 2 ^ (prefixWord ++ tailWord_7019617).sum := by decide
  have hdescent : baseEnd_7019617 < baseStart_7019617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019640 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 2, 5, 3]
def baseStart_7019640 : Nat := 118140960795 + 7019640 * 2 ^ 59
def prefixEnd_7019640 : Nat := 4983230072969 + 3 ^ 40 * 7019640 * 2
def baseEnd_7019640 : Nat := 3604449341527020859917269

theorem tailTrace_7019640 : CollatzResearch.WordTrace tailWord_7019640 prefixEnd_7019640 3604449341527020859917269 := by
  unfold tailWord_7019640
  simp only [CollatzResearch.WordTrace]
  refine ⟨128013652144525306955532187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170684869526033742607376249 128013652144525306955532187)
  ·
    refine ⟨192020478216787960433298281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128013652144525306955532187 192020478216787960433298281)
    ·
      refine ⟨144015358662590970324973711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192020478216787960433298281 144015358662590970324973711)
      ·
        refine ⟨216023037993886455487460567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144015358662590970324973711 216023037993886455487460567)
        ·
          refine ⟨324034556990829683231190851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216023037993886455487460567 324034556990829683231190851)
          ·
            refine ⟨486051835486244524846786277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324034556990829683231190851 486051835486244524846786277)
            ·
              refine ⟨91134719153670848408772427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 486051835486244524846786277 91134719153670848408772427)
              ·
                refine ⟨136702078730506272613158641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91134719153670848408772427 136702078730506272613158641)
                ·
                  refine ⟨102526559047879704459868981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136702078730506272613158641 102526559047879704459868981)
                  ·
                    refine ⟨9611864910738722293112717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102526559047879704459868981 9611864910738722293112717)
                    ·
                      refine ⟨3604449341527020859917269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9611864910738722293112717 3604449341527020859917269)
                      ·
                        rfl

theorem cell23_7019640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_7019640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019640 prefixEnd_7019640 := by exact prefixLift 7019640
  have htrace : WordTrace (prefixWord ++ tailWord_7019640) baseStart_7019640 baseEnd_7019640 := by
    simpa [prefixWord, tailWord_7019640, baseEnd_7019640] using wordTrace_append hprefix tailTrace_7019640
  have hstable : (prefixWord ++ tailWord_7019640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019640).length < 2 ^ (prefixWord ++ tailWord_7019640).sum := by decide
  have hdescent : baseEnd_7019640 < baseStart_7019640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019708 : List Nat := [2, 2, 2, 3, 2, 2, 2, 3, 1, 1, 3]
def baseStart_7019708 : Nat := 118140960795 + 7019708 * 2 ^ 59
def prefixEnd_7019708 : Nat := 4983230072969 + 3 ^ 40 * 7019708 * 2
def baseEnd_7019708 : Nat := 3604484258211526593866957

theorem tailTrace_7019708 : CollatzResearch.WordTrace tailWord_7019708 prefixEnd_7019708 3604484258211526593866957 := by
  unfold tailWord_7019708
  simp only [CollatzResearch.WordTrace]
  refine ⟨128014892226402130762269889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170686522968536174349693185 128014892226402130762269889)
  ·
    refine ⟨96011169169801598071702417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128014892226402130762269889 96011169169801598071702417)
    ·
      refine ⟨72008376877351198553776813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96011169169801598071702417 72008376877351198553776813)
      ·
        refine ⟨27003141329006699457666305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72008376877351198553776813 27003141329006699457666305)
        ·
          refine ⟨20252355996755024593249729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27003141329006699457666305 20252355996755024593249729)
          ·
            refine ⟨15189266997566268444937297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20252355996755024593249729 15189266997566268444937297)
            ·
              refine ⟨11391950248174701333702973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15189266997566268444937297 11391950248174701333702973)
              ·
                refine ⟨4271981343065513000138615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11391950248174701333702973 4271981343065513000138615)
                ·
                  refine ⟨6407972014598269500207923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271981343065513000138615 6407972014598269500207923)
                  ·
                    refine ⟨9611958021897404250311885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6407972014598269500207923 9611958021897404250311885)
                    ·
                      refine ⟨3604484258211526593866957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9611958021897404250311885 3604484258211526593866957)
                      ·
                        rfl

theorem cell23_7019708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_7019708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019708 prefixEnd_7019708 := by exact prefixLift 7019708
  have htrace : WordTrace (prefixWord ++ tailWord_7019708) baseStart_7019708 baseEnd_7019708 := by
    simpa [prefixWord, tailWord_7019708, baseEnd_7019708] using wordTrace_append hprefix tailTrace_7019708
  have hstable : (prefixWord ++ tailWord_7019708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019708).length < 2 ^ (prefixWord ++ tailWord_7019708).sum := by decide
  have hdescent : baseEnd_7019708 < baseStart_7019708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019725 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_7019725 : Nat := 118140960795 + 7019725 * 2 ^ 59
def prefixEnd_7019725 : Nat := 4983230072969 + 3 ^ 40 * 7019725 * 2
def baseEnd_7019725 : Nat := 3604492987382653027354379

theorem tailTrace_7019725 : CollatzResearch.WordTrace tailWord_7019725 prefixEnd_7019725 3604492987382653027354379 := by
  unfold tailWord_7019725
  simp only [CollatzResearch.WordTrace]
  refine ⟨256030404493742673427908629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170686936329161782285272419 256030404493742673427908629)
  ·
    refine ⟨12001425210644187816933217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 256030404493742673427908629 12001425210644187816933217)
    ·
      refine ⟨9001068907983140862699913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12001425210644187816933217 9001068907983140862699913)
      ·
        refine ⟨6750801680987355647024935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9001068907983140862699913 6750801680987355647024935)
        ·
          refine ⟨10126202521481033470537403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6750801680987355647024935 10126202521481033470537403)
          ·
            refine ⟨15189303782221550205806105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10126202521481033470537403 15189303782221550205806105)
            ·
              refine ⟨11391977836666162654354579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15189303782221550205806105 11391977836666162654354579)
              ·
                refine ⟨17087966754999243981531869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11391977836666162654354579 17087966754999243981531869)
                ·
                  refine ⟨6407987533124716493074451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17087966754999243981531869 6407987533124716493074451)
                  ·
                    refine ⟨9611981299687074739611677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6407987533124716493074451 9611981299687074739611677)
                    ·
                      refine ⟨3604492987382653027354379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9611981299687074739611677 3604492987382653027354379)
                      ·
                        rfl

theorem cell23_7019725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_7019725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019725 prefixEnd_7019725 := by exact prefixLift 7019725
  have htrace : WordTrace (prefixWord ++ tailWord_7019725) baseStart_7019725 baseEnd_7019725 := by
    simpa [prefixWord, tailWord_7019725, baseEnd_7019725] using wordTrace_append hprefix tailTrace_7019725
  have hstable : (prefixWord ++ tailWord_7019725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019725).length < 2 ^ (prefixWord ++ tailWord_7019725).sum := by decide
  have hdescent : baseEnd_7019725 < baseStart_7019725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019741 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_7019741 : Nat := 118140960795 + 7019741 * 2 ^ 59
def prefixEnd_7019741 : Nat := 4983230072969 + 3 ^ 40 * 7019741 * 2
def baseEnd_7019741 : Nat := 1201500401024374988251435

theorem tailTrace_7019741 : CollatzResearch.WordTrace tailWord_7019741 prefixEnd_7019741 1201500401024374988251435 := by
  unfold tailWord_7019741
  simp only [CollatzResearch.WordTrace]
  refine ⟨256030988061684708160491077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170687325374456472106994051 256030988061684708160491077)
  ·
    refine ⟨48005810261565882780092077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256030988061684708160491077 48005810261565882780092077)
    ·
      refine ⟨18002178848087206042534529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48005810261565882780092077 18002178848087206042534529)
      ·
        refine ⟨13501634136065404531900897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18002178848087206042534529 13501634136065404531900897)
        ·
          refine ⟨10126225602049053398925673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13501634136065404531900897 10126225602049053398925673)
          ·
            refine ⟨7594669201536790049194255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10126225602049053398925673 7594669201536790049194255)
            ·
              refine ⟨11392003802305185073791383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7594669201536790049194255 11392003802305185073791383)
              ·
                refine ⟨17088005703457777610687075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11392003802305185073791383 17088005703457777610687075)
                ·
                  refine ⟨25632008555186666416030613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17088005703457777610687075 25632008555186666416030613)
                  ·
                    refine ⟨1201500401024374988251435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25632008555186666416030613 1201500401024374988251435)
                    ·
                      rfl

theorem cell23_7019741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_7019741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019741 prefixEnd_7019741 := by exact prefixLift 7019741
  have htrace : WordTrace (prefixWord ++ tailWord_7019741) baseStart_7019741 baseEnd_7019741 := by
    simpa [prefixWord, tailWord_7019741, baseEnd_7019741] using wordTrace_append hprefix tailTrace_7019741
  have hstable : (prefixWord ++ tailWord_7019741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019741).length < 2 ^ (prefixWord ++ tailWord_7019741).sum := by decide
  have hdescent : baseEnd_7019741 < baseStart_7019741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019744 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 4]
def baseStart_7019744 : Nat := 118140960795 + 7019744 * 2 ^ 59
def prefixEnd_7019744 : Nat := 4983230072969 + 3 ^ 40 * 7019744 * 2
def baseEnd_7019744 : Nat := 3604502743515088453016791

theorem tailTrace_7019744 : CollatzResearch.WordTrace tailWord_7019744 prefixEnd_7019744 3604502743515088453016791 := by
  unfold tailWord_7019744
  simp only [CollatzResearch.WordTrace]
  refine ⟨128015548740336919836425143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170687398320449226448566857 128015548740336919836425143)
  ·
    refine ⟨192023323110505379754637715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128015548740336919836425143 192023323110505379754637715)
    ·
      refine ⟨288034984665758069631956573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192023323110505379754637715 288034984665758069631956573)
      ·
        refine ⟨108013119249659276111983715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288034984665758069631956573 108013119249659276111983715)
        ·
          refine ⟨162019678874488914167975573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108013119249659276111983715 162019678874488914167975573)
          ·
            refine ⟨7594672447241667851623855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162019678874488914167975573 7594672447241667851623855)
            ·
              refine ⟨11392008670862501777435783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7594672447241667851623855 11392008670862501777435783)
              ·
                refine ⟨17088013006293752666153675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11392008670862501777435783 17088013006293752666153675)
                ·
                  refine ⟨25632019509440628999230513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17088013006293752666153675 25632019509440628999230513)
                  ·
                    refine ⟨19224014632080471749422885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25632019509440628999230513 19224014632080471749422885)
                    ·
                      refine ⟨3604502743515088453016791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19224014632080471749422885 3604502743515088453016791)
                      ·
                        rfl

theorem cell23_7019744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_7019744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019744 prefixEnd_7019744 := by exact prefixLift 7019744
  have htrace : WordTrace (prefixWord ++ tailWord_7019744) baseStart_7019744 baseEnd_7019744 := by
    simpa [prefixWord, tailWord_7019744, baseEnd_7019744] using wordTrace_append hprefix tailTrace_7019744
  have hstable : (prefixWord ++ tailWord_7019744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019744).length < 2 ^ (prefixWord ++ tailWord_7019744).sum := by decide
  have hdescent : baseEnd_7019744 < baseStart_7019744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019754 : List Nat := [3, 1, 3, 1, 1, 5, 2, 7]
def baseStart_7019754 : Nat := 118140960795 + 7019754 * 2 ^ 59
def prefixEnd_7019754 : Nat := 4983230072969 + 3 ^ 40 * 7019754 * 2
def baseEnd_7019754 : Nat := 133500291789690126440435

theorem tailTrace_7019754 : CollatzResearch.WordTrace tailWord_7019754 prefixEnd_7019754 133500291789690126440435 := by
  unfold tailWord_7019754
  simp only [CollatzResearch.WordTrace]
  refine ⟨64007865552659402845178579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170687641473758407587142877 64007865552659402845178579)
  ·
    refine ⟨96011798328989104267767869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64007865552659402845178579 96011798328989104267767869)
    ·
      refine ⟨36004424373370914100412951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96011798328989104267767869 36004424373370914100412951)
      ·
        refine ⟨54006636560056371150619427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36004424373370914100412951 54006636560056371150619427)
        ·
          refine ⟨81009954840084556725929141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54006636560056371150619427 81009954840084556725929141)
          ·
            refine ⟨7594683266257927193055857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81009954840084556725929141 7594683266257927193055857)
            ·
              refine ⟨5696012449693445394791893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7594683266257927193055857 5696012449693445394791893)
              ·
                refine ⟨133500291789690126440435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5696012449693445394791893 133500291789690126440435)
                ·
                  rfl

theorem cell23_7019754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 7].length) (baseStart_7019754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019754 prefixEnd_7019754 := by exact prefixLift 7019754
  have htrace : WordTrace (prefixWord ++ tailWord_7019754) baseStart_7019754 baseEnd_7019754 := by
    simpa [prefixWord, tailWord_7019754, baseEnd_7019754] using wordTrace_append hprefix tailTrace_7019754
  have hstable : (prefixWord ++ tailWord_7019754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019754).length < 2 ^ (prefixWord ++ tailWord_7019754).sum := by decide
  have hdescent : baseEnd_7019754 < baseStart_7019754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019854 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_7019854 : Nat := 118140960795 + 7019854 * 2 ^ 59
def prefixEnd_7019854 : Nat := 4983230072969 + 3 ^ 40 * 7019854 * 2
def baseEnd_7019854 : Nat := 3604559226387083022641285

theorem tailTrace_7019854 : CollatzResearch.WordTrace tailWord_7019854 prefixEnd_7019854 3604559226387083022641285 := by
  unfold tailWord_7019854
  simp only [CollatzResearch.WordTrace]
  refine ⟨32004388688784416057419327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170690073006850218972903077 32004388688784416057419327)
  ·
    refine ⟨48006583033176624086128991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32004388688784416057419327 48006583033176624086128991)
    ·
      refine ⟨72009874549764936129193487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48006583033176624086128991 72009874549764936129193487)
      ·
        refine ⟨108014811824647404193790231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72009874549764936129193487 108014811824647404193790231)
        ·
          refine ⟨162022217736971106290685347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108014811824647404193790231 162022217736971106290685347)
          ·
            refine ⟨243033326605456659436028021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162022217736971106290685347 243033326605456659436028021)
            ·
              refine ⟨22784374369261561822127627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243033326605456659436028021 22784374369261561822127627)
              ·
                refine ⟨34176561553892342733191441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22784374369261561822127627 34176561553892342733191441)
                ·
                  refine ⟨25632421165419257049893581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34176561553892342733191441 25632421165419257049893581)
                  ·
                    refine ⟨9612157937032221393710093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25632421165419257049893581 9612157937032221393710093)
                    ·
                      refine ⟨3604559226387083022641285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9612157937032221393710093 3604559226387083022641285)
                      ·
                        rfl

theorem cell23_7019854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_7019854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019854 prefixEnd_7019854 := by exact prefixLift 7019854
  have htrace : WordTrace (prefixWord ++ tailWord_7019854) baseStart_7019854 baseEnd_7019854 := by
    simpa [prefixWord, tailWord_7019854, baseEnd_7019854] using wordTrace_append hprefix tailTrace_7019854
  have hstable : (prefixWord ++ tailWord_7019854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019854).length < 2 ^ (prefixWord ++ tailWord_7019854).sum := by decide
  have hdescent : baseEnd_7019854 < baseStart_7019854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019857 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 1, 7]
def baseStart_7019857 : Nat := 118140960795 + 7019857 * 2 ^ 59
def prefixEnd_7019857 : Nat := 4983230072969 + 3 ^ 40 * 7019857 * 2
def baseEnd_7019857 : Nat := 1201520255609682170301257

theorem tailTrace_7019857 : CollatzResearch.WordTrace tailWord_7019857 prefixEnd_7019857 1201520255609682170301257 := by
  unfold tailWord_7019857
  simp only [CollatzResearch.WordTrace]
  refine ⟨256035218929264459971713825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170690145952842973314475883 256035218929264459971713825)
  ·
    refine ⟨192026414196948344978785369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256035218929264459971713825 192026414196948344978785369)
    ·
      refine ⟨144019810647711258734089027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192026414196948344978785369 144019810647711258734089027)
      ·
        refine ⟨216029715971566888101133541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144019810647711258734089027 216029715971566888101133541)
        ·
          refine ⟨40505571744668791518962539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216029715971566888101133541 40505571744668791518962539)
          ·
            refine ⟨60758357617003187278443809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40505571744668791518962539 60758357617003187278443809)
            ·
              refine ⟨45568768212752390458832857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60758357617003187278443809 45568768212752390458832857)
              ·
                refine ⟨34176576159564292844124643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45568768212752390458832857 34176576159564292844124643)
                ·
                  refine ⟨51264864239346439266186965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34176576159564292844124643 51264864239346439266186965)
                  ·
                    refine ⟨1201520255609682170301257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51264864239346439266186965 1201520255609682170301257)
                    ·
                      rfl

theorem cell23_7019857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_7019857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019857 prefixEnd_7019857 := by exact prefixLift 7019857
  have htrace : WordTrace (prefixWord ++ tailWord_7019857) baseStart_7019857 baseEnd_7019857 := by
    simpa [prefixWord, tailWord_7019857, baseEnd_7019857] using wordTrace_append hprefix tailTrace_7019857
  have hstable : (prefixWord ++ tailWord_7019857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019857).length < 2 ^ (prefixWord ++ tailWord_7019857).sum := by decide
  have hdescent : baseEnd_7019857 < baseStart_7019857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019864 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 2, 5, 2]
def baseStart_7019864 : Nat := 118140960795 + 7019864 * 2 ^ 59
def prefixEnd_7019864 : Nat := 4983230072969 + 3 ^ 40 * 7019864 * 2
def baseEnd_7019864 : Nat := 3604564361193627983516239

theorem tailTrace_7019864 : CollatzResearch.WordTrace tailWord_7019864 prefixEnd_7019864 3604564361193627983516239 := by
  unfold tailWord_7019864
  simp only [CollatzResearch.WordTrace]
  refine ⟨128017737120119550083609323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170690316160159400111479097 128017737120119550083609323)
  ·
    refine ⟨192026605680179325125413985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128017737120119550083609323 192026605680179325125413985)
    ·
      refine ⟨144019954260134493844060489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192026605680179325125413985 144019954260134493844060489)
      ·
        refine ⟨108014965695100870383045367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144019954260134493844060489 108014965695100870383045367)
        ·
          refine ⟨162022448542651305574568051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108014965695100870383045367 162022448542651305574568051)
          ·
            refine ⟨243033672813976958361852077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162022448542651305574568051 243033672813976958361852077)
            ·
              refine ⟨91137627305241359385694529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243033672813976958361852077 91137627305241359385694529)
              ·
                refine ⟨68353220478931019539270897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91137627305241359385694529 68353220478931019539270897)
                ·
                  refine ⟨51264915359198264654453173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68353220478931019539270897 51264915359198264654453173)
                  ·
                    refine ⟨4806085814924837311354985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51264915359198264654453173 4806085814924837311354985)
                    ·
                      refine ⟨3604564361193627983516239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4806085814924837311354985 3604564361193627983516239)
                      ·
                        rfl

theorem cell23_7019864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_7019864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019864 prefixEnd_7019864 := by exact prefixLift 7019864
  have htrace : WordTrace (prefixWord ++ tailWord_7019864) baseStart_7019864 baseEnd_7019864 := by
    simpa [prefixWord, tailWord_7019864, baseEnd_7019864] using wordTrace_append hprefix tailTrace_7019864
  have hstable : (prefixWord ++ tailWord_7019864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019864).length < 2 ^ (prefixWord ++ tailWord_7019864).sum := by decide
  have hdescent : baseEnd_7019864 < baseStart_7019864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019874 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_7019874 : Nat := 118140960795 + 7019874 * 2 ^ 59
def prefixEnd_7019874 : Nat := 4983230072969 + 3 ^ 40 * 7019874 * 2
def baseEnd_7019874 : Nat := 1201523165333390981463731

theorem tailTrace_7019874 : CollatzResearch.WordTrace tailWord_7019874 prefixEnd_7019874 1201523165333390981463731 := by
  unfold tailWord_7019874
  simp only [CollatzResearch.WordTrace]
  refine ⟨64008959742550717968770669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170690559313468581250055117 64008959742550717968770669)
  ·
    refine ⟨24003359903456519238289001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64008959742550717968770669 24003359903456519238289001)
    ·
      refine ⟨18002519927592389428716751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24003359903456519238289001 18002519927592389428716751)
      ·
        refine ⟨27003779891388584143075127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18002519927592389428716751 27003779891388584143075127)
        ·
          refine ⟨40505669837082876214612691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27003779891388584143075127 40505669837082876214612691)
          ·
            refine ⟨60758504755624314321919037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40505669837082876214612691 60758504755624314321919037)
            ·
              refine ⟨22784439283359117870719639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60758504755624314321919037 22784439283359117870719639)
              ·
                refine ⟨34176658925038676806079459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22784439283359117870719639 34176658925038676806079459)
                ·
                  refine ⟨51264988387558015209119189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34176658925038676806079459 51264988387558015209119189)
                  ·
                    refine ⟨1201523165333390981463731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51264988387558015209119189 1201523165333390981463731)
                    ·
                      rfl

theorem cell23_7019874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_7019874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019874 prefixEnd_7019874 := by exact prefixLift 7019874
  have htrace : WordTrace (prefixWord ++ tailWord_7019874) baseStart_7019874 baseEnd_7019874 := by
    simpa [prefixWord, tailWord_7019874, baseEnd_7019874] using wordTrace_append hprefix tailTrace_7019874
  have hstable : (prefixWord ++ tailWord_7019874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019874).length < 2 ^ (prefixWord ++ tailWord_7019874).sum := by decide
  have hdescent : baseEnd_7019874 < baseStart_7019874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019897 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_7019897 : Nat := 118140960795 + 7019897 * 2 ^ 59
def prefixEnd_7019897 : Nat := 4983230072969 + 3 ^ 40 * 7019897 * 2
def baseEnd_7019897 : Nat := 3604581306055226354403587

theorem tailTrace_7019897 : CollatzResearch.WordTrace tailWord_7019897 prefixEnd_7019897 3604581306055226354403587 := by
  unfold tailWord_7019897
  simp only [CollatzResearch.WordTrace]
  refine ⟨256036677849119546803169945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170691118566079697868779963 256036677849119546803169945)
  ·
    refine ⟨192027508386839660102377459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256036677849119546803169945 192027508386839660102377459)
    ·
      refine ⟨288041262580259490153566189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192027508386839660102377459 288041262580259490153566189)
      ·
        refine ⟨108015473467597308807587321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288041262580259490153566189 108015473467597308807587321)
        ·
          refine ⟨81011605100697981605690491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108015473467597308807587321 81011605100697981605690491)
          ·
            refine ⟨121517407651046972408535737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81011605100697981605690491 121517407651046972408535737)
            ·
              refine ⟨91138055738285229306401803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121517407651046972408535737 91138055738285229306401803)
              ·
                refine ⟨136707083607427843959602705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91138055738285229306401803 136707083607427843959602705)
                ·
                  refine ⟨102530312705570882969702029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136707083607427843959602705 102530312705570882969702029)
                  ·
                    refine ⟨38448867264589081113638261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102530312705570882969702029 38448867264589081113638261)
                    ·
                      refine ⟨3604581306055226354403587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38448867264589081113638261 3604581306055226354403587)
                      ·
                        rfl

theorem cell23_7019897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_7019897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019897 prefixEnd_7019897 := by exact prefixLift 7019897
  have htrace : WordTrace (prefixWord ++ tailWord_7019897) baseStart_7019897 baseEnd_7019897 := by
    simpa [prefixWord, tailWord_7019897, baseEnd_7019897] using wordTrace_append hprefix tailTrace_7019897
  have hstable : (prefixWord ++ tailWord_7019897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019897).length < 2 ^ (prefixWord ++ tailWord_7019897).sum := by decide
  have hdescent : baseEnd_7019897 < baseStart_7019897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019911 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 2, 4, 2]
def baseStart_7019911 : Nat := 118140960795 + 7019911 * 2 ^ 59
def prefixEnd_7019911 : Nat := 4983230072969 + 3 ^ 40 * 7019911 * 2
def baseEnd_7019911 : Nat := 3604588494784389299628523

theorem tailTrace_7019911 : CollatzResearch.WordTrace tailWord_7019911 prefixEnd_7019911 3604588494784389299628523 := by
  unfold tailWord_7019911
  simp only [CollatzResearch.WordTrace]
  refine ⟨256037188471068827194179587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170691458980712551462786391 256037188471068827194179587)
  ·
    refine ⟨384055782706603240791269381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256037188471068827194179587 384055782706603240791269381)
    ·
      refine ⟨72010459257488107648363009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384055782706603240791269381 72010459257488107648363009)
      ·
        refine ⟨54007844443116080736272257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72010459257488107648363009 54007844443116080736272257)
        ·
          refine ⟨40505883332337060552204193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54007844443116080736272257 40505883332337060552204193)
          ·
            refine ⟨30379412499252795414153145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40505883332337060552204193 30379412499252795414153145)
            ·
              refine ⟨22784559374439596560614859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30379412499252795414153145 22784559374439596560614859)
              ·
                refine ⟨34176839061659394840922289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22784559374439596560614859 34176839061659394840922289)
                ·
                  refine ⟨25632629296244546130691717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34176839061659394840922289 25632629296244546130691717)
                  ·
                    refine ⟨4806117993045852399504697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25632629296244546130691717 4806117993045852399504697)
                    ·
                      refine ⟨3604588494784389299628523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4806117993045852399504697 3604588494784389299628523)
                      ·
                        rfl

theorem cell23_7019911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_7019911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019911 prefixEnd_7019911 := by exact prefixLift 7019911
  have htrace : WordTrace (prefixWord ++ tailWord_7019911) baseStart_7019911 baseEnd_7019911 := by
    simpa [prefixWord, tailWord_7019911, baseEnd_7019911] using wordTrace_append hprefix tailTrace_7019911
  have hstable : (prefixWord ++ tailWord_7019911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019911).length < 2 ^ (prefixWord ++ tailWord_7019911).sum := by decide
  have hdescent : baseEnd_7019911 < baseStart_7019911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019984 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 4]
def baseStart_7019984 : Nat := 118140960795 + 7019984 * 2 ^ 59
def prefixEnd_7019984 : Nat := 4983230072969 + 3 ^ 40 * 7019984 * 2
def baseEnd_7019984 : Nat := 3604625978872167514015687

theorem tailTrace_7019984 : CollatzResearch.WordTrace tailWord_7019984 prefixEnd_7019984 3604625978872167514015687 := by
  unfold tailWord_7019984
  simp only [CollatzResearch.WordTrace]
  refine ⟨128019925499902180330793503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170693233999869573774391337 128019925499902180330793503)
  ·
    refine ⟨192029888249853270496190255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128019925499902180330793503 192029888249853270496190255)
    ·
      refine ⟨288044832374779905744285383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192029888249853270496190255 288044832374779905744285383)
      ·
        refine ⟨432067248562169858616428075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288044832374779905744285383 432067248562169858616428075)
        ·
          refine ⟨648100872843254787924642113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432067248562169858616428075 648100872843254787924642113)
          ·
            refine ⟨486075654632441090943481585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648100872843254787924642113 486075654632441090943481585)
            ·
              refine ⟨364556740974330818207611189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486075654632441090943481585 364556740974330818207611189)
              ·
                refine ⟨34177194466343514206963549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 364556740974330818207611189 34177194466343514206963549)
                ·
                  refine ⟨12816447924878817827611331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34177194466343514206963549 12816447924878817827611331)
                  ·
                    refine ⟨19224671887318226741416997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12816447924878817827611331 19224671887318226741416997)
                    ·
                      refine ⟨3604625978872167514015687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19224671887318226741416997 3604625978872167514015687)
                      ·
                        rfl

theorem cell23_7019984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_7019984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019984 prefixEnd_7019984 := by exact prefixLift 7019984
  have htrace : WordTrace (prefixWord ++ tailWord_7019984) baseStart_7019984 baseEnd_7019984 := by
    simpa [prefixWord, tailWord_7019984, baseEnd_7019984] using wordTrace_append hprefix tailTrace_7019984
  have hstable : (prefixWord ++ tailWord_7019984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019984).length < 2 ^ (prefixWord ++ tailWord_7019984).sum := by decide
  have hdescent : baseEnd_7019984 < baseStart_7019984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019987 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 11]
def baseStart_7019987 : Nat := 118140960795 + 7019987 * 2 ^ 59
def prefixEnd_7019987 : Nat := 4983230072969 + 3 ^ 40 * 7019987 * 2
def baseEnd_7019987 : Nat := 3604627519314131002278173

theorem tailTrace_7019987 : CollatzResearch.WordTrace tailWord_7019987 prefixEnd_7019987 3604627519314131002278173 := by
  unfold tailWord_7019987
  simp only [CollatzResearch.WordTrace]
  refine ⟨256039960418793492173946215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170693306945862328115964143 256039960418793492173946215)
  ·
    refine ⟨384059940628190238260919323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256039960418793492173946215 384059940628190238260919323)
    ·
      refine ⟨576089910942285357391378985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384059940628190238260919323 576089910942285357391378985)
      ·
        refine ⟨432067433206714018043534239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576089910942285357391378985 432067433206714018043534239)
        ·
          refine ⟨648101149810071027065301359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432067433206714018043534239 648101149810071027065301359)
          ·
            refine ⟨972151724715106540597952039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648101149810071027065301359 972151724715106540597952039)
            ·
              refine ⟨1458227587072659810896928059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972151724715106540597952039 1458227587072659810896928059)
              ·
                refine ⟨2187341380608989716345392089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458227587072659810896928059 2187341380608989716345392089)
                ·
                  refine ⟨1640506035456742287259044067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2187341380608989716345392089 1640506035456742287259044067)
                  ·
                    refine ⟨2460759053185113430888566101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1640506035456742287259044067 2460759053185113430888566101)
                    ·
                      refine ⟨3604627519314131002278173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2460759053185113430888566101 3604627519314131002278173)
                      ·
                        rfl

theorem cell23_7019987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_7019987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019987 prefixEnd_7019987 := by exact prefixLift 7019987
  have htrace : WordTrace (prefixWord ++ tailWord_7019987) baseStart_7019987 baseEnd_7019987 := by
    simpa [prefixWord, tailWord_7019987, baseEnd_7019987] using wordTrace_append hprefix tailTrace_7019987
  have hstable : (prefixWord ++ tailWord_7019987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019987).length < 2 ^ (prefixWord ++ tailWord_7019987).sum := by decide
  have hdescent : baseEnd_7019987 < baseStart_7019987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7019994 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_7019994 : Nat := 118140960795 + 7019994 * 2 ^ 59
def prefixEnd_7019994 : Nat := 4983230072969 + 3 ^ 40 * 7019994 * 2
def baseEnd_7019994 : Nat := 1201543704559570824963547

theorem tailTrace_7019994 : CollatzResearch.WordTrace tailWord_7019994 prefixEnd_7019994 1201543704559570824963547 := by
  unfold tailWord_7019994
  simp only [CollatzResearch.WordTrace]
  refine ⟨64010053932442033092362759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170693477153178754912967357 64010053932442033092362759)
  ·
    refine ⟨96015080898663049638544139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64010053932442033092362759 96015080898663049638544139)
    ·
      refine ⟨144022621347994574457816209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96015080898663049638544139 144022621347994574457816209)
      ·
        refine ⟨108016966010995930843362157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144022621347994574457816209 108016966010995930843362157)
        ·
          refine ⟨40506362254123474066260809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108016966010995930843362157 40506362254123474066260809)
          ·
            refine ⟨30379771690592605549695607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40506362254123474066260809 30379771690592605549695607)
            ·
              refine ⟨45569657535888908324543411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30379771690592605549695607 45569657535888908324543411)
              ·
                refine ⟨68354486303833362486815117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45569657535888908324543411 68354486303833362486815117)
                ·
                  refine ⟨25632932363937510932555669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68354486303833362486815117 25632932363937510932555669)
                  ·
                    refine ⟨1201543704559570824963547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25632932363937510932555669 1201543704559570824963547)
                    ·
                      rfl

theorem cell23_7019994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_7019994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7019994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7019994 prefixEnd_7019994 := by exact prefixLift 7019994
  have htrace : WordTrace (prefixWord ++ tailWord_7019994) baseStart_7019994 baseEnd_7019994 := by
    simpa [prefixWord, tailWord_7019994, baseEnd_7019994] using wordTrace_append hprefix tailTrace_7019994
  have hstable : (prefixWord ++ tailWord_7019994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7019994).length < 2 ^ (prefixWord ++ tailWord_7019994).sum := by decide
  have hdescent : baseEnd_7019994 < baseStart_7019994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7019994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020024 : List Nat := [2, 1, 2, 1, 1, 5, 3, 8]
def baseStart_7020024 : Nat := 118140960795 + 7020024 * 2 ^ 59
def prefixEnd_7020024 : Nat := 4983230072969 + 3 ^ 40 * 7020024 * 2
def baseEnd_7020024 : Nat := 133505426596235087315389

theorem tailTrace_7020024 : CollatzResearch.WordTrace tailWord_7020024 prefixEnd_7020024 133505426596235087315389 := by
  unfold tailWord_7020024
  simp only [CollatzResearch.WordTrace]
  refine ⟨128020654959829723746521563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170694206613106298328695417 128020654959829723746521563)
  ·
    refine ⟨192030982439744585619782345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128020654959829723746521563 192030982439744585619782345)
    ·
      refine ⟨144023236829808439214836759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192030982439744585619782345 144023236829808439214836759)
      ·
        refine ⟨216034855244712658822255139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144023236829808439214836759 216034855244712658822255139)
        ·
          refine ⟨324052282867068988233382709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216034855244712658822255139 324052282867068988233382709)
          ·
            refine ⟨30379901518787717646879629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 324052282867068988233382709 30379901518787717646879629)
            ·
              refine ⟨11392463069545394117579861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30379901518787717646879629 11392463069545394117579861)
              ·
                refine ⟨133505426596235087315389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11392463069545394117579861 133505426596235087315389)
                ·
                  rfl

theorem cell23_7020024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 8].length) (baseStart_7020024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020024 prefixEnd_7020024 := by exact prefixLift 7020024
  have htrace : WordTrace (prefixWord ++ tailWord_7020024) baseStart_7020024 baseEnd_7020024 := by
    simpa [prefixWord, tailWord_7020024, baseEnd_7020024] using wordTrace_append hprefix tailTrace_7020024
  have hstable : (prefixWord ++ tailWord_7020024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020024).length < 2 ^ (prefixWord ++ tailWord_7020024).sum := by decide
  have hdescent : baseEnd_7020024 < baseStart_7020024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020051 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 3]
def baseStart_7020051 : Nat := 118140960795 + 7020051 * 2 ^ 59
def prefixEnd_7020051 : Nat := 4983230072969 + 3 ^ 40 * 7020051 * 2
def baseEnd_7020051 : Nat := 3604660382076018751877879

theorem tailTrace_7020051 : CollatzResearch.WordTrace tailWord_7020051 prefixEnd_7020051 3604660382076018751877879 := by
  unfold tailWord_7020051
  simp only [CollatzResearch.WordTrace]
  refine ⟨256042294690561631104276007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170694863127041087402850671 256042294690561631104276007)
  ·
    refine ⟨384063442035842446656414011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256042294690561631104276007 384063442035842446656414011)
    ·
      refine ⟨576095163053763669984621017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384063442035842446656414011 576095163053763669984621017)
      ·
        refine ⟨432071372290322752488465763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576095163053763669984621017 432071372290322752488465763)
        ·
          refine ⟨648107058435484128732698645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432071372290322752488465763 648107058435484128732698645)
          ·
            refine ⟨30380018364163318534345249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 648107058435484128732698645 30380018364163318534345249)
            ·
              refine ⟨22785013773122488900758937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30380018364163318534345249 22785013773122488900758937)
              ·
                refine ⟨17088760329841866675569203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22785013773122488900758937 17088760329841866675569203)
                ·
                  refine ⟨25633140494762800013353805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17088760329841866675569203 25633140494762800013353805)
                  ·
                    refine ⟨9612427685536050005007677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25633140494762800013353805 9612427685536050005007677)
                    ·
                      refine ⟨3604660382076018751877879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9612427685536050005007677 3604660382076018751877879)
                      ·
                        rfl

theorem cell23_7020051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 3].length) (baseStart_7020051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020051 prefixEnd_7020051 := by exact prefixLift 7020051
  have htrace : WordTrace (prefixWord ++ tailWord_7020051) baseStart_7020051 baseEnd_7020051 := by
    simpa [prefixWord, tailWord_7020051, baseEnd_7020051] using wordTrace_append hprefix tailTrace_7020051
  have hstable : (prefixWord ++ tailWord_7020051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020051).length < 2 ^ (prefixWord ++ tailWord_7020051).sum := by decide
  have hdescent : baseEnd_7020051 < baseStart_7020051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020095 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 1, 3, 2]
def baseStart_7020095 : Nat := 118140960795 + 7020095 * 2 ^ 59
def prefixEnd_7020095 : Nat := 4983230072969 + 3 ^ 40 * 7020095 * 2
def baseEnd_7020095 : Nat := 3604682975224816579727677

theorem tailTrace_7020095 : CollatzResearch.WordTrace tailWord_7020095 prefixEnd_7020095 3604682975224816579727677 := by
  unfold tailWord_7020095
  simp only [CollatzResearch.WordTrace]
  refine ⟨256043899502402226618877739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170695933001601484412585159 256043899502402226618877739)
  ·
    refine ⟨384065849253603339928316609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256043899502402226618877739 384065849253603339928316609)
    ·
      refine ⟨288049386940202504946237457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384065849253603339928316609 288049386940202504946237457)
      ·
        refine ⟨216037040205151878709678093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288049386940202504946237457 216037040205151878709678093)
        ·
          refine ⟨81013890076931954516129285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216037040205151878709678093 81013890076931954516129285)
          ·
            refine ⟨15190104389424741471774241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81013890076931954516129285 15190104389424741471774241)
            ·
              refine ⟨11392578292068556103830681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15190104389424741471774241 11392578292068556103830681)
              ·
                refine ⟨8544433719051417077873011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11392578292068556103830681 8544433719051417077873011)
                ·
                  refine ⟨12816650578577125616809517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8544433719051417077873011 12816650578577125616809517)
                  ·
                    refine ⟨4806243966966422106303569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12816650578577125616809517 4806243966966422106303569)
                    ·
                      refine ⟨3604682975224816579727677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4806243966966422106303569 3604682975224816579727677)
                      ·
                        rfl

theorem cell23_7020095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_7020095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020095 prefixEnd_7020095 := by exact prefixLift 7020095
  have htrace : WordTrace (prefixWord ++ tailWord_7020095) baseStart_7020095 baseEnd_7020095 := by
    simpa [prefixWord, tailWord_7020095, baseEnd_7020095] using wordTrace_append hprefix tailTrace_7020095
  have hstable : (prefixWord ++ tailWord_7020095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020095).length < 2 ^ (prefixWord ++ tailWord_7020095).sum := by decide
  have hdescent : baseEnd_7020095 < baseStart_7020095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020131 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 7]
def baseStart_7020131 : Nat := 118140960795 + 7020131 * 2 ^ 59
def prefixEnd_7020131 : Nat := 4983230072969 + 3 ^ 40 * 7020131 * 2
def baseEnd_7020131 : Nat := 400522384503153159875279

theorem tailTrace_7020131 : CollatzResearch.WordTrace tailWord_7020131 prefixEnd_7020131 400522384503153159875279 := by
  unfold tailWord_7020131
  simp only [CollatzResearch.WordTrace]
  refine ⟨256045212530271804767188247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170696808353514536511458831 256045212530271804767188247)
  ·
    refine ⟨384067818795407707150782371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256045212530271804767188247 384067818795407707150782371)
    ·
      refine ⟨576101728193111560726173557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384067818795407707150782371 576101728193111560726173557)
      ·
        refine ⟨54009537018104208818078771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 576101728193111560726173557 54009537018104208818078771)
        ·
          refine ⟨81014305527156313227118157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54009537018104208818078771 81014305527156313227118157)
          ·
            refine ⟨30380364572683617460169309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81014305527156313227118157 30380364572683617460169309)
            ·
              refine ⟨11392636714756356547563491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30380364572683617460169309 11392636714756356547563491)
              ·
                refine ⟨17088955072134534821345237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11392636714756356547563491 17088955072134534821345237)
                ·
                  refine ⟨400522384503153159875279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17088955072134534821345237 400522384503153159875279)
                  ·
                    rfl

theorem cell23_7020131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 7].length) (baseStart_7020131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020131 prefixEnd_7020131 := by exact prefixLift 7020131
  have htrace : WordTrace (prefixWord ++ tailWord_7020131) baseStart_7020131 baseEnd_7020131 := by
    simpa [prefixWord, tailWord_7020131, baseEnd_7020131] using wordTrace_append hprefix tailTrace_7020131
  have hstable : (prefixWord ++ tailWord_7020131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020131).length < 2 ^ (prefixWord ++ tailWord_7020131).sum := by decide
  have hdescent : baseEnd_7020131 < baseStart_7020131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020215 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 4]
def baseStart_7020215 : Nat := 118140960795 + 7020215 * 2 ^ 59
def prefixEnd_7020215 : Nat := 4983230072969 + 3 ^ 40 * 7020215 * 2
def baseEnd_7020215 : Nat := 3604744592903356110227125

theorem tailTrace_7020215 : CollatzResearch.WordTrace tailWord_7020215 prefixEnd_7020215 3604744592903356110227125 := by
  unfold tailWord_7020215
  simp only [CollatzResearch.WordTrace]
  refine ⟨256048276261967487113246099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170698850841311658075497399 256048276261967487113246099)
  ·
    refine ⟨384072414392951230669869149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256048276261967487113246099 384072414392951230669869149)
    ·
      refine ⟨144027155397356711501200931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384072414392951230669869149 144027155397356711501200931)
      ·
        refine ⟨216040733096035067251801397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144027155397356711501200931 216040733096035067251801397)
        ·
          refine ⟨20253818727753287554856381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216040733096035067251801397 20253818727753287554856381)
          ·
            refine ⟨7595182022907482833071143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20253818727753287554856381 7595182022907482833071143)
            ·
              refine ⟨11392773034361224249606715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595182022907482833071143 11392773034361224249606715)
              ·
                refine ⟨17089159551541836374410073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11392773034361224249606715 17089159551541836374410073)
                ·
                  refine ⟨12816869663656377280807555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17089159551541836374410073 12816869663656377280807555)
                  ·
                    refine ⟨19225304495484565921211333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12816869663656377280807555 19225304495484565921211333)
                    ·
                      refine ⟨3604744592903356110227125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19225304495484565921211333 3604744592903356110227125)
                      ·
                        rfl

theorem cell23_7020215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_7020215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020215 prefixEnd_7020215 := by exact prefixLift 7020215
  have htrace : WordTrace (prefixWord ++ tailWord_7020215) baseStart_7020215 baseEnd_7020215 := by
    simpa [prefixWord, tailWord_7020215, baseEnd_7020215] using wordTrace_append hprefix tailTrace_7020215
  have hstable : (prefixWord ++ tailWord_7020215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020215).length < 2 ^ (prefixWord ++ tailWord_7020215).sum := by decide
  have hdescent : baseEnd_7020215 < baseStart_7020215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020218 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3]
def baseStart_7020218 : Nat := 118140960795 + 7020218 * 2 ^ 59
def prefixEnd_7020218 : Nat := 4983230072969 + 3 ^ 40 * 7020218 * 2
def baseEnd_7020218 : Nat := 3604746133345319598489611

theorem tailTrace_7020218 : CollatzResearch.WordTrace tailWord_7020218 prefixEnd_7020218 3604746133345319598489611 := by
  unfold tailWord_7020218
  simp only [CollatzResearch.WordTrace]
  refine ⟨64012096420239154656401327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170698923787304412417070205 64012096420239154656401327)
  ·
    refine ⟨96018144630358731984601991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64012096420239154656401327 96018144630358731984601991)
    ·
      refine ⟨144027216945538097976902987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96018144630358731984601991 144027216945538097976902987)
      ·
        refine ⟨216040825418307146965354481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144027216945538097976902987 216040825418307146965354481)
        ·
          refine ⟨162030619063730360224015861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216040825418307146965354481 162030619063730360224015861)
          ·
            refine ⟨15190370537224721271001487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162030619063730360224015861 15190370537224721271001487)
            ·
              refine ⟨22785555805837081906502231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15190370537224721271001487 22785555805837081906502231)
              ·
                refine ⟨34178333708755622859753347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22785555805837081906502231 34178333708755622859753347)
                ·
                  refine ⟨51267500563133434289630021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34178333708755622859753347 51267500563133434289630021)
                  ·
                    refine ⟨9612656355587518929305629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51267500563133434289630021 9612656355587518929305629)
                    ·
                      refine ⟨3604746133345319598489611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9612656355587518929305629 3604746133345319598489611)
                      ·
                        rfl

theorem cell23_7020218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_7020218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020218 prefixEnd_7020218 := by exact prefixLift 7020218
  have htrace : WordTrace (prefixWord ++ tailWord_7020218) baseStart_7020218 baseEnd_7020218 := by
    simpa [prefixWord, tailWord_7020218, baseEnd_7020218] using wordTrace_append hprefix tailTrace_7020218
  have hstable : (prefixWord ++ tailWord_7020218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020218).length < 2 ^ (prefixWord ++ tailWord_7020218).sum := by decide
  have hdescent : baseEnd_7020218 < baseStart_7020218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020221 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 8]
def baseStart_7020221 : Nat := 118140960795 + 7020221 * 2 ^ 59
def prefixEnd_7020221 : Nat := 4983230072969 + 3 ^ 40 * 7020221 * 2
def baseEnd_7020221 : Nat := 400527519309698120750233

theorem tailTrace_7020221 : CollatzResearch.WordTrace tailWord_7020221 prefixEnd_7020221 400527519309698120750233 := by
  unfold tailWord_7020221
  simp only [CollatzResearch.WordTrace]
  refine ⟨256048495099945750137964517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170698996733297166758643011 256048495099945750137964517)
  ·
    refine ⟨48009092831239828150868347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256048495099945750137964517 48009092831239828150868347)
    ·
      refine ⟨72013639246859742226302521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48009092831239828150868347 72013639246859742226302521)
      ·
        refine ⟨54010229435144806669726891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72013639246859742226302521 54010229435144806669726891)
        ·
          refine ⟨81015344152717210004590337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54010229435144806669726891 81015344152717210004590337)
          ·
            refine ⟨60761508114537907503442753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81015344152717210004590337 60761508114537907503442753)
            ·
              refine ⟨45571131085903430627582065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60761508114537907503442753 45571131085903430627582065)
              ·
                refine ⟨34178348314427572970686549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45571131085903430627582065 34178348314427572970686549)
                ·
                  refine ⟨400527519309698120750233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34178348314427572970686549 400527519309698120750233)
                  ·
                    rfl

theorem cell23_7020221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_7020221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020221 prefixEnd_7020221 := by exact prefixLift 7020221
  have htrace : WordTrace (prefixWord ++ tailWord_7020221) baseStart_7020221 baseEnd_7020221 := by
    simpa [prefixWord, tailWord_7020221, baseEnd_7020221] using wordTrace_append hprefix tailTrace_7020221
  have hstable : (prefixWord ++ tailWord_7020221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020221).length < 2 ^ (prefixWord ++ tailWord_7020221).sum := by decide
  have hdescent : baseEnd_7020221 < baseStart_7020221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020241 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_7020241 : Nat := 118140960795 + 7020241 * 2 ^ 59
def prefixEnd_7020241 : Nat := 4983230072969 + 3 ^ 40 * 7020241 * 2
def baseEnd_7020241 : Nat := 3604757943400373008502005

theorem tailTrace_7020241 : CollatzResearch.WordTrace tailWord_7020241 prefixEnd_7020241 3604757943400373008502005 := by
  unfold tailWord_7020241
  simp only [CollatzResearch.WordTrace]
  refine ⟨256049224559873293553692577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170699483039915529035795051 256049224559873293553692577)
  ·
    refine ⟨192036918419904970165269433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256049224559873293553692577 192036918419904970165269433)
    ·
      refine ⟨144027688814928727623952075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192036918419904970165269433 144027688814928727623952075)
      ·
        refine ⟨216041533222393091435928113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144027688814928727623952075 216041533222393091435928113)
        ·
          refine ⟨162031149916794818576946085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216041533222393091435928113 162031149916794818576946085)
          ·
            refine ⟨30380840609399028483177391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162031149916794818576946085 30380840609399028483177391)
            ·
              refine ⟨45571260914098542724766087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30380840609399028483177391 45571260914098542724766087)
              ·
                refine ⟨68356891371147814087149131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45571260914098542724766087 68356891371147814087149131)
                ·
                  refine ⟨102535337056721721130723697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68356891371147814087149131 102535337056721721130723697)
                  ·
                    refine ⟨76901502792541290848042773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102535337056721721130723697 76901502792541290848042773)
                    ·
                      refine ⟨3604757943400373008502005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76901502792541290848042773 3604757943400373008502005)
                      ·
                        rfl

theorem cell23_7020241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_7020241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020241 prefixEnd_7020241 := by exact prefixLift 7020241
  have htrace : WordTrace (prefixWord ++ tailWord_7020241) baseStart_7020241 baseEnd_7020241 := by
    simpa [prefixWord, tailWord_7020241, baseEnd_7020241] using wordTrace_append hprefix tailTrace_7020241
  have hstable : (prefixWord ++ tailWord_7020241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020241).length < 2 ^ (prefixWord ++ tailWord_7020241).sum := by decide
  have hdescent : baseEnd_7020241 < baseStart_7020241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020242 : List Nat := [3, 2, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_7020242 : Nat := 118140960795 + 7020242 * 2 ^ 59
def prefixEnd_7020242 : Nat := 4983230072969 + 3 ^ 40 * 7020242 * 2
def baseEnd_7020242 : Nat := 1201586152293675834863167

theorem tailTrace_7020242 : CollatzResearch.WordTrace tailWord_7020242 prefixEnd_7020242 1201586152293675834863167 := by
  unfold tailWord_7020242
  simp only [CollatzResearch.WordTrace]
  refine ⟨64012315258217417681119745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170699507355246447149652653 64012315258217417681119745)
  ·
    refine ⟨48009236443663063260839809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64012315258217417681119745 48009236443663063260839809)
    ·
      refine ⟨36006927332747297445629857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48009236443663063260839809 36006927332747297445629857)
      ·
        refine ⟨27005195499560473084222393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36006927332747297445629857 27005195499560473084222393)
        ·
          refine ⟨20253896624670354813166795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27005195499560473084222393 20253896624670354813166795)
          ·
            refine ⟨30380844937005532219750193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20253896624670354813166795 30380844937005532219750193)
            ·
              refine ⟨22785633702754149164812645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30380844937005532219750193 22785633702754149164812645)
              ·
                refine ⟨4272306319266402968402371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22785633702754149164812645 4272306319266402968402371)
                ·
                  refine ⟨6408459478899604452603557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4272306319266402968402371 6408459478899604452603557)
                  ·
                    refine ⟨1201586152293675834863167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6408459478899604452603557 1201586152293675834863167)
                    ·
                      rfl

theorem cell23_7020242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_7020242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020242 prefixEnd_7020242 := by exact prefixLift 7020242
  have htrace : WordTrace (prefixWord ++ tailWord_7020242) baseStart_7020242 baseEnd_7020242 := by
    simpa [prefixWord, tailWord_7020242, baseEnd_7020242] using wordTrace_append hprefix tailTrace_7020242
  have hstable : (prefixWord ++ tailWord_7020242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020242).length < 2 ^ (prefixWord ++ tailWord_7020242).sum := by decide
  have hdescent : baseEnd_7020242 < baseStart_7020242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020268 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_7020268 : Nat := 118140960795 + 7020268 * 2 ^ 59
def prefixEnd_7020268 : Nat := 4983230072969 + 3 ^ 40 * 7020268 * 2
def baseEnd_7020268 : Nat := 1201590602459348134288127

theorem tailTrace_7020268 : CollatzResearch.WordTrace tailWord_7020268 prefixEnd_7020268 1201590602459348134288127 := by
  unfold tailWord_7020268
  simp only [CollatzResearch.WordTrace]
  refine ⟨128025104665387738582462729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170700139553850318109950305 128025104665387738582462729)
  ·
    refine ⟨96018828499040803936847047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128025104665387738582462729 96018828499040803936847047)
    ·
      refine ⟨144028242748561205905270571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96018828499040803936847047 144028242748561205905270571)
      ·
        refine ⟨216042364122841808857905857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144028242748561205905270571 216042364122841808857905857)
        ·
          refine ⟨162031773092131356643429393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216042364122841808857905857 162031773092131356643429393)
          ·
            refine ⟨121523829819098517482572045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162031773092131356643429393 121523829819098517482572045)
            ·
              refine ⟨45571436182161944055964517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121523829819098517482572045 45571436182161944055964517)
              ·
                refine ⟨8544644284155364510493347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45571436182161944055964517 8544644284155364510493347)
                ·
                  refine ⟨12816966426233046765740021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8544644284155364510493347 12816966426233046765740021)
                  ·
                    refine ⟨1201590602459348134288127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12816966426233046765740021 1201590602459348134288127)
                    ·
                      rfl

theorem cell23_7020268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_7020268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020268 prefixEnd_7020268 := by exact prefixLift 7020268
  have htrace : WordTrace (prefixWord ++ tailWord_7020268) baseStart_7020268 baseEnd_7020268 := by
    simpa [prefixWord, tailWord_7020268, baseEnd_7020268] using wordTrace_append hprefix tailTrace_7020268
  have hstable : (prefixWord ++ tailWord_7020268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020268).length < 2 ^ (prefixWord ++ tailWord_7020268).sum := by decide
  have hdescent : baseEnd_7020268 < baseStart_7020268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020276 : List Nat := [2, 6, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_7020276 : Nat := 118140960795 + 7020276 * 2 ^ 59
def prefixEnd_7020276 : Nat := 4983230072969 + 3 ^ 40 * 7020276 * 2
def baseEnd_7020276 : Nat := 1201591971741093457188115

theorem tailTrace_7020276 : CollatzResearch.WordTrace tailWord_7020276 prefixEnd_7020276 1201591971741093457188115 := by
  unfold tailWord_7020276
  simp only [CollatzResearch.WordTrace]
  refine ⟨128025250557373247265608341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170700334076497663020811121 128025250557373247265608341)
  ·
    refine ⟨6001183619876870965575391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128025250557373247265608341 6001183619876870965575391)
    ·
      refine ⟨9001775429815306448363087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001183619876870965575391 9001775429815306448363087)
      ·
        refine ⟨13502663144722959672544631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9001775429815306448363087 13502663144722959672544631)
        ·
          refine ⟨20253994717084439508816947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13502663144722959672544631 20253994717084439508816947)
          ·
            refine ⟨30380992075626659263225421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20253994717084439508816947 30380992075626659263225421)
            ·
              refine ⟨11392872028359997223709533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30380992075626659263225421 11392872028359997223709533)
              ·
                refine ⟨4272327010634998958891075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11392872028359997223709533 4272327010634998958891075)
                ·
                  refine ⟨6408490515952498438336613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4272327010634998958891075 6408490515952498438336613)
                  ·
                    refine ⟨1201591971741093457188115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6408490515952498438336613 1201591971741093457188115)
                    ·
                      rfl

theorem cell23_7020276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_7020276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020276 prefixEnd_7020276 := by exact prefixLift 7020276
  have htrace : WordTrace (prefixWord ++ tailWord_7020276) baseStart_7020276 baseEnd_7020276 := by
    simpa [prefixWord, tailWord_7020276, baseEnd_7020276] using wordTrace_append hprefix tailTrace_7020276
  have hstable : (prefixWord ++ tailWord_7020276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020276).length < 2 ^ (prefixWord ++ tailWord_7020276).sum := by decide
  have hdescent : baseEnd_7020276 < baseStart_7020276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020288 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 1, 8, 2]
def baseStart_7020288 : Nat := 118140960795 + 7020288 * 2 ^ 59
def prefixEnd_7020288 : Nat := 4983230072969 + 3 ^ 40 * 7020288 * 2
def baseEnd_7020288 : Nat := 3604782076991134324614289

theorem tailTrace_7020288 : CollatzResearch.WordTrace tailWord_7020288 prefixEnd_7020288 3604782076991134324614289 := by
  unfold tailWord_7020288
  simp only [CollatzResearch.WordTrace]
  refine ⟨128025469395351510290326759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170700625860468680387102345 128025469395351510290326759)
  ·
    refine ⟨192038204093027265435490139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128025469395351510290326759 192038204093027265435490139)
    ·
      refine ⟨288057306139540898153235209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192038204093027265435490139 288057306139540898153235209)
      ·
        refine ⟨216042979604655673614926407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288057306139540898153235209 216042979604655673614926407)
        ·
          refine ⟨324064469406983510422389611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216042979604655673614926407 324064469406983510422389611)
          ·
            refine ⟨486096704110475265633584417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324064469406983510422389611 486096704110475265633584417)
            ·
              refine ⟨364572528082856449225188313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486096704110475265633584417 364572528082856449225188313)
              ·
                refine ⟨273429396062142336918891235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364572528082856449225188313 273429396062142336918891235)
                ·
                  refine ⟨410144094093213505378336853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273429396062142336918891235 410144094093213505378336853)
                  ·
                    refine ⟨4806376102654845766152385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 410144094093213505378336853 4806376102654845766152385)
                    ·
                      refine ⟨3604782076991134324614289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4806376102654845766152385 3604782076991134324614289)
                      ·
                        rfl

theorem cell23_7020288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_7020288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020288 prefixEnd_7020288 := by exact prefixLift 7020288
  have htrace : WordTrace (prefixWord ++ tailWord_7020288) baseStart_7020288 baseEnd_7020288 := by
    simpa [prefixWord, tailWord_7020288, baseEnd_7020288] using wordTrace_append hprefix tailTrace_7020288
  have hstable : (prefixWord ++ tailWord_7020288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020288).length < 2 ^ (prefixWord ++ tailWord_7020288).sum := by decide
  have hdescent : baseEnd_7020288 < baseStart_7020288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020292 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_7020292 : Nat := 118140960795 + 7020292 * 2 ^ 59
def prefixEnd_7020292 : Nat := 4983230072969 + 3 ^ 40 * 7020292 * 2
def baseEnd_7020292 : Nat := 3604784130913752308964271

theorem tailTrace_7020292 : CollatzResearch.WordTrace tailWord_7020292 prefixEnd_7020292 3604784130913752308964271 := by
  unfold tailWord_7020292
  simp only [CollatzResearch.WordTrace]
  refine ⟨128025542341344264631899565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170700723121792352842532753 128025542341344264631899565)
  ·
    refine ⟨48009578378004099236962337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128025542341344264631899565 48009578378004099236962337)
    ·
      refine ⟨36007183783503074427721753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48009578378004099236962337 36007183783503074427721753)
      ·
        refine ⟨27005387837627305820791315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36007183783503074427721753 27005387837627305820791315)
        ·
          refine ⟨40508081756440958731186973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27005387837627305820791315 40508081756440958731186973)
          ·
            refine ⟨15190530658665359524195115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40508081756440958731186973 15190530658665359524195115)
            ·
              refine ⟨22785795987998039286292673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15190530658665359524195115 22785795987998039286292673)
              ·
                refine ⟨17089346990998529464719505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22785795987998039286292673 17089346990998529464719505)
                ·
                  refine ⟨12817010243248897098539629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17089346990998529464719505 12817010243248897098539629)
                  ·
                    refine ⟨4806378841218336411952361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12817010243248897098539629 4806378841218336411952361)
                    ·
                      refine ⟨3604784130913752308964271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4806378841218336411952361 3604784130913752308964271)
                      ·
                        rfl

theorem cell23_7020292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_7020292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020292 prefixEnd_7020292 := by exact prefixLift 7020292
  have htrace : WordTrace (prefixWord ++ tailWord_7020292) baseStart_7020292 baseEnd_7020292 := by
    simpa [prefixWord, tailWord_7020292, baseEnd_7020292] using wordTrace_append hprefix tailTrace_7020292
  have hstable : (prefixWord ++ tailWord_7020292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020292).length < 2 ^ (prefixWord ++ tailWord_7020292).sum := by decide
  have hdescent : baseEnd_7020292 < baseStart_7020292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020322 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_7020322 : Nat := 118140960795 + 7020322 * 2 ^ 59
def prefixEnd_7020322 : Nat := 4983230072969 + 3 ^ 40 * 7020322 * 2
def baseEnd_7020322 : Nat := 3604799535333387191589133

theorem tailTrace_7020322 : CollatzResearch.WordTrace tailWord_7020322 prefixEnd_7020322 3604799535333387191589133 := by
  unfold tailWord_7020322
  simp only [CollatzResearch.WordTrace]
  refine ⟨64013044718144961096847805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170701452581719896258260813 64013044718144961096847805)
  ·
    refine ⟨24004891769304360411317927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64013044718144961096847805 24004891769304360411317927)
    ·
      refine ⟨36007337653956540616976891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24004891769304360411317927 36007337653956540616976891)
      ·
        refine ⟨54011006480934810925465337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36007337653956540616976891 54011006480934810925465337)
        ·
          refine ⟨40508254860701108194099003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54011006480934810925465337 40508254860701108194099003)
          ·
            refine ⟨60762382291051662291148505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40508254860701108194099003 60762382291051662291148505)
            ·
              refine ⟨45571786718288746718361379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60762382291051662291148505 45571786718288746718361379)
              ·
                refine ⟨68357680077433120077542069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45571786718288746718361379 68357680077433120077542069)
                ·
                  refine ⟨6408532507259355007269569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68357680077433120077542069 6408532507259355007269569)
                  ·
                    refine ⟨4806399380444516255452177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6408532507259355007269569 4806399380444516255452177)
                    ·
                      refine ⟨3604799535333387191589133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4806399380444516255452177 3604799535333387191589133)
                      ·
                        rfl

theorem cell23_7020322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_7020322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020322 prefixEnd_7020322 := by exact prefixLift 7020322
  have htrace : WordTrace (prefixWord ++ tailWord_7020322) baseStart_7020322 baseEnd_7020322 := by
    simpa [prefixWord, tailWord_7020322, baseEnd_7020322] using wordTrace_append hprefix tailTrace_7020322
  have hstable : (prefixWord ++ tailWord_7020322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020322).length < 2 ^ (prefixWord ++ tailWord_7020322).sum := by decide
  have hdescent : baseEnd_7020322 < baseStart_7020322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020325 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 3, 2, 3]
def baseStart_7020325 : Nat := 118140960795 + 7020325 * 2 ^ 59
def prefixEnd_7020325 : Nat := 4983230072969 + 3 ^ 40 * 7020325 * 2
def baseEnd_7020325 : Nat := 3604801075775350679851619

theorem tailTrace_7020325 : CollatzResearch.WordTrace tailWord_7020325 prefixEnd_7020325 3604801075775350679851619 := by
  unfold tailWord_7020325
  simp only [CollatzResearch.WordTrace]
  refine ⟨256052288291568975899750429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170701525527712650599833619 256052288291568975899750429)
  ·
    refine ⟨96019608109338365962406411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256052288291568975899750429 96019608109338365962406411)
    ·
      refine ⟨144029412164007548943609617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96019608109338365962406411 144029412164007548943609617)
      ·
        refine ⟨108022059123005661707707213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144029412164007548943609617 108022059123005661707707213)
        ·
          refine ⟨40508272171127123140390205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108022059123005661707707213 40508272171127123140390205)
          ·
            refine ⟨15190602064172671177646327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40508272171127123140390205 15190602064172671177646327)
            ·
              refine ⟨22785903096259006766469491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15190602064172671177646327 22785903096259006766469491)
              ·
                refine ⟨34178854644388510149704237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22785903096259006766469491 34178854644388510149704237)
                ·
                  refine ⟨12817070491645691306139089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34178854644388510149704237 12817070491645691306139089)
                  ·
                    refine ⟨9612802868734268479604317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12817070491645691306139089 9612802868734268479604317)
                    ·
                      refine ⟨3604801075775350679851619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9612802868734268479604317 3604801075775350679851619)
                      ·
                        rfl

theorem cell23_7020325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_7020325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020325 prefixEnd_7020325 := by exact prefixLift 7020325
  have htrace : WordTrace (prefixWord ++ tailWord_7020325) baseStart_7020325 baseEnd_7020325 := by
    simpa [prefixWord, tailWord_7020325, baseEnd_7020325] using wordTrace_append hprefix tailTrace_7020325
  have hstable : (prefixWord ++ tailWord_7020325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020325).length < 2 ^ (prefixWord ++ tailWord_7020325).sum := by decide
  have hdescent : baseEnd_7020325 < baseStart_7020325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020328 : List Nat := [2, 1, 5, 1, 1, 2, 2, 9]
def baseStart_7020328 : Nat := 118140960795 + 7020328 * 2 ^ 59
def prefixEnd_7020328 : Nat := 4983230072969 + 3 ^ 40 * 7020328 * 2
def baseEnd_7020328 : Nat := 133511208008048672893115

theorem tailTrace_7020328 : CollatzResearch.WordTrace tailWord_7020328 prefixEnd_7020328 133511208008048672893115 := by
  unfold tailWord_7020328
  simp only [CollatzResearch.WordTrace]
  refine ⟨128026198855279053706054819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170701598473705404941406425 128026198855279053706054819)
  ·
    refine ⟨192039298282918580559082229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128026198855279053706054819 192039298282918580559082229)
    ·
      refine ⟨18003684214023616927413959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192039298282918580559082229 18003684214023616927413959)
      ·
        refine ⟨27005526321035425391120939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18003684214023616927413959 27005526321035425391120939)
        ·
          refine ⟨40508289481553138086681409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27005526321035425391120939 40508289481553138086681409)
          ·
            refine ⟨30381217111164853565011057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40508289481553138086681409 30381217111164853565011057)
            ·
              refine ⟨22785912833373640173758293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30381217111164853565011057 22785912833373640173758293)
              ·
                refine ⟨133511208008048672893115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22785912833373640173758293 133511208008048672893115)
                ·
                  rfl

theorem cell23_7020328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 9].length) (baseStart_7020328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020328 prefixEnd_7020328 := by exact prefixLift 7020328
  have htrace : WordTrace (prefixWord ++ tailWord_7020328) baseStart_7020328 baseEnd_7020328 := by
    simpa [prefixWord, tailWord_7020328, baseEnd_7020328] using wordTrace_append hprefix tailTrace_7020328
  have hstable : (prefixWord ++ tailWord_7020328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020328).length < 2 ^ (prefixWord ++ tailWord_7020328).sum := by decide
  have hdescent : baseEnd_7020328 < baseStart_7020328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020331 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 6]
def baseStart_7020331 : Nat := 118140960795 + 7020331 * 2 ^ 59
def prefixEnd_7020331 : Nat := 4983230072969 + 3 ^ 40 * 7020331 * 2
def baseEnd_7020331 : Nat := 3604804156659277656376591

theorem tailTrace_7020331 : CollatzResearch.WordTrace tailWord_7020331 prefixEnd_7020331 3604804156659277656376591 := by
  unfold tailWord_7020331
  simp only [CollatzResearch.WordTrace]
  refine ⟨256052507129547238924468847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170701671419698159282979231 256052507129547238924468847)
  ·
    refine ⟨384078760694320858386703271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256052507129547238924468847 384078760694320858386703271)
    ·
      refine ⟨576118141041481287580054907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384078760694320858386703271 576118141041481287580054907)
      ·
        refine ⟨864177211562221931370082361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576118141041481287580054907 864177211562221931370082361)
        ·
          refine ⟨648132908671666448527561771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864177211562221931370082361 648132908671666448527561771)
          ·
            refine ⟨972199363007499672791342657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648132908671666448527561771 972199363007499672791342657)
            ·
              refine ⟨729149522255624754593506993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972199363007499672791342657 729149522255624754593506993)
              ·
                refine ⟨546862141691718565945130245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729149522255624754593506993 546862141691718565945130245)
                ·
                  refine ⟨102536651567197231114711921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 546862141691718565945130245 102536651567197231114711921)
                  ·
                    refine ⟨76902488675397923336033941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102536651567197231114711921 76902488675397923336033941)
                    ·
                      refine ⟨3604804156659277656376591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76902488675397923336033941 3604804156659277656376591)
                      ·
                        rfl

theorem cell23_7020331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_7020331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020331 prefixEnd_7020331 := by exact prefixLift 7020331
  have htrace : WordTrace (prefixWord ++ tailWord_7020331) baseStart_7020331 baseEnd_7020331 := by
    simpa [prefixWord, tailWord_7020331, baseEnd_7020331] using wordTrace_append hprefix tailTrace_7020331
  have hstable : (prefixWord ++ tailWord_7020331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020331).length < 2 ^ (prefixWord ++ tailWord_7020331).sum := by decide
  have hdescent : baseEnd_7020331 < baseStart_7020331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020342 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_7020342 : Nat := 118140960795 + 7020342 * 2 ^ 59
def prefixEnd_7020342 : Nat := 4983230072969 + 3 ^ 40 * 7020342 * 2
def baseEnd_7020342 : Nat := 3604809804946477113339041

theorem tailTrace_7020342 : CollatzResearch.WordTrace tailWord_7020342 prefixEnd_7020342 3604809804946477113339041 := by
  unfold tailWord_7020342
  simp only [CollatzResearch.WordTrace]
  refine ⟨16003306770781711737694955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170701938888338258535412853 16003306770781711737694955)
  ·
    refine ⟨24004960156172567606542433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16003306770781711737694955 24004960156172567606542433)
    ·
      refine ⟨18003720117129425704906825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24004960156172567606542433 18003720117129425704906825)
      ·
        refine ⟨13502790087847069278680119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18003720117129425704906825 13502790087847069278680119)
        ·
          refine ⟨20254185131770603918020179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13502790087847069278680119 20254185131770603918020179)
          ·
            refine ⟨30381277697655905877030269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20254185131770603918020179 30381277697655905877030269)
            ·
              refine ⟨11392979136620964703886351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30381277697655905877030269 11392979136620964703886351)
              ·
                refine ⟨17089468704931447055829527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11392979136620964703886351 17089468704931447055829527)
                ·
                  refine ⟨25634203057397170583744291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17089468704931447055829527 25634203057397170583744291)
                  ·
                    refine ⟨38451304586095755875616437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25634203057397170583744291 38451304586095755875616437)
                    ·
                      refine ⟨3604809804946477113339041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38451304586095755875616437 3604809804946477113339041)
                      ·
                        rfl

theorem cell23_7020342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_7020342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020342 prefixEnd_7020342 := by exact prefixLift 7020342
  have htrace : WordTrace (prefixWord ++ tailWord_7020342) baseStart_7020342 baseEnd_7020342 := by
    simpa [prefixWord, tailWord_7020342, baseEnd_7020342] using wordTrace_append hprefix tailTrace_7020342
  have hstable : (prefixWord ++ tailWord_7020342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020342).length < 2 ^ (prefixWord ++ tailWord_7020342).sum := by decide
  have hdescent : baseEnd_7020342 < baseStart_7020342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020345 : List Nat := [1, 2, 1, 7, 2, 10]
def baseStart_7020345 : Nat := 118140960795 + 7020345 * 2 ^ 59
def prefixEnd_7020345 : Nat := 4983230072969 + 3 ^ 40 * 7020345 * 2
def baseEnd_7020345 : Nat := 14834614590075887249389

theorem tailTrace_7020345 : CollatzResearch.WordTrace tailWord_7020345 prefixEnd_7020345 14834614590075887249389 := by
  unfold tailWord_7020345
  simp only [CollatzResearch.WordTrace]
  refine ⟨256053017751496519315478489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170702011834331012876985659 256053017751496519315478489)
  ·
    refine ⟨192039763313622389486608867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256053017751496519315478489 192039763313622389486608867)
    ·
      refine ⟨288059644970433584229913301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192039763313622389486608867 288059644970433584229913301)
      ·
        refine ⟨6751397928994537130388593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 288059644970433584229913301 6751397928994537130388593)
        ·
          refine ⟨5063548446745902847791445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6751397928994537130388593 5063548446745902847791445)
          ·
            refine ⟨14834614590075887249389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5063548446745902847791445 14834614590075887249389)
            ·
              rfl

theorem cell23_7020345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 10].length) (baseStart_7020345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020345 prefixEnd_7020345 := by exact prefixLift 7020345
  have htrace : WordTrace (prefixWord ++ tailWord_7020345) baseStart_7020345 baseEnd_7020345 := by
    simpa [prefixWord, tailWord_7020345, baseEnd_7020345] using wordTrace_append hprefix tailTrace_7020345
  have hstable : (prefixWord ++ tailWord_7020345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020345).length < 2 ^ (prefixWord ++ tailWord_7020345).sum := by decide
  have hdescent : baseEnd_7020345 < baseStart_7020345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020372 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_7020372 : Nat := 118140960795 + 7020372 * 2 ^ 59
def prefixEnd_7020372 : Nat := 4983230072969 + 3 ^ 40 * 7020372 * 2
def baseEnd_7020372 : Nat := 3604825209366111995963903

theorem tailTrace_7020372 : CollatzResearch.WordTrace tailWord_7020372 prefixEnd_7020372 3604825209366111995963903 := by
  unfold tailWord_7020372
  simp only [CollatzResearch.WordTrace]
  refine ⟨128027001261199351463355685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170702668348265801951140913 128027001261199351463355685)
  ·
    refine ⟨24005062736474878399379191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128027001261199351463355685 24005062736474878399379191)
    ·
      refine ⟨36007594104712317599068787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24005062736474878399379191 36007594104712317599068787)
      ·
        refine ⟨54011391157068476398603181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36007594104712317599068787 54011391157068476398603181)
        ·
          refine ⟨20254271683900678649476193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54011391157068476398603181 20254271683900678649476193)
          ·
            refine ⟨15190703762925508987107145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20254271683900678649476193 15190703762925508987107145)
            ·
              refine ⟨11393027822194131740330359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15190703762925508987107145 11393027822194131740330359)
              ·
                refine ⟨17089541733291197610495539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11393027822194131740330359 17089541733291197610495539)
                ·
                  refine ⟨25634312599936796415743309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17089541733291197610495539 25634312599936796415743309)
                  ·
                    refine ⟨9612867224976298655903741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25634312599936796415743309 9612867224976298655903741)
                    ·
                      refine ⟨3604825209366111995963903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9612867224976298655903741 3604825209366111995963903)
                      ·
                        rfl

theorem cell23_7020372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_7020372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020372 prefixEnd_7020372 := by exact prefixLift 7020372
  have htrace : WordTrace (prefixWord ++ tailWord_7020372) baseStart_7020372 baseEnd_7020372 := by
    simpa [prefixWord, tailWord_7020372, baseEnd_7020372] using wordTrace_append hprefix tailTrace_7020372
  have hstable : (prefixWord ++ tailWord_7020372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020372).length < 2 ^ (prefixWord ++ tailWord_7020372).sum := by decide
  have hdescent : baseEnd_7020372 < baseStart_7020372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020378 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_7020378 : Nat := 118140960795 + 7020378 * 2 ^ 59
def prefixEnd_7020378 : Nat := 4983230072969 + 3 ^ 40 * 7020378 * 2
def baseEnd_7020378 : Nat := 3604828290250038972488875

theorem tailTrace_7020378 : CollatzResearch.WordTrace tailWord_7020378 prefixEnd_7020378 3604828290250038972488875 := by
  unfold tailWord_7020378
  simp only [CollatzResearch.WordTrace]
  refine ⟨64013555340094241487857447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170702814240251310634286525 64013555340094241487857447)
  ·
    refine ⟨96020333010141362231786171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64013555340094241487857447 96020333010141362231786171)
    ·
      refine ⟨144030499515212043347679257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96020333010141362231786171 144030499515212043347679257)
      ·
        refine ⟨108022874636409032510759443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144030499515212043347679257 108022874636409032510759443)
        ·
          refine ⟨162034311954613548766139165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108022874636409032510759443 162034311954613548766139165)
          ·
            refine ⟨60762866982980080787302187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162034311954613548766139165 60762866982980080787302187)
            ·
              refine ⟨91144300474470121180953281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60762866982980080787302187 91144300474470121180953281)
              ·
                refine ⟨68358225355852590885714961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91144300474470121180953281 68358225355852590885714961)
                ·
                  refine ⟨51268669016889443164286221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68358225355852590885714961 51268669016889443164286221)
                  ·
                    refine ⟨19225750881333541186607333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51268669016889443164286221 19225750881333541186607333)
                    ·
                      refine ⟨3604828290250038972488875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19225750881333541186607333 3604828290250038972488875)
                      ·
                        rfl

theorem cell23_7020378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_7020378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020378 prefixEnd_7020378 := by exact prefixLift 7020378
  have htrace : WordTrace (prefixWord ++ tailWord_7020378) baseStart_7020378 baseEnd_7020378 := by
    simpa [prefixWord, tailWord_7020378, baseEnd_7020378] using wordTrace_append hprefix tailTrace_7020378
  have hstable : (prefixWord ++ tailWord_7020378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020378).length < 2 ^ (prefixWord ++ tailWord_7020378).sum := by decide
  have hdescent : baseEnd_7020378 < baseStart_7020378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020452 : List Nat := [2, 3, 1, 2, 1, 3, 3, 3, 5]
def baseStart_7020452 : Nat := 118140960795 + 7020452 * 2 ^ 59
def prefixEnd_7020452 : Nat := 4983230072969 + 3 ^ 40 * 7020452 * 2
def baseEnd_7020452 : Nat := 400540698646496853662615

theorem tailTrace_7020452 : CollatzResearch.WordTrace tailWord_7020452 prefixEnd_7020452 400540698646496853662615 := by
  unfold tailWord_7020452
  simp only [CollatzResearch.WordTrace]
  refine ⟨128028460181054438294811805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170704613574739251059749073 128028460181054438294811805)
  ·
    refine ⟨48010672567895414360554427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128028460181054438294811805 48010672567895414360554427)
    ·
      refine ⟨72016008851843121540831641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48010672567895414360554427 72016008851843121540831641)
      ·
        refine ⟨54012006638882341155623731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72016008851843121540831641 54012006638882341155623731)
        ·
          refine ⟨81018009958323511733435597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54012006638882341155623731 81018009958323511733435597)
          ·
            refine ⟨30381753734371316900038349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81018009958323511733435597 30381753734371316900038349)
            ·
              refine ⟨11393157650389243837514381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30381753734371316900038349 11393157650389243837514381)
              ·
                refine ⟨4272434118895966439067893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11393157650389243837514381 4272434118895966439067893)
                ·
                  refine ⟨400540698646496853662615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4272434118895966439067893 400540698646496853662615)
                  ·
                    rfl

theorem cell23_7020452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_7020452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020452 prefixEnd_7020452 := by exact prefixLift 7020452
  have htrace : WordTrace (prefixWord ++ tailWord_7020452) baseStart_7020452 baseEnd_7020452 := by
    simpa [prefixWord, tailWord_7020452, baseEnd_7020452] using wordTrace_append hprefix tailTrace_7020452
  have hstable : (prefixWord ++ tailWord_7020452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020452).length < 2 ^ (prefixWord ++ tailWord_7020452).sum := by decide
  have hdescent : baseEnd_7020452 < baseStart_7020452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020465 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 4, 5]
def baseStart_7020465 : Nat := 118140960795 + 7020465 * 2 ^ 59
def prefixEnd_7020465 : Nat := 4983230072969 + 3 ^ 40 * 7020465 * 2
def baseEnd_7020465 : Nat := 1201624321022326710700325

theorem tailTrace_7020465 : CollatzResearch.WordTrace tailWord_7020465 prefixEnd_7020465 1201624321022326710700325 := by
  unfold tailWord_7020465
  simp only [CollatzResearch.WordTrace]
  refine ⟨256057394511061779809846849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170704929674041186539897899 256057394511061779809846849)
  ·
    refine ⟨192043045883296334857385137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256057394511061779809846849 192043045883296334857385137)
    ·
      refine ⟨144032284412472251143038853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192043045883296334857385137 144032284412472251143038853)
      ·
        refine ⟨27006053327338547089319785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144032284412472251143038853 27006053327338547089319785)
        ·
          refine ⟨20254539995503910316989839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27006053327338547089319785 20254539995503910316989839)
          ·
            refine ⟨30381809993255865475484759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20254539995503910316989839 30381809993255865475484759)
            ·
              refine ⟨45572714989883798213227139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30381809993255865475484759 45572714989883798213227139)
              ·
                refine ⟨68359072484825697319840709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45572714989883798213227139 68359072484825697319840709)
                ·
                  refine ⟨12817326090904818247470133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68359072484825697319840709 12817326090904818247470133)
                  ·
                    refine ⟨1201624321022326710700325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12817326090904818247470133 1201624321022326710700325)
                    ·
                      rfl

theorem cell23_7020465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_7020465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020465 prefixEnd_7020465 := by exact prefixLift 7020465
  have htrace : WordTrace (prefixWord ++ tailWord_7020465) baseStart_7020465 baseEnd_7020465 := by
    simpa [prefixWord, tailWord_7020465, baseEnd_7020465] using wordTrace_append hprefix tailTrace_7020465
  have hstable : (prefixWord ++ tailWord_7020465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020465).length < 2 ^ (prefixWord ++ tailWord_7020465).sum := by decide
  have hdescent : baseEnd_7020465 < baseStart_7020465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020469 : List Nat := [1, 3, 3, 2, 1, 3, 3, 2, 5]
def baseStart_7020469 : Nat := 118140960795 + 7020469 * 2 ^ 59
def prefixEnd_7020469 : Nat := 4983230072969 + 3 ^ 40 * 7020469 * 2
def baseEnd_7020469 : Nat := 400541668554399790716773

theorem tailTrace_7020469 : CollatzResearch.WordTrace tailWord_7020469 prefixEnd_7020469 400541668554399790716773 := by
  unfold tailWord_7020469
  simp only [CollatzResearch.WordTrace]
  refine ⟨256057540403047288492992461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170705026935364858995328307 256057540403047288492992461)
  ·
    refine ⟨96021577651142733184872173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256057540403047288492992461 96021577651142733184872173)
    ·
      refine ⟨36008091619178524944327065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96021577651142733184872173 36008091619178524944327065)
      ·
        refine ⟨27006068714383893708245299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36008091619178524944327065 27006068714383893708245299)
        ·
          refine ⟨40509103071575840562367949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27006068714383893708245299 40509103071575840562367949)
          ·
            refine ⟨15190913651840940210887981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40509103071575840562367949 15190913651840940210887981)
            ·
              refine ⟨5696592619440352579082993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15190913651840940210887981 5696592619440352579082993)
              ·
                refine ⟨4272444464580264434312245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5696592619440352579082993 4272444464580264434312245)
                ·
                  refine ⟨400541668554399790716773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4272444464580264434312245 400541668554399790716773)
                  ·
                    rfl

theorem cell23_7020469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_7020469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020469 prefixEnd_7020469 := by exact prefixLift 7020469
  have htrace : WordTrace (prefixWord ++ tailWord_7020469) baseStart_7020469 baseEnd_7020469 := by
    simpa [prefixWord, tailWord_7020469, baseEnd_7020469] using wordTrace_append hprefix tailTrace_7020469
  have hstable : (prefixWord ++ tailWord_7020469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020469).length < 2 ^ (prefixWord ++ tailWord_7020469).sum := by decide
  have hdescent : baseEnd_7020469 < baseStart_7020469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020495 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 5, 4]
def baseStart_7020495 : Nat := 118140960795 + 7020495 * 2 ^ 59
def prefixEnd_7020495 : Nat := 4983230072969 + 3 ^ 40 * 7020495 * 2
def baseEnd_7020495 : Nat := 1201629455828871671575279

theorem tailTrace_7020495 : CollatzResearch.WordTrace tailWord_7020495 prefixEnd_7020495 1201629455828871671575279 := by
  unfold tailWord_7020495
  simp only [CollatzResearch.WordTrace]
  refine ⟨256058488700953094933438939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170705659133968729955625959 256058488700953094933438939)
  ·
    refine ⟨384087733051429642400158409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256058488700953094933438939 384087733051429642400158409)
    ·
      refine ⟨288065799788572231800118807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384087733051429642400158409 288065799788572231800118807)
      ·
        refine ⟨432098699682858347700178211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288065799788572231800118807 432098699682858347700178211)
        ·
          refine ⟨648148049524287521550267317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432098699682858347700178211 648148049524287521550267317)
          ·
            refine ⟨60763879642901955145337561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 648148049524287521550267317 60763879642901955145337561)
            ·
              refine ⟨45572909732176466359003171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60763879642901955145337561 45572909732176466359003171)
              ·
                refine ⟨68359364598264699538504757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45572909732176466359003171 68359364598264699538504757)
                ·
                  refine ⟨6408690431087315581734821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68359364598264699538504757 6408690431087315581734821)
                  ·
                    refine ⟨1201629455828871671575279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6408690431087315581734821 1201629455828871671575279)
                    ·
                      rfl

theorem cell23_7020495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 4].length) (baseStart_7020495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020495 prefixEnd_7020495 := by exact prefixLift 7020495
  have htrace : WordTrace (prefixWord ++ tailWord_7020495) baseStart_7020495 baseEnd_7020495 := by
    simpa [prefixWord, tailWord_7020495, baseEnd_7020495] using wordTrace_append hprefix tailTrace_7020495
  have hstable : (prefixWord ++ tailWord_7020495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020495).length < 2 ^ (prefixWord ++ tailWord_7020495).sum := by decide
  have hdescent : baseEnd_7020495 < baseStart_7020495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020522 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_7020522 : Nat := 118140960795 + 7020522 * 2 ^ 59
def prefixEnd_7020522 : Nat := 4983230072969 + 3 ^ 40 * 7020522 * 2
def baseEnd_7020522 : Nat := 3604902231464286409088213

theorem tailTrace_7020522 : CollatzResearch.WordTrace tailWord_7020522 prefixEnd_7020522 3604902231464286409088213 := by
  unfold tailWord_7020522
  simp only [CollatzResearch.WordTrace]
  refine ⟨64014868367963819636167955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170706315647903519029781213 64014868367963819636167955)
  ·
    refine ⟨96022302551945729454251933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64014868367963819636167955 96022302551945729454251933)
    ·
      refine ⟨36008363456979648545344475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96022302551945729454251933 36008363456979648545344475)
      ·
        refine ⟨54012545185469472818016713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36008363456979648545344475 54012545185469472818016713)
        ·
          refine ⟨40509408889102104613512535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54012545185469472818016713 40509408889102104613512535)
          ·
            refine ⟨60764113333653156920268803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40509408889102104613512535 60764113333653156920268803)
            ·
              refine ⟨91146170000479735380403205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60764113333653156920268803 91146170000479735380403205)
              ·
                refine ⟨17089906875089950383825601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91146170000479735380403205 17089906875089950383825601)
                ·
                  refine ⟨12817430156317462787869201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17089906875089950383825601 12817430156317462787869201)
                  ·
                    refine ⟨9613072617238097090901901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12817430156317462787869201 9613072617238097090901901)
                    ·
                      refine ⟨3604902231464286409088213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9613072617238097090901901 3604902231464286409088213)
                      ·
                        rfl

theorem cell23_7020522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_7020522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020522 prefixEnd_7020522 := by exact prefixLift 7020522
  have htrace : WordTrace (prefixWord ++ tailWord_7020522) baseStart_7020522 baseEnd_7020522 := by
    simpa [prefixWord, tailWord_7020522, baseEnd_7020522] using wordTrace_append hprefix tailTrace_7020522
  have hstable : (prefixWord ++ tailWord_7020522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020522).length < 2 ^ (prefixWord ++ tailWord_7020522).sum := by decide
  have hdescent : baseEnd_7020522 < baseStart_7020522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020550 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7020550 : Nat := 118140960795 + 7020550 * 2 ^ 59
def prefixEnd_7020550 : Nat := 4983230072969 + 3 ^ 40 * 7020550 * 2
def baseEnd_7020550 : Nat := 1201638869640870766512695

theorem tailTrace_7020550 : CollatzResearch.WordTrace tailWord_7020550 prefixEnd_7020550 1201638869640870766512695 := by
  unfold tailWord_7020550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8001890459867307478959097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170706996477169226217794069 8001890459867307478959097)
  ·
    refine ⟨6001417844900480609219323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8001890459867307478959097 6001417844900480609219323)
    ·
      refine ⟨9002126767350720913828985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001417844900480609219323 9002126767350720913828985)
      ·
        refine ⟨6751595075513040685371739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9002126767350720913828985 6751595075513040685371739)
        ·
          refine ⟨10127392613269561028057609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751595075513040685371739 10127392613269561028057609)
          ·
            refine ⟨7595544459952170771043207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10127392613269561028057609 7595544459952170771043207)
            ·
              refine ⟨11393316689928256156564811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595544459952170771043207 11393316689928256156564811)
              ·
                refine ⟨17089975034892384234847217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11393316689928256156564811 17089975034892384234847217)
                ·
                  refine ⟨12817481276169288176135413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17089975034892384234847217 12817481276169288176135413)
                  ·
                    refine ⟨1201638869640870766512695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12817481276169288176135413 1201638869640870766512695)
                    ·
                      rfl

theorem cell23_7020550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7020550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020550 prefixEnd_7020550 := by exact prefixLift 7020550
  have htrace : WordTrace (prefixWord ++ tailWord_7020550) baseStart_7020550 baseEnd_7020550 := by
    simpa [prefixWord, tailWord_7020550, baseEnd_7020550] using wordTrace_append hprefix tailTrace_7020550
  have hstable : (prefixWord ++ tailWord_7020550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020550).length < 2 ^ (prefixWord ++ tailWord_7020550).sum := by decide
  have hdescent : baseEnd_7020550 < baseStart_7020550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020555 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 3, 5]
def baseStart_7020555 : Nat := 118140960795 + 7020555 * 2 ^ 59
def prefixEnd_7020555 : Nat := 4983230072969 + 3 ^ 40 * 7020555 * 2
def baseEnd_7020555 : Nat := 1201639725441961593325187

theorem tailTrace_7020555 : CollatzResearch.WordTrace tailWord_7020555 prefixEnd_7020555 1201639725441961593325187 := by
  unfold tailWord_7020555
  simp only [CollatzResearch.WordTrace]
  refine ⟨256060677080735725180623119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170707118053823816787082079 256060677080735725180623119)
  ·
    refine ⟨384091015621103587770934679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256060677080735725180623119 384091015621103587770934679)
    ·
      refine ⟨576136523431655381656402019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384091015621103587770934679 576136523431655381656402019)
      ·
        refine ⟨864204785147483072484603029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576136523431655381656402019 864204785147483072484603029)
        ·
          refine ⟨40509599303788269022715767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 864204785147483072484603029 40509599303788269022715767)
          ·
            refine ⟨60764398955682403534073651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40509599303788269022715767 60764398955682403534073651)
            ·
              refine ⟨91146598433523605301110477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60764398955682403534073651 91146598433523605301110477)
              ·
                refine ⟨34179974412571351987916429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91146598433523605301110477 34179974412571351987916429)
                ·
                  refine ⟨12817490404714256995468661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34179974412571351987916429 12817490404714256995468661)
                  ·
                    refine ⟨1201639725441961593325187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12817490404714256995468661 1201639725441961593325187)
                    ·
                      rfl

theorem cell23_7020555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 5].length) (baseStart_7020555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020555 prefixEnd_7020555 := by exact prefixLift 7020555
  have htrace : WordTrace (prefixWord ++ tailWord_7020555) baseStart_7020555 baseEnd_7020555 := by
    simpa [prefixWord, tailWord_7020555, baseEnd_7020555] using wordTrace_append hprefix tailTrace_7020555
  have hstable : (prefixWord ++ tailWord_7020555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020555).length < 2 ^ (prefixWord ++ tailWord_7020555).sum := by decide
  have hdescent : baseEnd_7020555 < baseStart_7020555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020586 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_7020586 : Nat := 118140960795 + 7020586 * 2 ^ 59
def prefixEnd_7020586 : Nat := 4983230072969 + 3 ^ 40 * 7020586 * 2
def baseEnd_7020586 : Nat := 3604935094226174158687919

theorem tailTrace_7020586 : CollatzResearch.WordTrace tailWord_7020586 prefixEnd_7020586 3604935094226174158687919 := by
  unfold tailWord_7020586
  simp only [CollatzResearch.WordTrace]
  refine ⟨64015451935905854368750403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170707871829082278316667741 64015451935905854368750403)
  ·
    refine ⟨96023177903858781553125605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64015451935905854368750403 96023177903858781553125605)
    ·
      refine ⟨18004345856973521541211051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96023177903858781553125605 18004345856973521541211051)
      ·
        refine ⟨27006518785460282311816577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18004345856973521541211051 27006518785460282311816577)
        ·
          refine ⟨20254889089095211733862433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27006518785460282311816577 20254889089095211733862433)
          ·
            refine ⟨15191166816821408800396825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20254889089095211733862433 15191166816821408800396825)
            ·
              refine ⟨11393375112616056600297619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15191166816821408800396825 11393375112616056600297619)
              ·
                refine ⟨17090062668924084900446429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11393375112616056600297619 17090062668924084900446429)
                ·
                  refine ⟨6408773500846531837667411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17090062668924084900446429 6408773500846531837667411)
                  ·
                    refine ⟨9613160251269797756501117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6408773500846531837667411 9613160251269797756501117)
                    ·
                      refine ⟨3604935094226174158687919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9613160251269797756501117 3604935094226174158687919)
                      ·
                        rfl

theorem cell23_7020586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_7020586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020586 prefixEnd_7020586 := by exact prefixLift 7020586
  have htrace : WordTrace (prefixWord ++ tailWord_7020586) baseStart_7020586 baseEnd_7020586 := by
    simpa [prefixWord, tailWord_7020586, baseEnd_7020586] using wordTrace_append hprefix tailTrace_7020586
  have hstable : (prefixWord ++ tailWord_7020586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020586).length < 2 ^ (prefixWord ++ tailWord_7020586).sum := by decide
  have hdescent : baseEnd_7020586 < baseStart_7020586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020595 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 5]
def baseStart_7020595 : Nat := 118140960795 + 7020595 * 2 ^ 59
def prefixEnd_7020595 : Nat := 4983230072969 + 3 ^ 40 * 7020595 * 2
def baseEnd_7020595 : Nat := 3604939715552064623475377

theorem tailTrace_7020595 : CollatzResearch.WordTrace tailWord_7020595 prefixEnd_7020595 3604939715552064623475377 := by
  unfold tailWord_7020595
  simp only [CollatzResearch.WordTrace]
  refine ⟨256062136000590812012079239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170708090667060541341386159 256062136000590812012079239)
  ·
    refine ⟨384093204000886218018118859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256062136000590812012079239 384093204000886218018118859)
    ·
      refine ⟨576139806001329327027178289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384093204000886218018118859 576139806001329327027178289)
      ·
        refine ⟨432104854500996995270383717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576139806001329327027178289 432104854500996995270383717)
        ·
          refine ⟨81019660218936936613196947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432104854500996995270383717 81019660218936936613196947)
          ·
            refine ⟨121529490328405404919795421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81019660218936936613196947 121529490328405404919795421)
            ·
              refine ⟨45573558873152026844923283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121529490328405404919795421 45573558873152026844923283)
              ·
                refine ⟨68360338309728040267384925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45573558873152026844923283 68360338309728040267384925)
                ·
                  refine ⟨25635126866148015100269347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68360338309728040267384925 25635126866148015100269347)
                  ·
                    refine ⟨38452690299222022650404021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25635126866148015100269347 38452690299222022650404021)
                    ·
                      refine ⟨3604939715552064623475377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38452690299222022650404021 3604939715552064623475377)
                      ·
                        rfl

theorem cell23_7020595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_7020595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020595 prefixEnd_7020595 := by exact prefixLift 7020595
  have htrace : WordTrace (prefixWord ++ tailWord_7020595) baseStart_7020595 baseEnd_7020595 := by
    simpa [prefixWord, tailWord_7020595, baseEnd_7020595] using wordTrace_append hprefix tailTrace_7020595
  have hstable : (prefixWord ++ tailWord_7020595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020595).length < 2 ^ (prefixWord ++ tailWord_7020595).sum := by decide
  have hdescent : baseEnd_7020595 < baseStart_7020595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020606 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_7020606 : Nat := 118140960795 + 7020606 * 2 ^ 59
def prefixEnd_7020606 : Nat := 4983230072969 + 3 ^ 40 * 7020606 * 2
def baseEnd_7020606 : Nat := 1201648454613088026812609

theorem tailTrace_7020606 : CollatzResearch.WordTrace tailWord_7020606 prefixEnd_7020606 1201648454613088026812609 := by
  unfold tailWord_7020606
  simp only [CollatzResearch.WordTrace]
  refine ⟨32007817150443870111341209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170708358135700640593819781 32007817150443870111341209)
  ·
    refine ⟨24005862862832902583505907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32007817150443870111341209 24005862862832902583505907)
    ·
      refine ⟨36008794294249353875258861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24005862862832902583505907 36008794294249353875258861)
      ·
        refine ⟨13503297860343507703222073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36008794294249353875258861 13503297860343507703222073)
        ·
          refine ⟨10127473395257630777416555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13503297860343507703222073 10127473395257630777416555)
          ·
            refine ⟨15191210092886446166124833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10127473395257630777416555 15191210092886446166124833)
            ·
              refine ⟨11393407569664834624593625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15191210092886446166124833 11393407569664834624593625)
              ·
                refine ⟨8545055677248625968445219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11393407569664834624593625 8545055677248625968445219)
                ·
                  refine ⟨12817583515872938952667829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8545055677248625968445219 12817583515872938952667829)
                  ·
                    refine ⟨1201648454613088026812609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12817583515872938952667829 1201648454613088026812609)
                    ·
                      rfl

theorem cell23_7020606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_7020606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020606 prefixEnd_7020606 := by exact prefixLift 7020606
  have htrace : WordTrace (prefixWord ++ tailWord_7020606) baseStart_7020606 baseEnd_7020606 := by
    simpa [prefixWord, tailWord_7020606, baseEnd_7020606] using wordTrace_append hprefix tailTrace_7020606
  have hstable : (prefixWord ++ tailWord_7020606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020606).length < 2 ^ (prefixWord ++ tailWord_7020606).sum := by decide
  have hdescent : baseEnd_7020606 < baseStart_7020606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020609 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_7020609 : Nat := 118140960795 + 7020609 * 2 ^ 59
def prefixEnd_7020609 : Nat := 4983230072969 + 3 ^ 40 * 7020609 * 2
def baseEnd_7020609 : Nat := 3604946904281227568700313

theorem tailTrace_7020609 : CollatzResearch.WordTrace tailWord_7020609 prefixEnd_7020609 3604946904281227568700313 := by
  unfold tailWord_7020609
  simp only [CollatzResearch.WordTrace]
  refine ⟨256062646622540092403088881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170708431081693394935392587 256062646622540092403088881)
  ·
    refine ⟨192046984966905069302316661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256062646622540092403088881 192046984966905069302316661)
    ·
      refine ⟨18004404840647350247092187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192046984966905069302316661 18004404840647350247092187)
      ·
        refine ⟨27006607260971025370638281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18004404840647350247092187 27006607260971025370638281)
        ·
          refine ⟨20254955445728269027978711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27006607260971025370638281 20254955445728269027978711)
          ·
            refine ⟨30382433168592403541968067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20254955445728269027978711 30382433168592403541968067)
            ·
              refine ⟨45573649752888605312952101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30382433168592403541968067 45573649752888605312952101)
              ·
                refine ⟨8545059328666613496178519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45573649752888605312952101 8545059328666613496178519)
                ·
                  refine ⟨12817588992999920244267779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8545059328666613496178519 12817588992999920244267779)
                  ·
                    refine ⟨19226383489499880366401669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12817588992999920244267779 19226383489499880366401669)
                    ·
                      refine ⟨3604946904281227568700313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19226383489499880366401669 3604946904281227568700313)
                      ·
                        rfl

theorem cell23_7020609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_7020609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020609 prefixEnd_7020609 := by exact prefixLift 7020609
  have htrace : WordTrace (prefixWord ++ tailWord_7020609) baseStart_7020609 baseEnd_7020609 := by
    simpa [prefixWord, tailWord_7020609, baseEnd_7020609] using wordTrace_append hprefix tailTrace_7020609
  have hstable : (prefixWord ++ tailWord_7020609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020609).length < 2 ^ (prefixWord ++ tailWord_7020609).sum := by decide
  have hdescent : baseEnd_7020609 < baseStart_7020609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020615 : List Nat := [1, 1, 4, 1, 3, 1, 3, 9]
def baseStart_7020615 : Nat := 118140960795 + 7020615 * 2 ^ 59
def prefixEnd_7020615 : Nat := 4983230072969 + 3 ^ 40 * 7020615 * 2
def baseEnd_7020615 : Nat := 133516666117227946119455

theorem tailTrace_7020615 : CollatzResearch.WordTrace tailWord_7020615 prefixEnd_7020615 133516666117227946119455 := by
  unfold tailWord_7020615
  simp only [CollatzResearch.WordTrace]
  refine ⟨256062865460518355427807299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170708576973678903618538199 256062865460518355427807299)
  ·
    refine ⟨384094298190777533141710949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256062865460518355427807299 384094298190777533141710949)
    ·
      refine ⟨72017680910770787464070803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384094298190777533141710949 72017680910770787464070803)
      ·
        refine ⟨108026521366156181196106205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72017680910770787464070803 108026521366156181196106205)
        ·
          refine ⟨40509945512308567948539827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108026521366156181196106205 40509945512308567948539827)
          ·
            refine ⟨60764918268462851922809741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40509945512308567948539827 60764918268462851922809741)
            ·
              refine ⟨22786844350673569471053653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60764918268462851922809741 22786844350673569471053653)
              ·
                refine ⟨133516666117227946119455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22786844350673569471053653 133516666117227946119455)
                ·
                  rfl

theorem cell23_7020615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 9].length) (baseStart_7020615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020615 prefixEnd_7020615 := by exact prefixLift 7020615
  have htrace : WordTrace (prefixWord ++ tailWord_7020615) baseStart_7020615 baseEnd_7020615 := by
    simpa [prefixWord, tailWord_7020615, baseEnd_7020615] using wordTrace_append hprefix tailTrace_7020615
  have hstable : (prefixWord ++ tailWord_7020615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020615).length < 2 ^ (prefixWord ++ tailWord_7020615).sum := by decide
  have hdescent : baseEnd_7020615 < baseStart_7020615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020629 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_7020629 : Nat := 118140960795 + 7020629 * 2 ^ 59
def prefixEnd_7020629 : Nat := 4983230072969 + 3 ^ 40 * 7020629 * 2
def baseEnd_7020629 : Nat := 3604957173894317490450221

theorem tailTrace_7020629 : CollatzResearch.WordTrace tailWord_7020629 prefixEnd_7020629 3604957173894317490450221 := by
  unfold tailWord_7020629
  simp only [CollatzResearch.WordTrace]
  refine ⟨256063376082467635818816941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170708917388311757212544627 256063376082467635818816941)
  ·
    refine ⟨96023766030925363432056353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256063376082467635818816941 96023766030925363432056353)
    ·
      refine ⟨72017824523194022574042265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96023766030925363432056353 72017824523194022574042265)
      ·
        refine ⟨54013368392395516930531699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72017824523194022574042265 54013368392395516930531699)
        ·
          refine ⟨81020052588593275395797549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54013368392395516930531699 81020052588593275395797549)
          ·
            refine ⟨30382519720722478273424081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81020052588593275395797549 30382519720722478273424081)
            ·
              refine ⟨22786889790541858705068061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30382519720722478273424081 22786889790541858705068061)
              ·
                refine ⟨8545083671453197014400523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22786889790541858705068061 8545083671453197014400523)
                ·
                  refine ⟨12817625507179795521600785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8545083671453197014400523 12817625507179795521600785)
                  ·
                    refine ⟨9613219130384846641200589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12817625507179795521600785 9613219130384846641200589)
                    ·
                      refine ⟨3604957173894317490450221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9613219130384846641200589 3604957173894317490450221)
                      ·
                        rfl

theorem cell23_7020629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_7020629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020629 prefixEnd_7020629 := by exact prefixLift 7020629
  have htrace : WordTrace (prefixWord ++ tailWord_7020629) baseStart_7020629 baseEnd_7020629 := by
    simpa [prefixWord, tailWord_7020629, baseEnd_7020629] using wordTrace_append hprefix tailTrace_7020629
  have hstable : (prefixWord ++ tailWord_7020629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020629).length < 2 ^ (prefixWord ++ tailWord_7020629).sum := by decide
  have hdescent : baseEnd_7020629 < baseStart_7020629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020715 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 7]
def baseStart_7020715 : Nat := 118140960795 + 7020715 * 2 ^ 59
def prefixEnd_7020715 : Nat := 4983230072969 + 3 ^ 40 * 7020715 * 2
def baseEnd_7020715 : Nat := 3605001333230604153974825

theorem tailTrace_7020715 : CollatzResearch.WordTrace tailWord_7020715 prefixEnd_7020715 3605001333230604153974825 := by
  unfold tailWord_7020715
  simp only [CollatzResearch.WordTrace]
  refine ⟨256066512760156072506447599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170711008506770715004298399 256066512760156072506447599)
  ·
    refine ⟨384099769140234108759671399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256066512760156072506447599 384099769140234108759671399)
    ·
      refine ⟨576149653710351163139507099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384099769140234108759671399 576149653710351163139507099)
      ·
        refine ⟨864224480565526744709260649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576149653710351163139507099 864224480565526744709260649)
        ·
          refine ⟨648168360424145058531945487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864224480565526744709260649 648168360424145058531945487)
          ·
            refine ⟨972252540636217587797918231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648168360424145058531945487 972252540636217587797918231)
            ·
              refine ⟨1458378810954326381696877347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972252540636217587797918231 1458378810954326381696877347)
              ·
                refine ⟨2187568216431489572545316021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458378810954326381696877347 2187568216431489572545316021)
                ·
                  refine ⟨205084520290452147426123377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2187568216431489572545316021 205084520290452147426123377)
                  ·
                    refine ⟨153813390217839110569592533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205084520290452147426123377 153813390217839110569592533)
                    ·
                      refine ⟨3605001333230604153974825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153813390217839110569592533 3605001333230604153974825)
                      ·
                        rfl

theorem cell23_7020715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_7020715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020715 prefixEnd_7020715 := by exact prefixLift 7020715
  have htrace : WordTrace (prefixWord ++ tailWord_7020715) baseStart_7020715 baseEnd_7020715 := by
    simpa [prefixWord, tailWord_7020715, baseEnd_7020715] using wordTrace_append hprefix tailTrace_7020715
  have hstable : (prefixWord ++ tailWord_7020715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020715).length < 2 ^ (prefixWord ++ tailWord_7020715).sum := by decide
  have hdescent : baseEnd_7020715 < baseStart_7020715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020722 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 7]
def baseStart_7020722 : Nat := 118140960795 + 7020722 * 2 ^ 59
def prefixEnd_7020722 : Nat := 4983230072969 + 3 ^ 40 * 7020722 * 2
def baseEnd_7020722 : Nat := 400556103066131736287477

theorem tailTrace_7020722 : CollatzResearch.WordTrace tailWord_7020722 prefixEnd_7020722 400556103066131736287477 := by
  unfold tailWord_7020722
  simp only [CollatzResearch.WordTrace]
  refine ⟨64016692017782678175488105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170711178714087141801301613 64016692017782678175488105)
  ·
    refine ⟨48012519013337008631616079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64016692017782678175488105 48012519013337008631616079)
    ·
      refine ⟨72018778520005512947424119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48012519013337008631616079 72018778520005512947424119)
      ·
        refine ⟨108028167780008269421136179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72018778520005512947424119 108028167780008269421136179)
        ·
          refine ⟨162042251670012404131704269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108028167780008269421136179 162042251670012404131704269)
          ·
            refine ⟨60765844376254651549389101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162042251670012404131704269 60765844376254651549389101)
            ·
              refine ⟨22787191641095494331020913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60765844376254651549389101 22787191641095494331020913)
              ·
                refine ⟨17090393730821620748265685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22787191641095494331020913 17090393730821620748265685)
                ·
                  refine ⟨400556103066131736287477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17090393730821620748265685 400556103066131736287477)
                  ·
                    rfl

theorem cell23_7020722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_7020722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020722 prefixEnd_7020722 := by exact prefixLift 7020722
  have htrace : WordTrace (prefixWord ++ tailWord_7020722) baseStart_7020722 baseEnd_7020722 := by
    simpa [prefixWord, tailWord_7020722, baseEnd_7020722] using wordTrace_append hprefix tailTrace_7020722
  have hstable : (prefixWord ++ tailWord_7020722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020722).length < 2 ^ (prefixWord ++ tailWord_7020722).sum := by decide
  have hdescent : baseEnd_7020722 < baseStart_7020722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020737 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7020737 : Nat := 118140960795 + 7020737 * 2 ^ 59
def prefixEnd_7020737 : Nat := 4983230072969 + 3 ^ 40 * 7020737 * 2
def baseEnd_7020737 : Nat := 3605012629805003067899725

theorem tailTrace_7020737 : CollatzResearch.WordTrace tailWord_7020737 prefixEnd_7020737 3605012629805003067899725 := by
  unfold tailWord_7020737
  simp only [CollatzResearch.WordTrace]
  refine ⟨256067315166076370263748465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170711543444050913509165643 256067315166076370263748465)
  ·
    refine ⟨192050486374557277697811349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256067315166076370263748465 192050486374557277697811349)
    ·
      refine ⟨9002366548807372392084907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192050486374557277697811349 9002366548807372392084907)
      ·
        refine ⟨13503549823211058588127361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9002366548807372392084907 13503549823211058588127361)
        ·
          refine ⟨10127662367408293941095521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13503549823211058588127361 10127662367408293941095521)
          ·
            refine ⟨7595746775556220455821641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10127662367408293941095521 7595746775556220455821641)
            ·
              refine ⟨5696810081667165341866231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7595746775556220455821641 5696810081667165341866231)
              ·
                refine ⟨8545215122500748012799347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5696810081667165341866231 8545215122500748012799347)
                ·
                  refine ⟨12817822683751122019199021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8545215122500748012799347 12817822683751122019199021)
                  ·
                    refine ⟨4806683506406670757199633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12817822683751122019199021 4806683506406670757199633)
                    ·
                      refine ⟨3605012629805003067899725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4806683506406670757199633 3605012629805003067899725)
                      ·
                        rfl

theorem cell23_7020737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7020737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020737 prefixEnd_7020737 := by exact prefixLift 7020737
  have htrace : WordTrace (prefixWord ++ tailWord_7020737) baseStart_7020737 baseEnd_7020737 := by
    simpa [prefixWord, tailWord_7020737, baseEnd_7020737] using wordTrace_append hprefix tailTrace_7020737
  have hstable : (prefixWord ++ tailWord_7020737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020737).length < 2 ^ (prefixWord ++ tailWord_7020737).sum := by decide
  have hdescent : baseEnd_7020737 < baseStart_7020737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020750 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2]
def baseStart_7020750 : Nat := 118140960795 + 7020750 * 2 ^ 59
def prefixEnd_7020750 : Nat := 4983230072969 + 3 ^ 40 * 7020750 * 2
def baseEnd_7020750 : Nat := 3605019305053511517037165

theorem tailTrace_7020750 : CollatzResearch.WordTrace tailWord_7020750 prefixEnd_7020750 3605019305053511517037165 := by
  unfold tailWord_7020750
  simp only [CollatzResearch.WordTrace]
  refine ⟨32008473664378659185496463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170711859543352848989314469 32008473664378659185496463)
  ·
    refine ⟨48012710496567988778244695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32008473664378659185496463 48012710496567988778244695)
    ·
      refine ⟨72019065744851983167367043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48012710496567988778244695 72019065744851983167367043)
      ·
        refine ⟨108028598617277974751050565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72019065744851983167367043 108028598617277974751050565)
        ·
          refine ⟨20255362240739620265821981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108028598617277974751050565 20255362240739620265821981)
          ·
            refine ⟨7595760840277357599683243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20255362240739620265821981 7595760840277357599683243)
            ·
              refine ⟨11393641260416036399524865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595760840277357599683243 11393641260416036399524865)
              ·
                refine ⟨8545230945312027299643649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11393641260416036399524865 8545230945312027299643649)
                ·
                  refine ⟨6408923208984020474732737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8545230945312027299643649 6408923208984020474732737)
                  ·
                    refine ⟨4806692406738015356049553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6408923208984020474732737 4806692406738015356049553)
                    ·
                      refine ⟨3605019305053511517037165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4806692406738015356049553 3605019305053511517037165)
                      ·
                        rfl

theorem cell23_7020750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_7020750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020750 prefixEnd_7020750 := by exact prefixLift 7020750
  have htrace : WordTrace (prefixWord ++ tailWord_7020750) baseStart_7020750 baseEnd_7020750 := by
    simpa [prefixWord, tailWord_7020750, baseEnd_7020750] using wordTrace_append hprefix tailTrace_7020750
  have hstable : (prefixWord ++ tailWord_7020750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020750).length < 2 ^ (prefixWord ++ tailWord_7020750).sum := by decide
  have hdescent : baseEnd_7020750 < baseStart_7020750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020762 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_7020762 : Nat := 118140960795 + 7020762 * 2 ^ 59
def prefixEnd_7020762 : Nat := 4983230072969 + 3 ^ 40 * 7020762 * 2
def baseEnd_7020762 : Nat := 3605025466821365470087109

theorem tailTrace_7020762 : CollatzResearch.WordTrace tailWord_7020762 prefixEnd_7020762 3605025466821365470087109 := by
  unfold tailWord_7020762
  simp only [CollatzResearch.WordTrace]
  refine ⟨64017056747746449883352135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170712151327323866355605693 64017056747746449883352135)
  ·
    refine ⟨96025585121619674825028203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64017056747746449883352135 96025585121619674825028203)
    ·
      refine ⟨144038377682429512237542305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96025585121619674825028203 144038377682429512237542305)
      ·
        refine ⟨108028783261822134178156729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144038377682429512237542305 108028783261822134178156729)
        ·
          refine ⟨81021587446366600633617547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108028783261822134178156729 81021587446366600633617547)
          ·
            refine ⟨121532381169549900950426321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81021587446366600633617547 121532381169549900950426321)
            ·
              refine ⟨91149285877162425712819741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121532381169549900950426321 91149285877162425712819741)
              ·
                refine ⟨34180982203935909642307403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91149285877162425712819741 34180982203935909642307403)
                ·
                  refine ⟨51271473305903864463461105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34180982203935909642307403 51271473305903864463461105)
                  ·
                    refine ⟨38453604979427898347595829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51271473305903864463461105 38453604979427898347595829)
                    ·
                      refine ⟨3605025466821365470087109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38453604979427898347595829 3605025466821365470087109)
                      ·
                        rfl

theorem cell23_7020762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_7020762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020762 prefixEnd_7020762 := by exact prefixLift 7020762
  have htrace : WordTrace (prefixWord ++ tailWord_7020762) baseStart_7020762 baseEnd_7020762 := by
    simpa [prefixWord, tailWord_7020762, baseEnd_7020762] using wordTrace_append hprefix tailTrace_7020762
  have hstable : (prefixWord ++ tailWord_7020762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020762).length < 2 ^ (prefixWord ++ tailWord_7020762).sum := by decide
  have hdescent : baseEnd_7020762 < baseStart_7020762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020782 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_7020782 : Nat := 118140960795 + 7020782 * 2 ^ 59
def prefixEnd_7020782 : Nat := 4983230072969 + 3 ^ 40 * 7020782 * 2
def baseEnd_7020782 : Nat := 1201678578811485130612339

theorem tailTrace_7020782 : CollatzResearch.WordTrace tailWord_7020782 prefixEnd_7020782 1201678578811485130612339 := by
  unfold tailWord_7020782
  simp only [CollatzResearch.WordTrace]
  refine ⟨32008619556364167868642075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170712637633942228632757733 32008619556364167868642075)
  ·
    refine ⟨48012929334546251802963113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32008619556364167868642075 48012929334546251802963113)
    ·
      refine ⟨36009697000909688852222335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48012929334546251802963113 36009697000909688852222335)
      ·
        refine ⟨54014545501364533278333503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36009697000909688852222335 54014545501364533278333503)
        ·
          refine ⟨81021818252046799917500255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54014545501364533278333503 81021818252046799917500255)
          ·
            refine ⟨121532727378070199876250383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81021818252046799917500255 121532727378070199876250383)
            ·
              refine ⟨182299091067105299814375575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121532727378070199876250383 182299091067105299814375575)
              ·
                refine ⟨273448636600657949721563363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182299091067105299814375575 273448636600657949721563363)
                ·
                  refine ⟨410172954900986924582345045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273448636600657949721563363 410172954900986924582345045)
                  ·
                    refine ⟨1201678578811485130612339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 410172954900986924582345045 1201678578811485130612339)
                    ·
                      rfl

theorem cell23_7020782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_7020782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020782 prefixEnd_7020782 := by exact prefixLift 7020782
  have htrace : WordTrace (prefixWord ++ tailWord_7020782) baseStart_7020782 baseEnd_7020782 := by
    simpa [prefixWord, tailWord_7020782, baseEnd_7020782] using wordTrace_append hprefix tailTrace_7020782
  have hstable : (prefixWord ++ tailWord_7020782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020782).length < 2 ^ (prefixWord ++ tailWord_7020782).sum := by decide
  have hdescent : baseEnd_7020782 < baseStart_7020782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020809 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 4, 2, 3]
def baseStart_7020809 : Nat := 118140960795 + 7020809 * 2 ^ 59
def prefixEnd_7020809 : Nat := 4983230072969 + 3 ^ 40 * 7020809 * 2
def baseEnd_7020809 : Nat := 3605049600412126786199393

theorem tailTrace_7020809 : CollatzResearch.WordTrace tailWord_7020809 prefixEnd_7020809 3605049600412126786199393 := by
  unfold tailWord_7020809
  simp only [CollatzResearch.WordTrace]
  refine ⟨256069941221815526560369481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170713294147877017706912987 256069941221815526560369481)
  ·
    refine ⟨192052455916361644920277111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256069941221815526560369481 192052455916361644920277111)
    ·
      refine ⟨288078683874542467380415667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192052455916361644920277111 288078683874542467380415667)
      ·
        refine ⟨432118025811813701070623501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288078683874542467380415667 432118025811813701070623501)
        ·
          refine ⟨162044259679430137901483813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432118025811813701070623501 162044259679430137901483813)
          ·
            refine ⟨30383298689893150856528215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162044259679430137901483813 30383298689893150856528215)
            ·
              refine ⟨45574948034839726284792323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30383298689893150856528215 45574948034839726284792323)
              ·
                refine ⟨68362422052259589427188485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45574948034839726284792323 68362422052259589427188485)
                ·
                  refine ⟨12817954134798673017597841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68362422052259589427188485 12817954134798673017597841)
                  ·
                    refine ⟨9613465601099004763198381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12817954134798673017597841 9613465601099004763198381)
                    ·
                      refine ⟨3605049600412126786199393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9613465601099004763198381 3605049600412126786199393)
                      ·
                        rfl

theorem cell23_7020809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2, 3].length) (baseStart_7020809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020809 prefixEnd_7020809 := by exact prefixLift 7020809
  have htrace : WordTrace (prefixWord ++ tailWord_7020809) baseStart_7020809 baseEnd_7020809 := by
    simpa [prefixWord, tailWord_7020809, baseEnd_7020809] using wordTrace_append hprefix tailTrace_7020809
  have hstable : (prefixWord ++ tailWord_7020809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020809).length < 2 ^ (prefixWord ++ tailWord_7020809).sum := by decide
  have hdescent : baseEnd_7020809 < baseStart_7020809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020812 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 8]
def baseStart_7020812 : Nat := 118140960795 + 7020812 * 2 ^ 59
def prefixEnd_7020812 : Nat := 4983230072969 + 3 ^ 40 * 7020812 * 2
def baseEnd_7020812 : Nat := 400561237872676697162431

theorem tailTrace_7020812 : CollatzResearch.WordTrace tailWord_7020812 prefixEnd_7020812 400561237872676697162431 := by
  unfold tailWord_7020812
  simp only [CollatzResearch.WordTrace]
  refine ⟨128035025320402329036364345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170713367093869772048485793 128035025320402329036364345)
  ·
    refine ⟨96026268990301746777273259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128035025320402329036364345 96026268990301746777273259)
    ·
      refine ⟨144039403485452620165909889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96026268990301746777273259 144039403485452620165909889)
      ·
        refine ⟨108029552614089465124432417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144039403485452620165909889 108029552614089465124432417)
        ·
          refine ⟨81022164460567098843324313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108029552614089465124432417 81022164460567098843324313)
          ·
            refine ⟨60766623345425324132493235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81022164460567098843324313 60766623345425324132493235)
            ·
              refine ⟨91149935018137986198739853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60766623345425324132493235 91149935018137986198739853)
              ·
                refine ⟨34181225631801744824527445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91149935018137986198739853 34181225631801744824527445)
                ·
                  refine ⟨400561237872676697162431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34181225631801744824527445 400561237872676697162431)
                  ·
                    rfl

theorem cell23_7020812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_7020812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020812 prefixEnd_7020812 := by exact prefixLift 7020812
  have htrace : WordTrace (prefixWord ++ tailWord_7020812) baseStart_7020812 baseEnd_7020812 := by
    simpa [prefixWord, tailWord_7020812, baseEnd_7020812] using wordTrace_append hprefix tailTrace_7020812
  have hstable : (prefixWord ++ tailWord_7020812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020812).length < 2 ^ (prefixWord ++ tailWord_7020812).sum := by decide
  have hdescent : baseEnd_7020812 < baseStart_7020812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020889 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 6, 4]
def baseStart_7020889 : Nat := 118140960795 + 7020889 * 2 ^ 59
def prefixEnd_7020889 : Nat := 4983230072969 + 3 ^ 40 * 7020889 * 2
def baseEnd_7020889 : Nat := 1201696892954828824399675

theorem tailTrace_7020889 : CollatzResearch.WordTrace tailWord_7020889 prefixEnd_7020889 1201696892954828824399675 := by
  unfold tailWord_7020889
  simp only [CollatzResearch.WordTrace]
  refine ⟨256072859061525700223281721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170715239374350466815521147 256072859061525700223281721)
  ·
    refine ⟨192054644296144275167461291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256072859061525700223281721 192054644296144275167461291)
    ·
      refine ⟨288081966444216412751191937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192054644296144275167461291 288081966444216412751191937)
      ·
        refine ⟨216061474833162309563393953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288081966444216412751191937 216061474833162309563393953)
        ·
          refine ⟨162046106124871732172545465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216061474833162309563393953 162046106124871732172545465)
          ·
            refine ⟨121534579593653799129409099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162046106124871732172545465 121534579593653799129409099)
            ·
              refine ⟨182301869390480698694113649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121534579593653799129409099 182301869390480698694113649)
              ·
                refine ⟨136726402042860524020585237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182301869390480698694113649 136726402042860524020585237)
                ·
                  refine ⟨6409050095759087063464933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136726402042860524020585237 6409050095759087063464933)
                  ·
                    refine ⟨1201696892954828824399675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6409050095759087063464933 1201696892954828824399675)
                    ·
                      rfl

theorem cell23_7020889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 4].length) (baseStart_7020889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020889 prefixEnd_7020889 := by exact prefixLift 7020889
  have htrace : WordTrace (prefixWord ++ tailWord_7020889) baseStart_7020889 baseEnd_7020889 := by
    simpa [prefixWord, tailWord_7020889, baseEnd_7020889] using wordTrace_append hprefix tailTrace_7020889
  have hstable : (prefixWord ++ tailWord_7020889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020889).length < 2 ^ (prefixWord ++ tailWord_7020889).sum := by decide
  have hdescent : baseEnd_7020889 < baseStart_7020889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020906 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_7020906 : Nat := 118140960795 + 7020906 * 2 ^ 59
def prefixEnd_7020906 : Nat := 4983230072969 + 3 ^ 40 * 7020906 * 2
def baseEnd_7020906 : Nat := 1201699802678537635562149

theorem tailTrace_7020906 : CollatzResearch.WordTrace tailWord_7020906 prefixEnd_7020906 1201699802678537635562149 := by
  unfold tailWord_7020906
  simp only [CollatzResearch.WordTrace]
  refine ⟨64018369775616028031662643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170715652734976074751100381 64018369775616028031662643)
  ·
    refine ⟨96027554663424042047493965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64018369775616028031662643 96027554663424042047493965)
    ·
      refine ⟨36010332998784015767810237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96027554663424042047493965 36010332998784015767810237)
      ·
        refine ⟨13503874874544005912928839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36010332998784015767810237 13503874874544005912928839)
        ·
          refine ⟨20255812311816008869393259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13503874874544005912928839 20255812311816008869393259)
          ·
            refine ⟨30383718467724013304089889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20255812311816008869393259 30383718467724013304089889)
            ·
              refine ⟨22787788850793009978067417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30383718467724013304089889 22787788850793009978067417)
              ·
                refine ⟨17090841638094757483550563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22787788850793009978067417 17090841638094757483550563)
                ·
                  refine ⟨25636262457142136225325845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17090841638094757483550563 25636262457142136225325845)
                  ·
                    refine ⟨1201699802678537635562149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25636262457142136225325845 1201699802678537635562149)
                    ·
                      rfl

theorem cell23_7020906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_7020906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020906 prefixEnd_7020906 := by exact prefixLift 7020906
  have htrace : WordTrace (prefixWord ++ tailWord_7020906) baseStart_7020906 baseEnd_7020906 := by
    simpa [prefixWord, tailWord_7020906, baseEnd_7020906] using wordTrace_append hprefix tailTrace_7020906
  have hstable : (prefixWord ++ tailWord_7020906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020906).length < 2 ^ (prefixWord ++ tailWord_7020906).sum := by decide
  have hdescent : baseEnd_7020906 < baseStart_7020906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020923 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 2, 4]
def baseStart_7020923 : Nat := 118140960795 + 7020923 * 2 ^ 59
def prefixEnd_7020923 : Nat := 4983230072969 + 3 ^ 40 * 7020923 * 2
def baseEnd_7020923 : Nat := 1201702712402246446724623

theorem tailTrace_7020923 : CollatzResearch.WordTrace tailWord_7020923 prefixEnd_7020923 1201702712402246446724623 := by
  unfold tailWord_7020923
  simp only [CollatzResearch.WordTrace]
  refine ⟨256074099143402524030019423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170716066095601682686679615 256074099143402524030019423)
  ·
    refine ⟨384111148715103786045029135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256074099143402524030019423 384111148715103786045029135)
    ·
      refine ⟨576166723072655679067543703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384111148715103786045029135 576166723072655679067543703)
      ·
        refine ⟨864250084608983518601315555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576166723072655679067543703 864250084608983518601315555)
        ·
          refine ⟨1296375126913475277901973333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864250084608983518601315555 1296375126913475277901973333)
          ·
            refine ⟨7595948009258644206456875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1296375126913475277901973333 7595948009258644206456875)
            ·
              refine ⟨11393922013887966309685313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595948009258644206456875 11393922013887966309685313)
              ·
                refine ⟨8545441510415974732263985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11393922013887966309685313 8545441510415974732263985)
                ·
                  refine ⟨6409081132811981049197989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8545441510415974732263985 6409081132811981049197989)
                  ·
                    refine ⟨1201702712402246446724623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6409081132811981049197989 1201702712402246446724623)
                    ·
                      rfl

theorem cell23_7020923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 4].length) (baseStart_7020923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020923 prefixEnd_7020923 := by exact prefixLift 7020923
  have htrace : WordTrace (prefixWord ++ tailWord_7020923) baseStart_7020923 baseEnd_7020923 := by
    simpa [prefixWord, tailWord_7020923, baseEnd_7020923] using wordTrace_append hprefix tailTrace_7020923
  have hstable : (prefixWord ++ tailWord_7020923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020923).length < 2 ^ (prefixWord ++ tailWord_7020923).sum := by decide
  have hdescent : baseEnd_7020923 < baseStart_7020923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020959 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_7020959 : Nat := 118140960795 + 7020959 * 2 ^ 59
def prefixEnd_7020959 : Nat := 4983230072969 + 3 ^ 40 * 7020959 * 2
def baseEnd_7020959 : Nat := 3605126622510301199323703

theorem tailTrace_7020959 : CollatzResearch.WordTrace tailWord_7020959 prefixEnd_7020959 3605126622510301199323703 := by
  unfold tailWord_7020959
  simp only [CollatzResearch.WordTrace]
  refine ⟨256075412171272102178329931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170716941447514734785553287 256075412171272102178329931)
  ·
    refine ⟨384113118256908153267494897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256075412171272102178329931 384113118256908153267494897)
    ·
      refine ⟨288084838692681114950621173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384113118256908153267494897 288084838692681114950621173)
      ·
        refine ⟨27007953627438854526620735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 288084838692681114950621173 27007953627438854526620735)
        ·
          refine ⟨40511930441158281789931103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27007953627438854526620735 40511930441158281789931103)
          ·
            refine ⟨60767895661737422684896655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40511930441158281789931103 60767895661737422684896655)
            ·
              refine ⟨91151843492606134027344983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60767895661737422684896655 91151843492606134027344983)
              ·
                refine ⟨136727765238909201041017475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91151843492606134027344983 136727765238909201041017475)
                ·
                  refine ⟨205091647858363801561526213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136727765238909201041017475 205091647858363801561526213)
                  ·
                    refine ⟨38454683973443212792786165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 205091647858363801561526213 38454683973443212792786165)
                    ·
                      refine ⟨3605126622510301199323703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38454683973443212792786165 3605126622510301199323703)
                      ·
                        rfl

theorem cell23_7020959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_7020959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020959 prefixEnd_7020959 := by exact prefixLift 7020959
  have htrace : WordTrace (prefixWord ++ tailWord_7020959) baseStart_7020959 baseEnd_7020959 := by
    simpa [prefixWord, tailWord_7020959, baseEnd_7020959] using wordTrace_append hprefix tailTrace_7020959
  have hstable : (prefixWord ++ tailWord_7020959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020959).length < 2 ^ (prefixWord ++ tailWord_7020959).sum := by decide
  have hdescent : baseEnd_7020959 < baseStart_7020959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020970 : List Nat := [3, 1, 6, 1, 1, 2, 9]
def baseStart_7020970 : Nat := 118140960795 + 7020970 * 2 ^ 59
def prefixEnd_7020970 : Nat := 4983230072969 + 3 ^ 40 * 7020970 * 2
def baseEnd_7020970 : Nat := 44507805812314822917113

theorem tailTrace_7020970 : CollatzResearch.WordTrace tailWord_7020970 prefixEnd_7020970 44507805812314822917113 := by
  unfold tailWord_7020970
  simp only [CollatzResearch.WordTrace]
  refine ⟨64018953343558062764245091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170717208916154834037986909 64018953343558062764245091)
  ·
    refine ⟨96028430015337094146367637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64018953343558062764245091 96028430015337094146367637)
    ·
      refine ⟨4501332656968926288110983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96028430015337094146367637 4501332656968926288110983)
      ·
        refine ⟨6751998985453389432166475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501332656968926288110983 6751998985453389432166475)
        ·
          refine ⟨10127998478180084148249713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751998985453389432166475 10127998478180084148249713)
          ·
            refine ⟨7595998858635063111187285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10127998478180084148249713 7595998858635063111187285)
            ·
              refine ⟨44507805812314822917113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7595998858635063111187285 44507805812314822917113)
              ·
                rfl

theorem cell23_7020970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 9].length) (baseStart_7020970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7020970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7020970 prefixEnd_7020970 := by exact prefixLift 7020970
  have htrace : WordTrace (prefixWord ++ tailWord_7020970) baseStart_7020970 baseEnd_7020970 := by
    simpa [prefixWord, tailWord_7020970, baseEnd_7020970] using wordTrace_append hprefix tailTrace_7020970
  have hstable : (prefixWord ++ tailWord_7020970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020970).length < 2 ^ (prefixWord ++ tailWord_7020970).sum := by decide
  have hdescent : baseEnd_7020970 < baseStart_7020970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021009 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 7]
def baseStart_7021009 : Nat := 118140960795 + 7021009 * 2 ^ 59
def prefixEnd_7021009 : Nat := 4983230072969 + 3 ^ 40 * 7021009 * 2
def baseEnd_7021009 : Nat := 400572477393669555966497

theorem tailTrace_7021009 : CollatzResearch.WordTrace tailWord_7021009 prefixEnd_7021009 400572477393669555966497 := by
  unfold tailWord_7021009
  simp only [CollatzResearch.WordTrace]
  refine ⟨256077235821090960717650081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170718157214060640478433387 256077235821090960717650081)
  ·
    refine ⟨192057926865818220538237561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256077235821090960717650081 192057926865818220538237561)
    ·
      refine ⟨144043445149363665403678171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192057926865818220538237561 144043445149363665403678171)
      ·
        refine ⟨216065167724045498105517257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144043445149363665403678171 216065167724045498105517257)
        ·
          refine ⟨162048875793034123579137943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216065167724045498105517257 162048875793034123579137943)
          ·
            refine ⟨243073313689551185368706915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162048875793034123579137943 243073313689551185368706915)
            ·
              refine ⟨364609970534326778053060373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243073313689551185368706915 364609970534326778053060373)
              ·
                refine ⟨17091092368796567721237205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 364609970534326778053060373 17091092368796567721237205)
                ·
                  refine ⟨400572477393669555966497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17091092368796567721237205 400572477393669555966497)
                  ·
                    rfl

theorem cell23_7021009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 7].length) (baseStart_7021009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021009 prefixEnd_7021009 := by exact prefixLift 7021009
  have htrace : WordTrace (prefixWord ++ tailWord_7021009) baseStart_7021009 baseEnd_7021009 := by
    simpa [prefixWord, tailWord_7021009, baseEnd_7021009] using wordTrace_append hprefix tailTrace_7021009
  have hstable : (prefixWord ++ tailWord_7021009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021009).length < 2 ^ (prefixWord ++ tailWord_7021009).sum := by decide
  have hdescent : baseEnd_7021009 < baseStart_7021009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021036 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 3]
def baseStart_7021036 : Nat := 118140960795 + 7021036 * 2 ^ 59
def prefixEnd_7021036 : Nat := 4983230072969 + 3 ^ 40 * 7021036 * 2
def baseEnd_7021036 : Nat := 3605166160520697398060849

theorem tailTrace_7021036 : CollatzResearch.WordTrace tailWord_7021036 prefixEnd_7021036 3605166160520697398060849 := by
  unfold tailWord_7021036
  simp only [CollatzResearch.WordTrace]
  refine ⟨128039110295996572164441481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170718813727995429552588641 128039110295996572164441481)
  ·
    refine ⟨96029332721997429123331111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128039110295996572164441481 96029332721997429123331111)
    ·
      refine ⟨144043999082996143684996667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96029332721997429123331111 144043999082996143684996667)
      ·
        refine ⟨216065998624494215527495001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144043999082996143684996667 216065998624494215527495001)
        ·
          refine ⟨162049498968370661645621251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216065998624494215527495001 162049498968370661645621251)
          ·
            refine ⟨243074248452555992468431877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162049498968370661645621251 243074248452555992468431877)
            ·
              refine ⟨45576421584854248587830977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243074248452555992468431877 45576421584854248587830977)
              ·
                refine ⟨34182316188640686440873233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45576421584854248587830977 34182316188640686440873233)
                ·
                  refine ⟨25636737141480514830654925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34182316188640686440873233 25636737141480514830654925)
                  ·
                    refine ⟨9613776428055193061495597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25636737141480514830654925 9613776428055193061495597)
                    ·
                      refine ⟨3605166160520697398060849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9613776428055193061495597 3605166160520697398060849)
                      ·
                        rfl

theorem cell23_7021036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_7021036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021036 prefixEnd_7021036 := by exact prefixLift 7021036
  have htrace : WordTrace (prefixWord ++ tailWord_7021036) baseStart_7021036 baseEnd_7021036 := by
    simpa [prefixWord, tailWord_7021036, baseEnd_7021036] using wordTrace_append hprefix tailTrace_7021036
  have hstable : (prefixWord ++ tailWord_7021036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021036).length < 2 ^ (prefixWord ++ tailWord_7021036).sum := by decide
  have hdescent : baseEnd_7021036 < baseStart_7021036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
