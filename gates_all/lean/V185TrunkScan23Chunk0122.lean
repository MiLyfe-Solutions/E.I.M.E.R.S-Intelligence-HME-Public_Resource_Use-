import V185TrunkScan23Chunk0121

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_722180 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_722180 : Nat := 118140960795 + 722180 * 2 ^ 59
def prefixEnd_722180 : Nat := 4983230072969 + 3 ^ 40 * 722180 * 2
def baseEnd_722180 : Nat := 370825459064089701128761

theorem tailTrace_722180 : CollatzResearch.WordTrace tailWord_722180 prefixEnd_722180 370825459064089701128761 := by
  unfold tailWord_722180
  simp only [CollatzResearch.WordTrace]
  refine ⟨13170034261836336684813997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17560045682448448913085329 13170034261836336684813997)
  ·
    refine ⟨4938762848188626256805249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13170034261836336684813997 4938762848188626256805249)
    ·
      refine ⟨3704072136141469692603937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4938762848188626256805249 3704072136141469692603937)
      ·
        refine ⟨2778054102106102269452953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3704072136141469692603937 2778054102106102269452953)
        ·
          refine ⟨2083540576579576702089715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2778054102106102269452953 2083540576579576702089715)
          ·
            refine ⟨3125310864869365053134573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083540576579576702089715 3125310864869365053134573)
            ·
              refine ⟨1171991574326011894925465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3125310864869365053134573 1171991574326011894925465)
              ·
                refine ⟨878993680744508921194099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1171991574326011894925465 878993680744508921194099)
                ·
                  refine ⟨1318490521116763381791149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 878993680744508921194099 1318490521116763381791149)
                  ·
                    refine ⟨494433945418786268171681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1318490521116763381791149 494433945418786268171681)
                    ·
                      refine ⟨370825459064089701128761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494433945418786268171681 370825459064089701128761)
                      ·
                        rfl

theorem cell23_722180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_722180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722180 prefixEnd_722180 := by exact prefixLift 722180
  have htrace : WordTrace (prefixWord ++ tailWord_722180) baseStart_722180 baseEnd_722180 := by
    simpa [prefixWord, tailWord_722180, baseEnd_722180] using wordTrace_append hprefix tailTrace_722180
  have hstable : (prefixWord ++ tailWord_722180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722180).length < 2 ^ (prefixWord ++ tailWord_722180).sum := by decide
  have hdescent : baseEnd_722180 < baseStart_722180 := by decide
  rcases family_descends (prefixWord ++ tailWord_722180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722226 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_722226 : Nat := 118140960795 + 722226 * 2 ^ 59
def prefixEnd_722226 : Nat := 4983230072969 + 3 ^ 40 * 722226 * 2
def baseEnd_722226 : Nat := 370849079174196521153549

theorem tailTrace_722226 : CollatzResearch.WordTrace tailWord_722226 prefixEnd_722226 370849079174196521153549 := by
  unfold tailWord_722226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6585436570376505806450633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17561164187670682150535021 6585436570376505806450633)
  ·
    refine ⟨4939077427782379354837975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6585436570376505806450633 4939077427782379354837975)
    ·
      refine ⟨7408616141673569032256963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4939077427782379354837975 7408616141673569032256963)
      ·
        refine ⟨11112924212510353548385445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7408616141673569032256963 11112924212510353548385445)
        ·
          refine ⟨2083673289845691290322271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11112924212510353548385445 2083673289845691290322271)
          ·
            refine ⟨3125509934768536935483407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083673289845691290322271 3125509934768536935483407)
            ·
              refine ⟨4688264902152805403225111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125509934768536935483407 4688264902152805403225111)
              ·
                refine ⟨7032397353229208104837667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688264902152805403225111 7032397353229208104837667)
                ·
                  refine ⟨10548596029843812157256501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7032397353229208104837667 10548596029843812157256501)
                  ·
                    refine ⟨988930877797857389742797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10548596029843812157256501 988930877797857389742797)
                    ·
                      refine ⟨370849079174196521153549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 988930877797857389742797 370849079174196521153549)
                      ·
                        rfl

theorem cell23_722226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_722226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722226 prefixEnd_722226 := by exact prefixLift 722226
  have htrace : WordTrace (prefixWord ++ tailWord_722226) baseStart_722226 baseEnd_722226 := by
    simpa [prefixWord, tailWord_722226, baseEnd_722226] using wordTrace_append hprefix tailTrace_722226
  have hstable : (prefixWord ++ tailWord_722226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722226).length < 2 ^ (prefixWord ++ tailWord_722226).sum := by decide
  have hdescent : baseEnd_722226 < baseStart_722226 := by decide
  rcases family_descends (prefixWord ++ tailWord_722226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722266 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_722266 : Nat := 118140960795 + 722266 * 2 ^ 59
def prefixEnd_722266 : Nat := 4983230072969 + 3 ^ 40 * 722266 * 2
def baseEnd_722266 : Nat := 370869618400376364653365

theorem tailTrace_722266 : CollatzResearch.WordTrace tailWord_722266 prefixEnd_722266 370869618400376364653365 := by
  unfold tailWord_722266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6585801300340277514314663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17562136800907406704839101 6585801300340277514314663)
  ·
    refine ⟨9878701950510416271471995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6585801300340277514314663 9878701950510416271471995)
    ·
      refine ⟨14818052925765624407207993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9878701950510416271471995 14818052925765624407207993)
      ·
        refine ⟨11113539694324218305405995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14818052925765624407207993 11113539694324218305405995)
        ·
          refine ⟨16670309541486327458108993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11113539694324218305405995 16670309541486327458108993)
          ·
            refine ⟨12502732156114745593581745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16670309541486327458108993 12502732156114745593581745)
            ·
              refine ⟨9377049117086059195186309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12502732156114745593581745 9377049117086059195186309)
              ·
                refine ⟨1758196709453636099097433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9377049117086059195186309 1758196709453636099097433)
                ·
                  refine ⟨1318647532090227074323075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1758196709453636099097433 1318647532090227074323075)
                  ·
                    refine ⟨1977971298135340611484613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1318647532090227074323075 1977971298135340611484613)
                    ·
                      refine ⟨370869618400376364653365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1977971298135340611484613 370869618400376364653365)
                      ·
                        rfl

theorem cell23_722266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_722266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722266 prefixEnd_722266 := by exact prefixLift 722266
  have htrace : WordTrace (prefixWord ++ tailWord_722266) baseStart_722266 baseEnd_722266 := by
    simpa [prefixWord, tailWord_722266, baseEnd_722266] using wordTrace_append hprefix tailTrace_722266
  have hstable : (prefixWord ++ tailWord_722266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722266).length < 2 ^ (prefixWord ++ tailWord_722266).sum := by decide
  have hdescent : baseEnd_722266 < baseStart_722266 := by decide
  rcases family_descends (prefixWord ++ tailWord_722266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722336 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 3, 5]
def baseStart_722336 : Nat := 118140960795 + 722336 * 2 ^ 59
def prefixEnd_722336 : Nat := 4983230072969 + 3 ^ 40 * 722336 * 2
def baseEnd_722336 : Nat := 123635187348730363592681

theorem tailTrace_722336 : CollatzResearch.WordTrace tailWord_722336 prefixEnd_722336 123635187348730363592681 := by
  unfold tailWord_722336
  simp only [CollatzResearch.WordTrace]
  refine ⟨13172879155553756006153431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17563838874071674674871241 13172879155553756006153431)
  ·
    refine ⟨19759318733330634009230147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13172879155553756006153431 19759318733330634009230147)
    ·
      refine ⟨29638978099995951013845221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19759318733330634009230147 29638978099995951013845221)
      ·
        refine ⟨5557308393749240815095979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29638978099995951013845221 5557308393749240815095979)
        ·
          refine ⟨8335962590623861222643969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5557308393749240815095979 8335962590623861222643969)
          ·
            refine ⟨6251971942967895916982977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8335962590623861222643969 6251971942967895916982977)
            ·
              refine ⟨4688978957225921937737233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6251971942967895916982977 4688978957225921937737233)
              ·
                refine ⟨3516734217919441453302925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4688978957225921937737233 3516734217919441453302925)
                ·
                  refine ⟨1318775331719790544988597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3516734217919441453302925 1318775331719790544988597)
                  ·
                    refine ⟨123635187348730363592681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1318775331719790544988597 123635187348730363592681)
                    ·
                      rfl

theorem cell23_722336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_722336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722336 prefixEnd_722336 := by exact prefixLift 722336
  have htrace : WordTrace (prefixWord ++ tailWord_722336) baseStart_722336 baseEnd_722336 := by
    simpa [prefixWord, tailWord_722336, baseEnd_722336] using wordTrace_append hprefix tailTrace_722336
  have hstable : (prefixWord ++ tailWord_722336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722336).length < 2 ^ (prefixWord ++ tailWord_722336).sum := by decide
  have hdescent : baseEnd_722336 < baseStart_722336 := by decide
  rcases family_descends (prefixWord ++ tailWord_722336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722383 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 2, 4]
def baseStart_722383 : Nat := 118140960795 + 722383 * 2 ^ 59
def prefixEnd_722383 : Nat := 4983230072969 + 3 ^ 40 * 722383 * 2
def baseEnd_722383 : Nat := 123643231878984135630109

theorem tailTrace_722383 : CollatzResearch.WordTrace tailWord_722383 prefixEnd_722383 123643231878984135630109 := by
  unfold tailWord_722383
  simp only [CollatzResearch.WordTrace]
  refine ⟨26347472541937239039267803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17564981694624826026178535 26347472541937239039267803)
  ·
    refine ⟨39521208812905858558901705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26347472541937239039267803 39521208812905858558901705)
    ·
      refine ⟨29640906609679393919176279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39521208812905858558901705 29640906609679393919176279)
      ·
        refine ⟨44461359914519090878764419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29640906609679393919176279 44461359914519090878764419)
        ·
          refine ⟨66692039871778636318146629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44461359914519090878764419 66692039871778636318146629)
          ·
            refine ⟨12504757475958494309652493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66692039871778636318146629 12504757475958494309652493)
            ·
              refine ⟨4689284053484435366119685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12504757475958494309652493 4689284053484435366119685)
              ·
                refine ⟨879240760028331631147441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4689284053484435366119685 879240760028331631147441)
                ·
                  refine ⟨659430570021248723360581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 879240760028331631147441 659430570021248723360581)
                  ·
                    refine ⟨123643231878984135630109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659430570021248723360581 123643231878984135630109)
                    ·
                      rfl

theorem cell23_722383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 4].length) (baseStart_722383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722383 prefixEnd_722383 := by exact prefixLift 722383
  have htrace : WordTrace (prefixWord ++ tailWord_722383) baseStart_722383 baseEnd_722383 := by
    simpa [prefixWord, tailWord_722383, baseEnd_722383] using wordTrace_append hprefix tailTrace_722383
  have hstable : (prefixWord ++ tailWord_722383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722383).length < 2 ^ (prefixWord ++ tailWord_722383).sum := by decide
  have hdescent : baseEnd_722383 < baseStart_722383 := by decide
  rcases family_descends (prefixWord ++ tailWord_722383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722390 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_722390 : Nat := 118140960795 + 722390 * 2 ^ 59
def prefixEnd_722390 : Nat := 4983230072969 + 3 ^ 40 * 722390 * 2
def baseEnd_722390 : Nat := 370933290001533879502795

theorem tailTrace_722390 : CollatzResearch.WordTrace tailWord_722390 prefixEnd_722390 370933290001533879502795 := by
  unfold tailWord_722390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646732990806992452173289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17565151901941252823181749 1646732990806992452173289)
  ·
    refine ⟨1235049743105244339129967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1646732990806992452173289 1235049743105244339129967)
    ·
      refine ⟨1852574614657866508694951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1235049743105244339129967 1852574614657866508694951)
      ·
        refine ⟨2778861921986799763042427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852574614657866508694951 2778861921986799763042427)
        ·
          refine ⟨4168292882980199644563641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778861921986799763042427 4168292882980199644563641)
          ·
            refine ⟨3126219662235149733422731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4168292882980199644563641 3126219662235149733422731)
            ·
              refine ⟨4689329493352724600134097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126219662235149733422731 4689329493352724600134097)
              ·
                refine ⟨3516997120014543450100573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4689329493352724600134097 3516997120014543450100573)
                ·
                  refine ⟨1318873920005453793787715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3516997120014543450100573 1318873920005453793787715)
                  ·
                    refine ⟨1978310880008180690681573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1318873920005453793787715 1978310880008180690681573)
                    ·
                      refine ⟨370933290001533879502795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1978310880008180690681573 370933290001533879502795)
                      ·
                        rfl

theorem cell23_722390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_722390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722390 prefixEnd_722390 := by exact prefixLift 722390
  have htrace : WordTrace (prefixWord ++ tailWord_722390) baseStart_722390 baseEnd_722390 := by
    simpa [prefixWord, tailWord_722390, baseEnd_722390] using wordTrace_append hprefix tailTrace_722390
  have hstable : (prefixWord ++ tailWord_722390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722390).length < 2 ^ (prefixWord ++ tailWord_722390).sum := by decide
  have hdescent : baseEnd_722390 < baseStart_722390 := by decide
  rcases family_descends (prefixWord ++ tailWord_722390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722393 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 3, 2, 3]
def baseStart_722393 : Nat := 118140960795 + 722393 * 2 ^ 59
def prefixEnd_722393 : Nat := 4983230072969 + 3 ^ 40 * 722393 * 2
def baseEnd_722393 : Nat := 370934830443497367765281

theorem tailTrace_722393 : CollatzResearch.WordTrace tailWord_722393 prefixEnd_722393 370934830443497367765281 := by
  unfold tailWord_722393
  simp only [CollatzResearch.WordTrace]
  refine ⟨26347837271901010747131833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17565224847934007164754555 26347837271901010747131833)
  ·
    refine ⟨19760877953925758060348875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26347837271901010747131833 19760877953925758060348875)
    ·
      refine ⟨29641316930888637090523313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19760877953925758060348875 29641316930888637090523313)
      ·
        refine ⟨22230987698166477817892485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29641316930888637090523313 22230987698166477817892485)
        ·
          refine ⟨4168310193406214590854841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22230987698166477817892485 4168310193406214590854841)
          ·
            refine ⟨3126232645054660943141131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4168310193406214590854841 3126232645054660943141131)
            ·
              refine ⟨4689348967581991414711697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126232645054660943141131 4689348967581991414711697)
              ·
                refine ⟨3517011725686493561033773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4689348967581991414711697 3517011725686493561033773)
                ·
                  refine ⟨1318879397132435085387665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3517011725686493561033773 1318879397132435085387665)
                  ·
                    refine ⟨989159547849326314040749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1318879397132435085387665 989159547849326314040749)
                    ·
                      refine ⟨370934830443497367765281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 989159547849326314040749 370934830443497367765281)
                      ·
                        rfl

theorem cell23_722393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_722393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722393 prefixEnd_722393 := by exact prefixLift 722393
  have htrace : WordTrace (prefixWord ++ tailWord_722393) baseStart_722393 baseEnd_722393 := by
    simpa [prefixWord, tailWord_722393, baseEnd_722393] using wordTrace_append hprefix tailTrace_722393
  have hstable : (prefixWord ++ tailWord_722393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722393).length < 2 ^ (prefixWord ++ tailWord_722393).sum := by decide
  have hdescent : baseEnd_722393 < baseStart_722393 := by decide
  rcases family_descends (prefixWord ++ tailWord_722393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722403 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 4]
def baseStart_722403 : Nat := 118140960795 + 722403 * 2 ^ 59
def prefixEnd_722403 : Nat := 4983230072969 + 3 ^ 40 * 722403 * 2
def baseEnd_722403 : Nat := 370939965250042328640235

theorem tailTrace_722403 : CollatzResearch.WordTrace tailWord_722403 prefixEnd_722403 370939965250042328640235 := by
  unfold tailWord_722403
  simp only [CollatzResearch.WordTrace]
  refine ⟨26348202001864782454995863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17565468001243188303330575 26348202001864782454995863)
  ·
    refine ⟨39522303002797173682493795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26348202001864782454995863 39522303002797173682493795)
    ·
      refine ⟨59283454504195760523740693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39522303002797173682493795 59283454504195760523740693)
      ·
        refine ⟨2778911929884176274550345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59283454504195760523740693 2778911929884176274550345)
        ·
          refine ⟨2084183947413132205912759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2778911929884176274550345 2084183947413132205912759)
          ·
            refine ⟨3126275921119698308869139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084183947413132205912759 3126275921119698308869139)
            ·
              refine ⟨4689413881679547463303709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126275921119698308869139 4689413881679547463303709)
              ·
                refine ⟨1758530205629830298738891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4689413881679547463303709 1758530205629830298738891)
                ·
                  refine ⟨2637795308444745448108337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758530205629830298738891 2637795308444745448108337)
                  ·
                    refine ⟨1978346481333559086081253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2637795308444745448108337 1978346481333559086081253)
                    ·
                      refine ⟨370939965250042328640235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1978346481333559086081253 370939965250042328640235)
                      ·
                        rfl

theorem cell23_722403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_722403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722403 prefixEnd_722403 := by exact prefixLift 722403
  have htrace : WordTrace (prefixWord ++ tailWord_722403) baseStart_722403 baseEnd_722403 := by
    simpa [prefixWord, tailWord_722403, baseEnd_722403] using wordTrace_append hprefix tailTrace_722403
  have hstable : (prefixWord ++ tailWord_722403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722403).length < 2 ^ (prefixWord ++ tailWord_722403).sum := by decide
  have hdescent : baseEnd_722403 < baseStart_722403 := by decide
  rcases family_descends (prefixWord ++ tailWord_722403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722407 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_722407 : Nat := 118140960795 + 722407 * 2 ^ 59
def prefixEnd_722407 : Nat := 4983230072969 + 3 ^ 40 * 722407 * 2
def baseEnd_722407 : Nat := 370942019172660312990217

theorem tailTrace_722407 : CollatzResearch.WordTrace tailWord_722407 prefixEnd_722407 370942019172660312990217 := by
  unfold tailWord_722407
  simp only [CollatzResearch.WordTrace]
  refine ⟨26348347893850291138141475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17565565262566860758760983 26348347893850291138141475)
  ·
    refine ⟨39522521840775436707212213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26348347893850291138141475 39522521840775436707212213)
    ·
      refine ⟨3705236422572697191301145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39522521840775436707212213 3705236422572697191301145)
      ·
        refine ⟨2778927316929522893475859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3705236422572697191301145 2778927316929522893475859)
        ·
          refine ⟨4168390975394284340213789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778927316929522893475859 4168390975394284340213789)
          ·
            refine ⟨1563146615772856627580171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4168390975394284340213789 1563146615772856627580171)
            ·
              refine ⟨2344719923659284941370257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563146615772856627580171 2344719923659284941370257)
              ·
                refine ⟨1758539942744463706027693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344719923659284941370257 1758539942744463706027693)
                ·
                  refine ⟨659452478529173889760385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1758539942744463706027693 659452478529173889760385)
                  ·
                    refine ⟨494589358896880417320289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 659452478529173889760385 494589358896880417320289)
                    ·
                      refine ⟨370942019172660312990217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494589358896880417320289 370942019172660312990217)
                      ·
                        rfl

theorem cell23_722407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_722407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722407 prefixEnd_722407 := by exact prefixLift 722407
  have htrace : WordTrace (prefixWord ++ tailWord_722407) baseStart_722407 baseEnd_722407 := by
    simpa [prefixWord, tailWord_722407, baseEnd_722407] using wordTrace_append hprefix tailTrace_722407
  have hstable : (prefixWord ++ tailWord_722407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722407).length < 2 ^ (prefixWord ++ tailWord_722407).sum := by decide
  have hdescent : baseEnd_722407 < baseStart_722407 := by decide
  rcases family_descends (prefixWord ++ tailWord_722407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722424 : List Nat := [2, 1, 2, 1, 1, 6, 2, 3, 1, 2, 2]
def baseStart_722424 : Nat := 118140960795 + 722424 * 2 ^ 59
def prefixEnd_722424 : Nat := 4983230072969 + 3 ^ 40 * 722424 * 2
def baseEnd_722424 : Nat := 370950748343786746477639

theorem tailTrace_722424 : CollatzResearch.WordTrace tailWord_722424 prefixEnd_722424 370950748343786746477639 := by
  unfold tailWord_722424
  simp only [CollatzResearch.WordTrace]
  refine ⟨13174483967394351520755163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17565978623192468694340217 13174483967394351520755163)
  ·
    refine ⟨19761725951091527281132745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13174483967394351520755163 19761725951091527281132745)
    ·
      refine ⟨14821294463318645460849559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19761725951091527281132745 14821294463318645460849559)
      ·
        refine ⟨22231941694977968191274339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14821294463318645460849559 22231941694977968191274339)
        ·
          refine ⟨33347912542466952286911509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22231941694977968191274339 33347912542466952286911509)
          ·
            refine ⟨1563183400428138388448977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33347912542466952286911509 1563183400428138388448977)
            ·
              refine ⟨1172387550321103791336733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563183400428138388448977 1172387550321103791336733)
              ·
                refine ⟨439645331370413921751275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1172387550321103791336733 439645331370413921751275)
                ·
                  refine ⟨659467997055620882626913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439645331370413921751275 659467997055620882626913)
                  ·
                    refine ⟨494600997791715661970185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 659467997055620882626913 494600997791715661970185)
                    ·
                      refine ⟨370950748343786746477639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494600997791715661970185 370950748343786746477639)
                      ·
                        rfl

theorem cell23_722424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 1, 2, 2].length) (baseStart_722424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722424 prefixEnd_722424 := by exact prefixLift 722424
  have htrace : WordTrace (prefixWord ++ tailWord_722424) baseStart_722424 baseEnd_722424 := by
    simpa [prefixWord, tailWord_722424, baseEnd_722424] using wordTrace_append hprefix tailTrace_722424
  have hstable : (prefixWord ++ tailWord_722424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722424).length < 2 ^ (prefixWord ++ tailWord_722424).sum := by decide
  have hdescent : baseEnd_722424 < baseStart_722424 := by decide
  rcases family_descends (prefixWord ++ tailWord_722424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722430 : List Nat := [4, 2, 2, 3, 1, 1, 10]
def baseStart_722430 : Nat := 118140960795 + 722430 * 2 ^ 59
def prefixEnd_722430 : Nat := 4983230072969 + 3 ^ 40 * 722430 * 2
def baseEnd_722430 : Nat := 4579676904045848432131

theorem tailTrace_722430 : CollatzResearch.WordTrace tailWord_722430 prefixEnd_722430 4579676904045848432131 := by
  unfold tailWord_722430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293648346595870758278593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17566124515177977377485829 3293648346595870758278593)
  ·
    refine ⟨2470236259946903068708945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3293648346595870758278593 2470236259946903068708945)
    ·
      refine ⟨1852677194960177301531709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2470236259946903068708945 1852677194960177301531709)
      ·
        refine ⟨694753948110066488074391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1852677194960177301531709 694753948110066488074391)
        ·
          refine ⟨1042130922165099732111587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694753948110066488074391 1042130922165099732111587)
          ·
            refine ⟨1563196383247649598167381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042130922165099732111587 1563196383247649598167381)
            ·
              refine ⟨4579676904045848432131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1563196383247649598167381 4579676904045848432131)
              ·
                rfl

theorem cell23_722430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 10].length) (baseStart_722430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722430 prefixEnd_722430 := by exact prefixLift 722430
  have htrace : WordTrace (prefixWord ++ tailWord_722430) baseStart_722430 baseEnd_722430 := by
    simpa [prefixWord, tailWord_722430, baseEnd_722430] using wordTrace_append hprefix tailTrace_722430
  have hstable : (prefixWord ++ tailWord_722430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722430).length < 2 ^ (prefixWord ++ tailWord_722430).sum := by decide
  have hdescent : baseEnd_722430 < baseStart_722430 := by decide
  rcases family_descends (prefixWord ++ tailWord_722430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722434 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_722434 : Nat := 118140960795 + 722434 * 2 ^ 59
def prefixEnd_722434 : Nat := 4983230072969 + 3 ^ 40 * 722434 * 2
def baseEnd_722434 : Nat := 123651961050110569117531

theorem tailTrace_722434 : CollatzResearch.WordTrace tailWord_722434 prefixEnd_722434 123651961050110569117531 := by
  unfold tailWord_722434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587333166188118687343589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17566221776501649832916237 6587333166188118687343589)
  ·
    refine ⟨1235124968660272253876923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6587333166188118687343589 1235124968660272253876923)
    ·
      refine ⟨1852687452990408380815385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1235124968660272253876923 1852687452990408380815385)
      ·
        refine ⟨1389515589742806285611539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1852687452990408380815385 1389515589742806285611539)
        ·
          refine ⟨2084273384614209428417309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389515589742806285611539 2084273384614209428417309)
          ·
            refine ⟨781602519230328535656491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2084273384614209428417309 781602519230328535656491)
            ·
              refine ⟨1172403778845492803484737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781602519230328535656491 1172403778845492803484737)
              ·
                refine ⟨879302834134119602613553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172403778845492803484737 879302834134119602613553)
                ·
                  refine ⟨659477125600589701960165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 879302834134119602613553 659477125600589701960165)
                  ·
                    refine ⟨123651961050110569117531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659477125600589701960165 123651961050110569117531)
                    ·
                      rfl

theorem cell23_722434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_722434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722434 prefixEnd_722434 := by exact prefixLift 722434
  have htrace : WordTrace (prefixWord ++ tailWord_722434) baseStart_722434 baseEnd_722434 := by
    simpa [prefixWord, tailWord_722434, baseEnd_722434] using wordTrace_append hprefix tailTrace_722434
  have hstable : (prefixWord ++ tailWord_722434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722434).length < 2 ^ (prefixWord ++ tailWord_722434).sum := by decide
  have hdescent : baseEnd_722434 < baseStart_722434 := by decide
  rcases family_descends (prefixWord ++ tailWord_722434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722483 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 5]
def baseStart_722483 : Nat := 118140960795 + 722483 * 2 ^ 59
def prefixEnd_722483 : Nat := 4983230072969 + 3 ^ 40 * 722483 * 2
def baseEnd_722483 : Nat := 370981043702402015639867

theorem tailTrace_722483 : CollatzResearch.WordTrace tailWord_722483 prefixEnd_722483 370981043702402015639867 := by
  unfold tailWord_722483
  simp only [CollatzResearch.WordTrace]
  refine ⟨26351119841574956117908103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17567413227716637411938735 26351119841574956117908103)
  ·
    refine ⟨39526679762362434176862155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26351119841574956117908103 39526679762362434176862155)
    ·
      refine ⟨59290019643543651265293233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39526679762362434176862155 59290019643543651265293233)
      ·
        refine ⟨44467514732657738448969925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59290019643543651265293233 44467514732657738448969925)
        ·
          refine ⟨8337659012373325959181861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44467514732657738448969925 8337659012373325959181861)
          ·
            refine ⟨1563311064819998617346599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8337659012373325959181861 1563311064819998617346599)
            ·
              refine ⟨2344966597229997926019899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563311064819998617346599 2344966597229997926019899)
              ·
                refine ⟨3517449895844996889029849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344966597229997926019899 3517449895844996889029849)
                ·
                  refine ⟨2638087421883747666772387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3517449895844996889029849 2638087421883747666772387)
                  ·
                    refine ⟨3957131132825621500158581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2638087421883747666772387 3957131132825621500158581)
                    ·
                      refine ⟨370981043702402015639867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3957131132825621500158581 370981043702402015639867)
                      ·
                        rfl

theorem cell23_722483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_722483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722483 prefixEnd_722483 := by exact prefixLift 722483
  have htrace : WordTrace (prefixWord ++ tailWord_722483) baseStart_722483 baseEnd_722483 := by
    simpa [prefixWord, tailWord_722483, baseEnd_722483] using wordTrace_append hprefix tailTrace_722483
  have hstable : (prefixWord ++ tailWord_722483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722483).length < 2 ^ (prefixWord ++ tailWord_722483).sum := by decide
  have hdescent : baseEnd_722483 < baseStart_722483 := by decide
  rcases family_descends (prefixWord ++ tailWord_722483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722496 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_722496 : Nat := 118140960795 + 722496 * 2 ^ 59
def prefixEnd_722496 : Nat := 4983230072969 + 3 ^ 40 * 722496 * 2
def baseEnd_722496 : Nat := 370987718950910464777307

theorem tailTrace_722496 : CollatzResearch.WordTrace tailWord_722496 prefixEnd_722496 370987718950910464777307 := by
  unfold tailWord_722496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13175796995263929669065671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17567729327018572892087561 13175796995263929669065671)
  ·
    refine ⟨19763695492895894503598507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13175796995263929669065671 19763695492895894503598507)
    ·
      refine ⟨29645543239343841755397761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19763695492895894503598507 29645543239343841755397761)
      ·
        refine ⟨22234157429507881316548321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29645543239343841755397761 22234157429507881316548321)
        ·
          refine ⟨16675618072130910987411241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22234157429507881316548321 16675618072130910987411241)
          ·
            refine ⟨12506713554098183240558431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16675618072130910987411241 12506713554098183240558431)
            ·
              refine ⟨18760070331147274860837647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12506713554098183240558431 18760070331147274860837647)
              ·
                refine ⟨28140105496720912291256471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18760070331147274860837647 28140105496720912291256471)
                ·
                  refine ⟨42210158245081368436884707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28140105496720912291256471 42210158245081368436884707)
                  ·
                    refine ⟨63315237367622052655327061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42210158245081368436884707 63315237367622052655327061)
                    ·
                      refine ⟨370987718950910464777307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 63315237367622052655327061 370987718950910464777307)
                      ·
                        rfl

theorem cell23_722496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_722496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722496 prefixEnd_722496 := by exact prefixLift 722496
  have htrace : WordTrace (prefixWord ++ tailWord_722496) baseStart_722496 baseEnd_722496 := by
    simpa [prefixWord, tailWord_722496, baseEnd_722496] using wordTrace_append hprefix tailTrace_722496
  have hstable : (prefixWord ++ tailWord_722496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722496).length < 2 ^ (prefixWord ++ tailWord_722496).sum := by decide
  have hdescent : baseEnd_722496 < baseStart_722496 := by decide
  rcases family_descends (prefixWord ++ tailWord_722496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722497 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_722497 : Nat := 118140960795 + 722497 * 2 ^ 59
def prefixEnd_722497 : Nat := 4983230072969 + 3 ^ 40 * 722497 * 2
def baseEnd_722497 : Nat := 370988232431564960864803

theorem tailTrace_722497 : CollatzResearch.WordTrace tailWord_722497 prefixEnd_722497 370988232431564960864803 := by
  unfold tailWord_722497
  simp only [CollatzResearch.WordTrace]
  refine ⟨26351630463524236508917745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17567753642349491005945163 26351630463524236508917745)
  ·
    refine ⟨19763722847643177381688309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26351630463524236508917745 19763722847643177381688309)
    ·
      refine ⟨1852849016966547879533279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19763722847643177381688309 1852849016966547879533279)
      ·
        refine ⟨2779273525449821819299919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852849016966547879533279 2779273525449821819299919)
        ·
          refine ⟨4168910288174732728949879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779273525449821819299919 4168910288174732728949879)
          ·
            refine ⟨6253365432262099093424819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168910288174732728949879 6253365432262099093424819)
            ·
              refine ⟨9380048148393148640137229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6253365432262099093424819 9380048148393148640137229)
              ·
                refine ⟨3517518055647430740051461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9380048148393148640137229 3517518055647430740051461)
                ·
                  refine ⟨659534635433893263759649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3517518055647430740051461 659534635433893263759649)
                  ·
                    refine ⟨494650976575419947819737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 659534635433893263759649 494650976575419947819737)
                    ·
                      refine ⟨370988232431564960864803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494650976575419947819737 370988232431564960864803)
                      ·
                        rfl

theorem cell23_722497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_722497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722497 prefixEnd_722497 := by exact prefixLift 722497
  have htrace : WordTrace (prefixWord ++ tailWord_722497) baseStart_722497 baseEnd_722497 := by
    simpa [prefixWord, tailWord_722497, baseEnd_722497] using wordTrace_append hprefix tailTrace_722497
  have hstable : (prefixWord ++ tailWord_722497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722497).length < 2 ^ (prefixWord ++ tailWord_722497).sum := by decide
  have hdescent : baseEnd_722497 < baseStart_722497 := by decide
  rcases family_descends (prefixWord ++ tailWord_722497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722513 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 1, 5, 3]
def baseStart_722513 : Nat := 118140960795 + 722513 * 2 ^ 59
def prefixEnd_722513 : Nat := 4983230072969 + 3 ^ 40 * 722513 * 2
def baseEnd_722513 : Nat := 370996448122036898264729

theorem tailTrace_722513 : CollatzResearch.WordTrace tailWord_722513 prefixEnd_722513 370996448122036898264729 := by
  unfold tailWord_722513
  simp only [CollatzResearch.WordTrace]
  refine ⟨26352214031466271241500193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17568142687644180827666795 26352214031466271241500193)
  ·
    refine ⟨19764160523599703431125145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26352214031466271241500193 19764160523599703431125145)
    ·
      refine ⟨14823120392699777573343859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19764160523599703431125145 14823120392699777573343859)
      ·
        refine ⟨22234680589049666360015789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14823120392699777573343859 22234680589049666360015789)
        ·
          refine ⟨8338005220893624885005921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22234680589049666360015789 8338005220893624885005921)
          ·
            refine ⟨6253503915670218663754441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8338005220893624885005921 6253503915670218663754441)
            ·
              refine ⟨4690127936752663997815831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6253503915670218663754441 4690127936752663997815831)
              ·
                refine ⟨7035191905128995996723747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4690127936752663997815831 7035191905128995996723747)
                ·
                  refine ⟨10552787857693493995085621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7035191905128995996723747 10552787857693493995085621)
                  ·
                    refine ⟨989323861658765062039277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10552787857693493995085621 989323861658765062039277)
                    ·
                      refine ⟨370996448122036898264729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 989323861658765062039277 370996448122036898264729)
                      ·
                        rfl

theorem cell23_722513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_722513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722513 prefixEnd_722513 := by exact prefixLift 722513
  have htrace : WordTrace (prefixWord ++ tailWord_722513) baseStart_722513 baseEnd_722513 := by
    simpa [prefixWord, tailWord_722513, baseEnd_722513] using wordTrace_append hprefix tailTrace_722513
  have hstable : (prefixWord ++ tailWord_722513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722513).length < 2 ^ (prefixWord ++ tailWord_722513).sum := by decide
  have hdescent : baseEnd_722513 < baseStart_722513 := by decide
  rcases family_descends (prefixWord ++ tailWord_722513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722514 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_722514 : Nat := 118140960795 + 722514 * 2 ^ 59
def prefixEnd_722514 : Nat := 4983230072969 + 3 ^ 40 * 722514 * 2
def baseEnd_722514 : Nat := 370996961602691394352225

theorem tailTrace_722514 : CollatzResearch.WordTrace tailWord_722514 prefixEnd_722514 370996961602691394352225 := by
  unfold tailWord_722514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6588062626115662103071649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17568167002975098941524397 6588062626115662103071649)
  ·
    refine ⟨4941046969586746577303737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6588062626115662103071649 4941046969586746577303737)
    ·
      refine ⟨3705785227190059932977803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4941046969586746577303737 3705785227190059932977803)
      ·
        refine ⟨5558677840785089899466705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3705785227190059932977803 5558677840785089899466705)
        ·
          refine ⟨4169008380588817424600029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5558677840785089899466705 4169008380588817424600029)
          ·
            refine ⟨1563378142720806534225011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4169008380588817424600029 1563378142720806534225011)
            ·
              refine ⟨2345067214081209801337517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563378142720806534225011 2345067214081209801337517)
              ·
                refine ⟨879400205280453675501569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2345067214081209801337517 879400205280453675501569)
                ·
                  refine ⟨659550153960340256626177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 879400205280453675501569 659550153960340256626177)
                  ·
                    refine ⟨494662615470255192469633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 659550153960340256626177 494662615470255192469633)
                    ·
                      refine ⟨370996961602691394352225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494662615470255192469633 370996961602691394352225)
                      ·
                        rfl

theorem cell23_722514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_722514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722514 prefixEnd_722514 := by exact prefixLift 722514
  have htrace : WordTrace (prefixWord ++ tailWord_722514) baseStart_722514 baseEnd_722514 := by
    simpa [prefixWord, tailWord_722514, baseEnd_722514] using wordTrace_append hprefix tailTrace_722514
  have hstable : (prefixWord ++ tailWord_722514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722514).length < 2 ^ (prefixWord ++ tailWord_722514).sum := by decide
  have hdescent : baseEnd_722514 < baseStart_722514 := by decide
  rcases family_descends (prefixWord ++ tailWord_722514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722597 : List Nat := [1, 3, 1, 2, 1, 2, 3, 5, 1, 4]
def baseStart_722597 : Nat := 118140960795 + 722597 * 2 ^ 59
def prefixEnd_722597 : Nat := 4983230072969 + 3 ^ 40 * 722597 * 2
def baseEnd_722597 : Nat := 123679860165671523204781

theorem tailTrace_722597 : CollatzResearch.WordTrace tailWord_722597 prefixEnd_722597 123679860165671523204781 := by
  unfold tailWord_722597
  simp only [CollatzResearch.WordTrace]
  refine ⟨26355277763161953587558045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17570185175441302391705363 26355277763161953587558045)
  ·
    refine ⟨9883229161185732595334267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26355277763161953587558045 9883229161185732595334267)
    ·
      refine ⟨14824843741778598893001401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9883229161185732595334267 14824843741778598893001401)
      ·
        refine ⟨11118632806333949169751051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14824843741778598893001401 11118632806333949169751051)
        ·
          refine ⟨16677949209500923754626577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11118632806333949169751051 16677949209500923754626577)
          ·
            refine ⟨12508461907125692815969933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16677949209500923754626577 12508461907125692815969933)
            ·
              refine ⟨4690673215172134805988725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12508461907125692815969933 4690673215172134805988725)
              ·
                refine ⟨439750613922387638061443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4690673215172134805988725 439750613922387638061443)
                ·
                  refine ⟨659625920883581457092165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439750613922387638061443 659625920883581457092165)
                  ·
                    refine ⟨123679860165671523204781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659625920883581457092165 123679860165671523204781)
                    ·
                      rfl

theorem cell23_722597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_722597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722597 prefixEnd_722597 := by exact prefixLift 722597
  have htrace : WordTrace (prefixWord ++ tailWord_722597) baseStart_722597 baseEnd_722597 := by
    simpa [prefixWord, tailWord_722597, baseEnd_722597] using wordTrace_append hprefix tailTrace_722597
  have hstable : (prefixWord ++ tailWord_722597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722597).length < 2 ^ (prefixWord ++ tailWord_722597).sum := by decide
  have hdescent : baseEnd_722597 < baseStart_722597 := by decide
  rcases family_descends (prefixWord ++ tailWord_722597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722610 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 6]
def baseStart_722610 : Nat := 118140960795 + 722610 * 2 ^ 59
def prefixEnd_722610 : Nat := 4983230072969 + 3 ^ 40 * 722610 * 2
def baseEnd_722610 : Nat := 41227361749502557639087

theorem tailTrace_722610 : CollatzResearch.WordTrace tailWord_722610 prefixEnd_722610 41227361749502557639087 := by
  unfold tailWord_722610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6588937978028714201945321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17570501274743237871854189 6588937978028714201945321)
  ·
    refine ⟨4941703483521535651458991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6588937978028714201945321 4941703483521535651458991)
    ·
      refine ⟨7412555225282303477188487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4941703483521535651458991 7412555225282303477188487)
      ·
        refine ⟨11118832837923455215782731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7412555225282303477188487 11118832837923455215782731)
        ·
          refine ⟨16678249256885182823674097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11118832837923455215782731 16678249256885182823674097)
          ·
            refine ⟨12508686942663887117755573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16678249256885182823674097 12508686942663887117755573)
            ·
              refine ⟨1172689400874739417289585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12508686942663887117755573 1172689400874739417289585)
              ·
                refine ⟨879517050656054562967189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172689400874739417289585 879517050656054562967189)
                ·
                  refine ⟨41227361749502557639087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 879517050656054562967189 41227361749502557639087)
                  ·
                    rfl

theorem cell23_722610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_722610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722610 prefixEnd_722610 := by exact prefixLift 722610
  have htrace : WordTrace (prefixWord ++ tailWord_722610) baseStart_722610 baseEnd_722610 := by
    simpa [prefixWord, tailWord_722610, baseEnd_722610] using wordTrace_append hprefix tailTrace_722610
  have hstable : (prefixWord ++ tailWord_722610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722610).length < 2 ^ (prefixWord ++ tailWord_722610).sum := by decide
  have hdescent : baseEnd_722610 < baseStart_722610 := by decide
  rcases family_descends (prefixWord ++ tailWord_722610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722614 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_722614 : Nat := 118140960795 + 722614 * 2 ^ 59
def prefixEnd_722614 : Nat := 4983230072969 + 3 ^ 40 * 722614 * 2
def baseEnd_722614 : Nat := 123682769889380334367255

theorem tailTrace_722614 : CollatzResearch.WordTrace tailWord_722614 prefixEnd_722614 123682769889380334367255 := by
  unfold tailWord_722614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1647243612756272843182931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17570598536066910327284597 1647243612756272843182931)
  ·
    refine ⟨2470865419134409264774397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1647243612756272843182931 2470865419134409264774397)
    ·
      refine ⟨926574532175403474290399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2470865419134409264774397 926574532175403474290399)
      ·
        refine ⟨1389861798263105211435599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926574532175403474290399 1389861798263105211435599)
        ·
          refine ⟨2084792697394657817153399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389861798263105211435599 2084792697394657817153399)
          ·
            refine ⟨3127189046091986725730099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084792697394657817153399 3127189046091986725730099)
            ·
              refine ⟨4690783569137980088595149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127189046091986725730099 4690783569137980088595149)
              ·
                refine ⟨1759043838426742533223181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4690783569137980088595149 1759043838426742533223181)
                ·
                  refine ⟨659641439410028449958693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1759043838426742533223181 659641439410028449958693)
                  ·
                    refine ⟨123682769889380334367255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659641439410028449958693 123682769889380334367255)
                    ·
                      rfl

theorem cell23_722614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_722614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722614 prefixEnd_722614 := by exact prefixLift 722614
  have htrace : WordTrace (prefixWord ++ tailWord_722614) baseStart_722614 baseEnd_722614 := by
    simpa [prefixWord, tailWord_722614, baseEnd_722614] using wordTrace_append hprefix tailTrace_722614
  have hstable : (prefixWord ++ tailWord_722614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722614).length < 2 ^ (prefixWord ++ tailWord_722614).sum := by decide
  have hdescent : baseEnd_722614 < baseStart_722614 := by decide
  rcases family_descends (prefixWord ++ tailWord_722614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722647 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 2, 3, 2]
def baseStart_722647 : Nat := 118140960795 + 722647 * 2 ^ 59
def prefixEnd_722647 : Nat := 4983230072969 + 3 ^ 40 * 722647 * 2
def baseEnd_722647 : Nat := 371065254529739373989113

theorem tailTrace_722647 : CollatzResearch.WordTrace tailWord_722647 prefixEnd_722647 371065254529739373989113 := by
  unfold tailWord_722647
  simp only [CollatzResearch.WordTrace]
  refine ⟨26357101412980812126878195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17571400941987208084585463 26357101412980812126878195)
  ·
    refine ⟨39535652119471218190317293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26357101412980812126878195 39535652119471218190317293)
    ·
      refine ⟨14825869544801706821368985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39535652119471218190317293 14825869544801706821368985)
      ·
        refine ⟨11119402158601280116026739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14825869544801706821368985 11119402158601280116026739)
        ·
          refine ⟨16679103237901920174040109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11119402158601280116026739 16679103237901920174040109)
          ·
            refine ⟨6254663714213220065265041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16679103237901920174040109 6254663714213220065265041)
            ·
              refine ⟨4690997785659915048948781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6254663714213220065265041 4690997785659915048948781)
              ·
                refine ⟨1759124169622468143355793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4690997785659915048948781 1759124169622468143355793)
                ·
                  refine ⟨1319343127216851107516845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1759124169622468143355793 1319343127216851107516845)
                  ·
                    refine ⟨494753672706319165318817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319343127216851107516845 494753672706319165318817)
                    ·
                      refine ⟨371065254529739373989113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494753672706319165318817 371065254529739373989113)
                      ·
                        rfl

theorem cell23_722647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_722647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722647 prefixEnd_722647 := by exact prefixLift 722647
  have htrace : WordTrace (prefixWord ++ tailWord_722647) baseStart_722647 baseEnd_722647 := by
    simpa [prefixWord, tailWord_722647, baseEnd_722647] using wordTrace_append hprefix tailTrace_722647
  have hstable : (prefixWord ++ tailWord_722647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722647).length < 2 ^ (prefixWord ++ tailWord_722647).sum := by decide
  have hdescent : baseEnd_722647 < baseStart_722647 := by decide
  rcases family_descends (prefixWord ++ tailWord_722647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722664 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_722664 : Nat := 118140960795 + 722664 * 2 ^ 59
def prefixEnd_722664 : Nat := 4983230072969 + 3 ^ 40 * 722664 * 2
def baseEnd_722664 : Nat := 371073983700865807476535

theorem tailTrace_722664 : CollatzResearch.WordTrace tailWord_722664 prefixEnd_722664 371073983700865807476535 := by
  unfold tailWord_722664
  simp only [CollatzResearch.WordTrace]
  refine ⟨13178860726959612015123523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17571814302612816020164697 13178860726959612015123523)
  ·
    refine ⟨19768291090439418022685285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13178860726959612015123523 19768291090439418022685285)
    ·
      refine ⟨3706554579457390879253491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19768291090439418022685285 3706554579457390879253491)
      ·
        refine ⟨5559831869186086318880237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706554579457390879253491 5559831869186086318880237)
        ·
          refine ⟨2084936950944782369580089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5559831869186086318880237 2084936950944782369580089)
          ·
            refine ⟨1563702713208586777185067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2084936950944782369580089 1563702713208586777185067)
            ·
              refine ⟨2345554069812880165777601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563702713208586777185067 2345554069812880165777601)
              ·
                refine ⟨1759165552359660124333201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2345554069812880165777601 1759165552359660124333201)
                ·
                  refine ⟨1319374164269745093249901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1759165552359660124333201 1319374164269745093249901)
                  ·
                    refine ⟨494765311601154409968713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319374164269745093249901 494765311601154409968713)
                    ·
                      refine ⟨371073983700865807476535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494765311601154409968713 371073983700865807476535)
                      ·
                        rfl

theorem cell23_722664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_722664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722664 prefixEnd_722664 := by exact prefixLift 722664
  have htrace : WordTrace (prefixWord ++ tailWord_722664) baseStart_722664 baseEnd_722664 := by
    simpa [prefixWord, tailWord_722664, baseEnd_722664] using wordTrace_append hprefix tailTrace_722664
  have hstable : (prefixWord ++ tailWord_722664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722664).length < 2 ^ (prefixWord ++ tailWord_722664).sum := by decide
  have hdescent : baseEnd_722664 < baseStart_722664 := by decide
  rcases family_descends (prefixWord ++ tailWord_722664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722671 : List Nat := [1, 1, 2, 1, 5, 1, 5, 2, 1, 1, 3]
def baseStart_722671 : Nat := 118140960795 + 722671 * 2 ^ 59
def prefixEnd_722671 : Nat := 4983230072969 + 3 ^ 40 * 722671 * 2
def baseEnd_722671 : Nat := 371077578065447280089003

theorem tailTrace_722671 : CollatzResearch.WordTrace tailWord_722671 prefixEnd_722671 371077578065447280089003 := by
  unfold tailWord_722671
  simp only [CollatzResearch.WordTrace]
  refine ⟨26357976764893864225751867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17571984509929242817167911 26357976764893864225751867)
  ·
    refine ⟨39536965147340796338627801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26357976764893864225751867 39536965147340796338627801)
    ·
      refine ⟨29652723860505597253970851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39536965147340796338627801 29652723860505597253970851)
      ·
        refine ⟨44479085790758395880956277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29652723860505597253970851 44479085790758395880956277)
        ·
          refine ⟨4169914292883599613839651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44479085790758395880956277 4169914292883599613839651)
          ·
            refine ⟨6254871439325399420759477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4169914292883599613839651 6254871439325399420759477)
            ·
              refine ⟨586394197436756195696201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6254871439325399420759477 586394197436756195696201)
              ·
                refine ⟨439795648077567146772151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586394197436756195696201 439795648077567146772151)
                ·
                  refine ⟨659693472116350720158227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439795648077567146772151 659693472116350720158227)
                  ·
                    refine ⟨989540208174526080237341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 659693472116350720158227 989540208174526080237341)
                    ·
                      refine ⟨371077578065447280089003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 989540208174526080237341 371077578065447280089003)
                      ·
                        rfl

theorem cell23_722671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 1, 1, 3].length) (baseStart_722671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722671 prefixEnd_722671 := by exact prefixLift 722671
  have htrace : WordTrace (prefixWord ++ tailWord_722671) baseStart_722671 baseEnd_722671 := by
    simpa [prefixWord, tailWord_722671, baseEnd_722671] using wordTrace_append hprefix tailTrace_722671
  have hstable : (prefixWord ++ tailWord_722671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722671).length < 2 ^ (prefixWord ++ tailWord_722671).sum := by decide
  have hdescent : baseEnd_722671 < baseStart_722671 := by decide
  rcases family_descends (prefixWord ++ tailWord_722671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722728 : List Nat := [2, 1, 5, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_722728 : Nat := 118140960795 + 722728 * 2 ^ 59
def prefixEnd_722728 : Nat := 4983230072969 + 3 ^ 40 * 722728 * 2
def baseEnd_722728 : Nat := 371106846462753557076241

theorem tailTrace_722728 : CollatzResearch.WordTrace tailWord_722728 prefixEnd_722728 371106846462753557076241 := by
  unfold tailWord_722728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13180027862843681480288419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17573370483791575307051225 13180027862843681480288419)
  ·
    refine ⟨19770041794265522220432629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13180027862843681480288419 19770041794265522220432629)
    ·
      refine ⟨1853441418212392708165559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19770041794265522220432629 1853441418212392708165559)
      ·
        refine ⟨2780162127318589062248339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853441418212392708165559 2780162127318589062248339)
        ·
          refine ⟨4170243190977883593372509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2780162127318589062248339 4170243190977883593372509)
          ·
            refine ⟨1563841196616706347514691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4170243190977883593372509 1563841196616706347514691)
            ·
              refine ⟨2345761794925059521272037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563841196616706347514691 2345761794925059521272037)
              ·
                refine ⟨439830336548448660238507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2345761794925059521272037 439830336548448660238507)
                ·
                  refine ⟨659745504822672990357761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439830336548448660238507 659745504822672990357761)
                  ·
                    refine ⟨494809128617004742768321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 659745504822672990357761 494809128617004742768321)
                    ·
                      refine ⟨371106846462753557076241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494809128617004742768321 371106846462753557076241)
                      ·
                        rfl

theorem cell23_722728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_722728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722728 prefixEnd_722728 := by exact prefixLift 722728
  have htrace : WordTrace (prefixWord ++ tailWord_722728) baseStart_722728 baseEnd_722728 := by
    simpa [prefixWord, tailWord_722728, baseEnd_722728] using wordTrace_append hprefix tailTrace_722728
  have hstable : (prefixWord ++ tailWord_722728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722728).length < 2 ^ (prefixWord ++ tailWord_722728).sum := by decide
  have hdescent : baseEnd_722728 < baseStart_722728 := by decide
  rcases family_descends (prefixWord ++ tailWord_722728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722734 : List Nat := [4, 1, 3, 2, 2, 2, 1, 8]
def baseStart_722734 : Nat := 118140960795 + 722734 * 2 ^ 59
def prefixEnd_722734 : Nat := 4983230072969 + 3 ^ 40 * 722734 * 2
def baseEnd_722734 : Nat := 13744812123951130874119

theorem tailTrace_722734 : CollatzResearch.WordTrace tailWord_722734 prefixEnd_722734 13744812123951130874119 := by
  unfold tailWord_722734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295034320458203248161907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17573516375777083990196837 3295034320458203248161907)
  ·
    refine ⟨4942551480687304872242861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3295034320458203248161907 4942551480687304872242861)
    ·
      refine ⟨1853456805257739327091073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4942551480687304872242861 1853456805257739327091073)
      ·
        refine ⟨1390092603943304495318305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1853456805257739327091073 1390092603943304495318305)
        ·
          refine ⟨1042569452957478371488729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1390092603943304495318305 1042569452957478371488729)
          ·
            refine ⟨781927089718108778616547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1042569452957478371488729 781927089718108778616547)
            ·
              refine ⟨1172890634577163167924821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781927089718108778616547 1172890634577163167924821)
              ·
                refine ⟨13744812123951130874119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1172890634577163167924821 13744812123951130874119)
                ·
                  rfl

theorem cell23_722734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_722734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722734 prefixEnd_722734 := by exact prefixLift 722734
  have htrace : WordTrace (prefixWord ++ tailWord_722734) baseStart_722734 baseEnd_722734 := by
    simpa [prefixWord, tailWord_722734, baseEnd_722734] using wordTrace_append hprefix tailTrace_722734
  have hstable : (prefixWord ++ tailWord_722734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722734).length < 2 ^ (prefixWord ++ tailWord_722734).sum := by decide
  have hdescent : baseEnd_722734 < baseStart_722734 := by decide
  rcases family_descends (prefixWord ++ tailWord_722734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722744 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 2, 1, 3]
def baseStart_722744 : Nat := 118140960795 + 722744 * 2 ^ 59
def prefixEnd_722744 : Nat := 4983230072969 + 3 ^ 40 * 722744 * 2
def baseEnd_722744 : Nat := 371115062153225494476167

theorem tailTrace_722744 : CollatzResearch.WordTrace tailWord_722744 prefixEnd_722744 371115062153225494476167 := by
  unfold tailWord_722744
  simp only [CollatzResearch.WordTrace]
  refine ⟨13180319646814698846579643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17573759529086265128772857 13180319646814698846579643)
  ·
    refine ⟨19770479470222048269869465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13180319646814698846579643 19770479470222048269869465)
    ·
      refine ⟨14827859602666536202402099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19770479470222048269869465 14827859602666536202402099)
      ·
        refine ⟨22241789403999804303603149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14827859602666536202402099 22241789403999804303603149)
        ·
          refine ⟨8340671026499926613851181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22241789403999804303603149 8340671026499926613851181)
          ·
            refine ⟨3127751634937472480194193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8340671026499926613851181 3127751634937472480194193)
            ·
              refine ⟨2345813726203104360145645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3127751634937472480194193 2345813726203104360145645)
              ·
                refine ⟨879680147326164135054617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2345813726203104360145645 879680147326164135054617)
                ·
                  refine ⟨659760110494623101290963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 879680147326164135054617 659760110494623101290963)
                  ·
                    refine ⟨989640165741934651936445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 659760110494623101290963 989640165741934651936445)
                    ·
                      refine ⟨371115062153225494476167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 989640165741934651936445 371115062153225494476167)
                      ·
                        rfl

theorem cell23_722744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_722744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722744 prefixEnd_722744 := by exact prefixLift 722744
  have htrace : WordTrace (prefixWord ++ tailWord_722744) baseStart_722744 baseEnd_722744 := by
    simpa [prefixWord, tailWord_722744, baseEnd_722744] using wordTrace_append hprefix tailTrace_722744
  have hstable : (prefixWord ++ tailWord_722744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722744).length < 2 ^ (prefixWord ++ tailWord_722744).sum := by decide
  have hdescent : baseEnd_722744 < baseStart_722744 := by decide
  rcases family_descends (prefixWord ++ tailWord_722744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722797 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_722797 : Nat := 118140960795 + 722797 * 2 ^ 59
def prefixEnd_722797 : Nat := 4983230072969 + 3 ^ 40 * 722797 * 2
def baseEnd_722797 : Nat := 371142276627913787113423

theorem tailTrace_722797 : CollatzResearch.WordTrace tailWord_722797 prefixEnd_722797 371142276627913787113423 := by
  unfold tailWord_722797
  simp only [CollatzResearch.WordTrace]
  refine ⟨26362572362437387744838645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17575048241624925163225763 26362572362437387744838645)
  ·
    refine ⟨2471491158978505101078623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26362572362437387744838645 2471491158978505101078623)
    ·
      refine ⟨3707236738467757651617935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2471491158978505101078623 3707236738467757651617935)
      ·
        refine ⟨5560855107701636477426903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3707236738467757651617935 5560855107701636477426903)
        ·
          refine ⟨8341282661552454716140355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560855107701636477426903 8341282661552454716140355)
          ·
            refine ⟨12511923992328682074210533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8341282661552454716140355 12511923992328682074210533)
            ·
              refine ⟨2345985748561627888914475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12511923992328682074210533 2345985748561627888914475)
              ·
                refine ⟨3518978622842441833371713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345985748561627888914475 3518978622842441833371713)
                ·
                  refine ⟨2639233967131831375028785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3518978622842441833371713 2639233967131831375028785)
                  ·
                    refine ⟨1979425475348873531271589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2639233967131831375028785 1979425475348873531271589)
                    ·
                      refine ⟨371142276627913787113423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1979425475348873531271589 371142276627913787113423)
                      ·
                        rfl

theorem cell23_722797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_722797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722797 prefixEnd_722797 := by exact prefixLift 722797
  have htrace : WordTrace (prefixWord ++ tailWord_722797) baseStart_722797 baseEnd_722797 := by
    simpa [prefixWord, tailWord_722797, baseEnd_722797] using wordTrace_append hprefix tailTrace_722797
  have hstable : (prefixWord ++ tailWord_722797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722797).length < 2 ^ (prefixWord ++ tailWord_722797).sum := by decide
  have hdescent : baseEnd_722797 < baseStart_722797 := by decide
  rcases family_descends (prefixWord ++ tailWord_722797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722827 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 1, 7, 2]
def baseStart_722827 : Nat := 118140960795 + 722827 * 2 ^ 59
def prefixEnd_722827 : Nat := 4983230072969 + 3 ^ 40 * 722827 * 2
def baseEnd_722827 : Nat := 371157681047548669738285

theorem tailTrace_722827 : CollatzResearch.WordTrace tailWord_722827 prefixEnd_722827 371157681047548669738285 := by
  unfold tailWord_722827
  simp only [CollatzResearch.WordTrace]
  refine ⟨26363666552328702868430735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17575777701552468578953823 26363666552328702868430735)
  ·
    refine ⟨39545499828493054302646103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26363666552328702868430735 39545499828493054302646103)
    ·
      refine ⟨59318249742739581453969155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39545499828493054302646103 59318249742739581453969155)
      ·
        refine ⟨88977374614109372180953733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59318249742739581453969155 88977374614109372180953733)
        ·
          refine ⟨16683257740145507283928825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88977374614109372180953733 16683257740145507283928825)
          ·
            refine ⟨12512443305109130462946619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16683257740145507283928825 12512443305109130462946619)
            ·
              refine ⟨18768664957663695694419929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12512443305109130462946619 18768664957663695694419929)
              ·
                refine ⟨14076498718247771770814947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18768664957663695694419929 14076498718247771770814947)
                ·
                  refine ⟨21114748077371657656222421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14076498718247771770814947 21114748077371657656222421)
                  ·
                    refine ⟨494876908063398226317713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21114748077371657656222421 494876908063398226317713)
                    ·
                      refine ⟨371157681047548669738285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494876908063398226317713 371157681047548669738285)
                      ·
                        rfl

theorem cell23_722827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 7, 2].length) (baseStart_722827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722827 prefixEnd_722827 := by exact prefixLift 722827
  have htrace : WordTrace (prefixWord ++ tailWord_722827) baseStart_722827 baseEnd_722827 := by
    simpa [prefixWord, tailWord_722827, baseEnd_722827] using wordTrace_append hprefix tailTrace_722827
  have hstable : (prefixWord ++ tailWord_722827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722827).length < 2 ^ (prefixWord ++ tailWord_722827).sum := by decide
  have hdescent : baseEnd_722827 < baseStart_722827 := by decide
  rcases family_descends (prefixWord ++ tailWord_722827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722837 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_722837 : Nat := 118140960795 + 722837 * 2 ^ 59
def prefixEnd_722837 : Nat := 4983230072969 + 3 ^ 40 * 722837 * 2
def baseEnd_722837 : Nat := 123720938618031210204413

theorem tailTrace_722837 : CollatzResearch.WordTrace tailWord_722837 prefixEnd_722837 123720938618031210204413 := by
  unfold tailWord_722837
  simp only [CollatzResearch.WordTrace]
  refine ⟨26364031282292474576294765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17576020854861649717529843 26364031282292474576294765)
  ·
    refine ⟨9886511730859677966110537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26364031282292474576294765 9886511730859677966110537)
    ·
      refine ⟨7414883798144758474582903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9886511730859677966110537 7414883798144758474582903)
      ·
        refine ⟨11122325697217137711874355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7414883798144758474582903 11122325697217137711874355)
        ·
          refine ⟨16683488545825706567811533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11122325697217137711874355 16683488545825706567811533)
          ·
            refine ⟨6256308204684639962929325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16683488545825706567811533 6256308204684639962929325)
            ·
              refine ⟨2346115576756739986098497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6256308204684639962929325 2346115576756739986098497)
              ·
                refine ⟨1759586682567554989573873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2346115576756739986098497 1759586682567554989573873)
                ·
                  refine ⟨1319690011925666242180405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1759586682567554989573873 1319690011925666242180405)
                  ·
                    refine ⟨123720938618031210204413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1319690011925666242180405 123720938618031210204413)
                    ·
                      rfl

theorem cell23_722837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_722837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722837 prefixEnd_722837 := by exact prefixLift 722837
  have htrace : WordTrace (prefixWord ++ tailWord_722837) baseStart_722837 baseEnd_722837 := by
    simpa [prefixWord, tailWord_722837, baseEnd_722837] using wordTrace_append hprefix tailTrace_722837
  have hstable : (prefixWord ++ tailWord_722837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722837).length < 2 ^ (prefixWord ++ tailWord_722837).sum := by decide
  have hdescent : baseEnd_722837 < baseStart_722837 := by decide
  rcases family_descends (prefixWord ++ tailWord_722837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722867 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 5, 4]
def baseStart_722867 : Nat := 118140960795 + 722867 * 2 ^ 59
def prefixEnd_722867 : Nat := 4983230072969 + 3 ^ 40 * 722867 * 2
def baseEnd_722867 : Nat := 123726073424576171079367

theorem tailTrace_722867 : CollatzResearch.WordTrace tailWord_722867 prefixEnd_722867 123726073424576171079367 := by
  unfold tailWord_722867
  simp only [CollatzResearch.WordTrace]
  refine ⟨26365125472183789699886855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17576750314789193133257903 26365125472183789699886855)
  ·
    refine ⟨39547688208275684549830283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26365125472183789699886855 39547688208275684549830283)
    ·
      refine ⟨59321532312413526824745425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39547688208275684549830283 59321532312413526824745425)
      ·
        refine ⟨44491149234310145118559069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59321532312413526824745425 44491149234310145118559069)
        ·
          refine ⟨16684180962866304419459651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44491149234310145118559069 16684180962866304419459651)
          ·
            refine ⟨25026271444299456629189477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16684180962866304419459651 25026271444299456629189477)
            ·
              refine ⟨4692425895806148117973027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25026271444299456629189477 4692425895806148117973027)
              ·
                refine ⟨7038638843709222176959541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4692425895806148117973027 7038638843709222176959541)
                ·
                  refine ⟨659872391597739579089957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7038638843709222176959541 659872391597739579089957)
                  ·
                    refine ⟨123726073424576171079367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659872391597739579089957 123726073424576171079367)
                    ·
                      rfl

theorem cell23_722867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 4].length) (baseStart_722867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722867 prefixEnd_722867 := by exact prefixLift 722867
  have htrace : WordTrace (prefixWord ++ tailWord_722867) baseStart_722867 baseEnd_722867 := by
    simpa [prefixWord, tailWord_722867, baseEnd_722867] using wordTrace_append hprefix tailTrace_722867
  have hstable : (prefixWord ++ tailWord_722867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722867).length < 2 ^ (prefixWord ++ tailWord_722867).sum := by decide
  have hdescent : baseEnd_722867 < baseStart_722867 := by decide
  rcases family_descends (prefixWord ++ tailWord_722867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722894 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_722894 : Nat := 118140960795 + 722894 * 2 ^ 59
def prefixEnd_722894 : Nat := 4983230072969 + 3 ^ 40 * 722894 * 2
def baseEnd_722894 : Nat := 371192084251399907600477

theorem tailTrace_722894 : CollatzResearch.WordTrace tailWord_722894 prefixEnd_722894 371192084251399907600477 := by
  unfold tailWord_722894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295763780385746663889967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17577406828723982207413157 3295763780385746663889967)
  ·
    refine ⟨4943645670578619995834951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3295763780385746663889967 4943645670578619995834951)
    ·
      refine ⟨7415468505867929993752427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4943645670578619995834951 7415468505867929993752427)
      ·
        refine ⟨11123202758801894990628641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7415468505867929993752427 11123202758801894990628641)
        ·
          refine ⟨8342402069101421242971481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11123202758801894990628641 8342402069101421242971481)
          ·
            refine ⟨6256801551826065932228611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8342402069101421242971481 6256801551826065932228611)
            ·
              refine ⟨9385202327739098898342917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6256801551826065932228611 9385202327739098898342917)
              ·
                refine ⟨1759725436451081043439297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9385202327739098898342917 1759725436451081043439297)
                ·
                  refine ⟨1319794077338310782579473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1759725436451081043439297 1319794077338310782579473)
                  ·
                    refine ⟨989845558003733086934605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1319794077338310782579473 989845558003733086934605)
                    ·
                      refine ⟨371192084251399907600477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 989845558003733086934605 371192084251399907600477)
                      ·
                        rfl

theorem cell23_722894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_722894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722894 prefixEnd_722894 := by exact prefixLift 722894
  have htrace : WordTrace (prefixWord ++ tailWord_722894) baseStart_722894 baseEnd_722894 := by
    simpa [prefixWord, tailWord_722894, baseEnd_722894] using wordTrace_append hprefix tailTrace_722894
  have hstable : (prefixWord ++ tailWord_722894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722894).length < 2 ^ (prefixWord ++ tailWord_722894).sum := by decide
  have hdescent : baseEnd_722894 < baseStart_722894 := by decide
  rcases family_descends (prefixWord ++ tailWord_722894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722925 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_722925 : Nat := 118140960795 + 722925 * 2 ^ 59
def prefixEnd_722925 : Nat := 4983230072969 + 3 ^ 40 * 722925 * 2
def baseEnd_722925 : Nat := 371208002151689286312835

theorem tailTrace_722925 : CollatzResearch.WordTrace tailWord_722925 prefixEnd_722925 371208002151689286312835 := by
  unfold tailWord_722925
  simp only [CollatzResearch.WordTrace]
  refine ⟨26367240905973665605498229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17578160603982443736998819 26367240905973665605498229)
  ·
    refine ⟨2471928834935031150515459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26367240905973665605498229 2471928834935031150515459)
    ·
      refine ⟨3707893252402546725773189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2471928834935031150515459 3707893252402546725773189)
      ·
        refine ⟨695229984825477511082473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3707893252402546725773189 695229984825477511082473)
        ·
          refine ⟨521422488619108133311855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 695229984825477511082473 521422488619108133311855)
          ·
            refine ⟨782133732928662199967783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521422488619108133311855 782133732928662199967783)
            ·
              refine ⟨1173200599392993299951675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782133732928662199967783 1173200599392993299951675)
              ·
                refine ⟨1759800899089489949927513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173200599392993299951675 1759800899089489949927513)
                ·
                  refine ⟨1319850674317117462445635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1759800899089489949927513 1319850674317117462445635)
                  ·
                    refine ⟨1979776011475676193668453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1319850674317117462445635 1979776011475676193668453)
                    ·
                      refine ⟨371208002151689286312835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1979776011475676193668453 371208002151689286312835)
                      ·
                        rfl

theorem cell23_722925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_722925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722925 prefixEnd_722925 := by exact prefixLift 722925
  have htrace : WordTrace (prefixWord ++ tailWord_722925) baseStart_722925 baseEnd_722925 := by
    simpa [prefixWord, tailWord_722925, baseEnd_722925] using wordTrace_append hprefix tailTrace_722925
  have hstable : (prefixWord ++ tailWord_722925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722925).length < 2 ^ (prefixWord ++ tailWord_722925).sum := by decide
  have hdescent : baseEnd_722925 < baseStart_722925 := by decide
  rcases family_descends (prefixWord ++ tailWord_722925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722927 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 3, 5]
def baseStart_722927 : Nat := 118140960795 + 722927 * 2 ^ 59
def prefixEnd_722927 : Nat := 4983230072969 + 3 ^ 40 * 722927 * 2
def baseEnd_722927 : Nat := 123736343037666092829275

theorem tailTrace_722927 : CollatzResearch.WordTrace tailWord_722927 prefixEnd_722927 123736343037666092829275 := by
  unfold tailWord_722927
  simp only [CollatzResearch.WordTrace]
  refine ⟨26367313851966419947071035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17578209234644279964714023 26367313851966419947071035)
  ·
    refine ⟨39550970777949629920606553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26367313851966419947071035 39550970777949629920606553)
    ·
      refine ⟨29663228083462222440454915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39550970777949629920606553 29663228083462222440454915)
      ·
        refine ⟨44494842125193333660682373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29663228083462222440454915 44494842125193333660682373)
        ·
          refine ⟨8342782898473750061377945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44494842125193333660682373 8342782898473750061377945)
          ·
            refine ⟨6257087173855312546033459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8342782898473750061377945 6257087173855312546033459)
            ·
              refine ⟨9385630760782968819050189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257087173855312546033459 9385630760782968819050189)
              ·
                refine ⟨3519611535293613307143821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9385630760782968819050189 3519611535293613307143821)
                ·
                  refine ⟨1319854325735104990178933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3519611535293613307143821 1319854325735104990178933)
                  ·
                    refine ⟨123736343037666092829275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1319854325735104990178933 123736343037666092829275)
                    ·
                      rfl

theorem cell23_722927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_722927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722927 prefixEnd_722927 := by exact prefixLift 722927
  have htrace : WordTrace (prefixWord ++ tailWord_722927) baseStart_722927 baseEnd_722927 := by
    simpa [prefixWord, tailWord_722927, baseEnd_722927] using wordTrace_append hprefix tailTrace_722927
  have hstable : (prefixWord ++ tailWord_722927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722927).length < 2 ^ (prefixWord ++ tailWord_722927).sum := by decide
  have hdescent : baseEnd_722927 < baseStart_722927 := by decide
  rcases family_descends (prefixWord ++ tailWord_722927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722948 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 6]
def baseStart_722948 : Nat := 118140960795 + 722948 * 2 ^ 59
def prefixEnd_722948 : Nat := 4983230072969 + 3 ^ 40 * 722948 * 2
def baseEnd_722948 : Nat := 41246645800749188480581

theorem tailTrace_722948 : CollatzResearch.WordTrace tailWord_722948 prefixEnd_722948 41246645800749188480581 := by
  unfold tailWord_722948
  simp only [CollatzResearch.WordTrace]
  refine ⟨13184039892445170266792749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17578719856593560355723665 13184039892445170266792749)
  ·
    refine ⟨4944014959666938850047281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13184039892445170266792749 4944014959666938850047281)
    ·
      refine ⟨3708011219750204137535461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4944014959666938850047281 3708011219750204137535461)
      ·
        refine ⟨695252103703163275787899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3708011219750204137535461 695252103703163275787899)
        ·
          refine ⟨1042878155554744913681849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695252103703163275787899 1042878155554744913681849)
          ·
            refine ⟨782158616666058685261387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1042878155554744913681849 782158616666058685261387)
            ·
              refine ⟨1173237924999088027892081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782158616666058685261387 1173237924999088027892081)
              ·
                refine ⟨879928443749316020919061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173237924999088027892081 879928443749316020919061)
                ·
                  refine ⟨41246645800749188480581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 879928443749316020919061 41246645800749188480581)
                  ·
                    rfl

theorem cell23_722948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_722948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722948 prefixEnd_722948 := by exact prefixLift 722948
  have htrace : WordTrace (prefixWord ++ tailWord_722948) baseStart_722948 baseEnd_722948 := by
    simpa [prefixWord, tailWord_722948, baseEnd_722948] using wordTrace_append hprefix tailTrace_722948
  have hstable : (prefixWord ++ tailWord_722948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722948).length < 2 ^ (prefixWord ++ tailWord_722948).sum := by decide
  have hdescent : baseEnd_722948 < baseStart_722948 := by decide
  rcases family_descends (prefixWord ++ tailWord_722948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722958 : List Nat := [4, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3]
def baseStart_722958 : Nat := 118140960795 + 722958 * 2 ^ 59
def prefixEnd_722958 : Nat := 4983230072969 + 3 ^ 40 * 722958 * 2
def baseEnd_722958 : Nat := 371224947013287657200183

theorem tailTrace_722958 : CollatzResearch.WordTrace tailWord_722958 prefixEnd_722958 371224947013287657200183 := by
  unfold tailWord_722958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296055564356764030181191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17578963009902741494299685 3296055564356764030181191)
  ·
    refine ⟨4944083346535146045271787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3296055564356764030181191 4944083346535146045271787)
    ·
      refine ⟨7416125019802719067907681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4944083346535146045271787 7416125019802719067907681)
      ·
        refine ⟨5562093764852039300930761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7416125019802719067907681 5562093764852039300930761)
        ·
          refine ⟨4171570323639029475698071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5562093764852039300930761 4171570323639029475698071)
          ·
            refine ⟨6257355485458544213547107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171570323639029475698071 6257355485458544213547107)
            ·
              refine ⟨9386033228187816320320661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257355485458544213547107 9386033228187816320320661)
              ·
                refine ⟨439970307571303890015031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9386033228187816320320661 439970307571303890015031)
                ·
                  refine ⟨659955461356955835022547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439970307571303890015031 659955461356955835022547)
                  ·
                    refine ⟨989933192035433752533821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 659955461356955835022547 989933192035433752533821)
                    ·
                      refine ⟨371224947013287657200183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 989933192035433752533821 371224947013287657200183)
                      ·
                        rfl

theorem cell23_722958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_722958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722958 prefixEnd_722958 := by exact prefixLift 722958
  have htrace : WordTrace (prefixWord ++ tailWord_722958) baseStart_722958 baseEnd_722958 := by
    simpa [prefixWord, tailWord_722958, baseEnd_722958] using wordTrace_append hprefix tailTrace_722958
  have hstable : (prefixWord ++ tailWord_722958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722958).length < 2 ^ (prefixWord ++ tailWord_722958).sum := by decide
  have hdescent : baseEnd_722958 < baseStart_722958 := by decide
  rcases family_descends (prefixWord ++ tailWord_722958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722981 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 4]
def baseStart_722981 : Nat := 118140960795 + 722981 * 2 ^ 59
def prefixEnd_722981 : Nat := 4983230072969 + 3 ^ 40 * 722981 * 2
def baseEnd_722981 : Nat := 371236757068341067212577

theorem tailTrace_722981 : CollatzResearch.WordTrace tailWord_722981 prefixEnd_722981 371236757068341067212577 := by
  unfold tailWord_722981
  simp only [CollatzResearch.WordTrace]
  refine ⟨26369283393770787169536797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17579522262513858113024531 26369283393770787169536797)
  ·
    refine ⟨9888481272664045188576299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26369283393770787169536797 9888481272664045188576299)
    ·
      refine ⟨14832721908996067782864449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9888481272664045188576299 14832721908996067782864449)
      ·
        refine ⟨11124541431747050837148337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14832721908996067782864449 11124541431747050837148337)
        ·
          refine ⟨8343406073810288127861253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11124541431747050837148337 8343406073810288127861253)
          ·
            refine ⟨1564388638839429023973985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8343406073810288127861253 1564388638839429023973985)
            ·
              refine ⟨1173291479129571767980489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1564388638839429023973985 1173291479129571767980489)
              ·
                refine ⟨879968609347178825985367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173291479129571767980489 879968609347178825985367)
                ·
                  refine ⟨1319952914020768238978051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879968609347178825985367 1319952914020768238978051)
                  ·
                    refine ⟨1979929371031152358467077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1319952914020768238978051 1979929371031152358467077)
                    ·
                      refine ⟨371236757068341067212577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1979929371031152358467077 371236757068341067212577)
                      ·
                        rfl

theorem cell23_722981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_722981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722981 prefixEnd_722981 := by exact prefixLift 722981
  have htrace : WordTrace (prefixWord ++ tailWord_722981) baseStart_722981 baseEnd_722981 := by
    simpa [prefixWord, tailWord_722981, baseEnd_722981] using wordTrace_append hprefix tailTrace_722981
  have hstable : (prefixWord ++ tailWord_722981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722981).length < 2 ^ (prefixWord ++ tailWord_722981).sum := by decide
  have hdescent : baseEnd_722981 < baseStart_722981 := by decide
  rcases family_descends (prefixWord ++ tailWord_722981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723001 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 5]
def baseStart_723001 : Nat := 118140960795 + 723001 * 2 ^ 59
def prefixEnd_723001 : Nat := 4983230072969 + 3 ^ 40 * 723001 * 2
def baseEnd_723001 : Nat := 371247026681430988962485

theorem tailTrace_723001 : CollatzResearch.WordTrace tailWord_723001 prefixEnd_723001 371247026681430988962485 := by
  unfold tailWord_723001
  simp only [CollatzResearch.WordTrace]
  refine ⟨26370012853698330585264857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17580008569132220390176571 26370012853698330585264857)
  ·
    refine ⟨19777509640273747938948643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26370012853698330585264857 19777509640273747938948643)
    ·
      refine ⟨29666264460410621908422965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19777509640273747938948643 29666264460410621908422965)
      ·
        refine ⟨2781212293163495803914653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29666264460410621908422965 2781212293163495803914653)
        ·
          refine ⟨1042954609936310926467995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2781212293163495803914653 1042954609936310926467995)
          ·
            refine ⟨1564431914904466389701993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042954609936310926467995 1564431914904466389701993)
            ·
              refine ⟨1173323936178349792276495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1564431914904466389701993 1173323936178349792276495)
              ·
                refine ⟨1759985904267524688414743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173323936178349792276495 1759985904267524688414743)
                ·
                  refine ⟨2639978856401287032622115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759985904267524688414743 2639978856401287032622115)
                  ·
                    refine ⟨3959968284601930548933173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2639978856401287032622115 3959968284601930548933173)
                    ·
                      refine ⟨371247026681430988962485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3959968284601930548933173 371247026681430988962485)
                      ·
                        rfl

theorem cell23_723001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_723001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723001 prefixEnd_723001 := by exact prefixLift 723001
  have htrace : WordTrace (prefixWord ++ tailWord_723001) baseStart_723001 baseEnd_723001 := by
    simpa [prefixWord, tailWord_723001, baseEnd_723001] using wordTrace_append hprefix tailTrace_723001
  have hstable : (prefixWord ++ tailWord_723001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723001).length < 2 ^ (prefixWord ++ tailWord_723001).sum := by decide
  have hdescent : baseEnd_723001 < baseStart_723001 := by decide
  rcases family_descends (prefixWord ++ tailWord_723001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723017 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 2, 7]
def baseStart_723017 : Nat := 118140960795 + 723017 * 2 ^ 59
def prefixEnd_723017 : Nat := 4983230072969 + 3 ^ 40 * 723017 * 2
def baseEnd_723017 : Nat := 123751747457300975454137

theorem tailTrace_723017 : CollatzResearch.WordTrace tailWord_723017 prefixEnd_723017 123751747457300975454137 := by
  unfold tailWord_723017
  simp only [CollatzResearch.WordTrace]
  refine ⟨26370596421640365317847305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17580397614426910211898203 26370596421640365317847305)
  ·
    refine ⟨19777947316230273988385479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26370596421640365317847305 19777947316230273988385479)
    ·
      refine ⟨29666920974345410982578219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19777947316230273988385479 29666920974345410982578219)
      ·
        refine ⟨44500381461518116473867329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29666920974345410982578219 44500381461518116473867329)
        ·
          refine ⟨33375286096138587355400497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44500381461518116473867329 33375286096138587355400497)
          ·
            refine ⟨25031464572103940516550373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33375286096138587355400497 25031464572103940516550373)
            ·
              refine ⟨4693399607269488846853195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25031464572103940516550373 4693399607269488846853195)
              ·
                refine ⟨7040099410904233270279793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4693399607269488846853195 7040099410904233270279793)
                ·
                  refine ⟨5280074558178174952709845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7040099410904233270279793 5280074558178174952709845)
                  ·
                    refine ⟨123751747457300975454137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5280074558178174952709845 123751747457300975454137)
                    ·
                      rfl

theorem cell23_723017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_723017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723017 prefixEnd_723017 := by exact prefixLift 723017
  have htrace : WordTrace (prefixWord ++ tailWord_723017) baseStart_723017 baseEnd_723017 := by
    simpa [prefixWord, tailWord_723017, baseEnd_723017] using wordTrace_append hprefix tailTrace_723017
  have hstable : (prefixWord ++ tailWord_723017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723017).length < 2 ^ (prefixWord ++ tailWord_723017).sum := by decide
  have hdescent : baseEnd_723017 < baseStart_723017 := by decide
  rcases family_descends (prefixWord ++ tailWord_723017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723024 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 1, 9, 2]
def baseStart_723024 : Nat := 118140960795 + 723024 * 2 ^ 59
def prefixEnd_723024 : Nat := 4983230072969 + 3 ^ 40 * 723024 * 2
def baseEnd_723024 : Nat := 371258836736484398974879

theorem tailTrace_723024 : CollatzResearch.WordTrace tailWord_723024 prefixEnd_723024 371258836736484398974879 := by
  unfold tailWord_723024
  simp only [CollatzResearch.WordTrace]
  refine ⟨13185425866307502756676063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17580567821743337008901417 13185425866307502756676063)
  ·
    refine ⟨19778138799461254135014095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13185425866307502756676063 19778138799461254135014095)
    ·
      refine ⟨29667208199191881202521143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19778138799461254135014095 29667208199191881202521143)
      ·
        refine ⟨44500812298787821803781715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29667208199191881202521143 44500812298787821803781715)
        ·
          refine ⟨66751218448181732705672573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44500812298787821803781715 66751218448181732705672573)
          ·
            refine ⟨25031706918068149764627215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66751218448181732705672573 25031706918068149764627215)
            ·
              refine ⟨37547560377102224646940823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25031706918068149764627215 37547560377102224646940823)
              ·
                refine ⟨56321340565653336970411235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37547560377102224646940823 56321340565653336970411235)
                ·
                  refine ⟨84482010848480005455616853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56321340565653336970411235 84482010848480005455616853)
                  ·
                    refine ⟨495011782315312531966505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 84482010848480005455616853 495011782315312531966505)
                    ·
                      refine ⟨371258836736484398974879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 495011782315312531966505 371258836736484398974879)
                      ·
                        rfl

theorem cell23_723024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 9, 2].length) (baseStart_723024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723024 prefixEnd_723024 := by exact prefixLift 723024
  have htrace : WordTrace (prefixWord ++ tailWord_723024) baseStart_723024 baseEnd_723024 := by
    simpa [prefixWord, tailWord_723024, baseEnd_723024] using wordTrace_append hprefix tailTrace_723024
  have hstable : (prefixWord ++ tailWord_723024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723024).length < 2 ^ (prefixWord ++ tailWord_723024).sum := by decide
  have hdescent : baseEnd_723024 < baseStart_723024 := by decide
  rcases family_descends (prefixWord ++ tailWord_723024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723067 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 6]
def baseStart_723067 : Nat := 118140960795 + 723067 * 2 ^ 59
def prefixEnd_723067 : Nat := 4983230072969 + 3 ^ 40 * 723067 * 2
def baseEnd_723067 : Nat := 371280916404627730737181

theorem tailTrace_723067 : CollatzResearch.WordTrace tailWord_723067 prefixEnd_723067 371280916404627730737181 := by
  unfold tailWord_723067
  simp only [CollatzResearch.WordTrace]
  refine ⟨26372420071459223857167455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17581613380972815904778303 26372420071459223857167455)
  ·
    refine ⟨39558630107188835785751183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26372420071459223857167455 39558630107188835785751183)
    ·
      refine ⟨59337945160783253678626775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39558630107188835785751183 59337945160783253678626775)
      ·
        refine ⟨89006917741174880517940163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59337945160783253678626775 89006917741174880517940163)
        ·
          refine ⟨133510376611762320776910245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89006917741174880517940163 133510376611762320776910245)
          ·
            refine ⟨25033195614705435145670671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133510376611762320776910245 25033195614705435145670671)
            ·
              refine ⟨37549793422058152718506007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25033195614705435145670671 37549793422058152718506007)
              ·
                refine ⟨56324690133087229077759011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37549793422058152718506007 56324690133087229077759011)
                ·
                  refine ⟨84487035199630843616638517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56324690133087229077759011 84487035199630843616638517)
                  ·
                    refine ⟨7920659549965391589059861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84487035199630843616638517 7920659549965391589059861)
                    ·
                      refine ⟨371280916404627730737181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7920659549965391589059861 371280916404627730737181)
                      ·
                        rfl

theorem cell23_723067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_723067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723067 prefixEnd_723067 := by exact prefixLift 723067
  have htrace : WordTrace (prefixWord ++ tailWord_723067) baseStart_723067 baseEnd_723067 := by
    simpa [prefixWord, tailWord_723067, baseEnd_723067] using wordTrace_append hprefix tailTrace_723067
  have hstable : (prefixWord ++ tailWord_723067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723067).length < 2 ^ (prefixWord ++ tailWord_723067).sum := by decide
  have hdescent : baseEnd_723067 < baseStart_723067 := by decide
  rcases family_descends (prefixWord ++ tailWord_723067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723088 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 2, 2, 2]
def baseStart_723088 : Nat := 118140960795 + 723088 * 2 ^ 59
def prefixEnd_723088 : Nat := 4983230072969 + 3 ^ 40 * 723088 * 2
def baseEnd_723088 : Nat := 371291699498372148574585

theorem tailTrace_723088 : CollatzResearch.WordTrace tailWord_723088 prefixEnd_723088 371291699498372148574585 := by
  unfold tailWord_723088
  simp only [CollatzResearch.WordTrace]
  refine ⟨13186593002191572221840959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17582124002922096295787945 13186593002191572221840959)
  ·
    refine ⟨19779889503287358332761439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13186593002191572221840959 19779889503287358332761439)
    ·
      refine ⟨29669834254931037499142159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19779889503287358332761439 29669834254931037499142159)
      ·
        refine ⟨44504751382396556248713239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29669834254931037499142159 44504751382396556248713239)
        ·
          refine ⟨66757127073594834373069859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44504751382396556248713239 66757127073594834373069859)
          ·
            refine ⟨100135690610392251559604789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66757127073594834373069859 100135690610392251559604789)
            ·
              refine ⟨9387720994724273583712949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100135690610392251559604789 9387720994724273583712949)
              ·
                refine ⟨880098843255400648473089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9387720994724273583712949 880098843255400648473089)
                ·
                  refine ⟨660074132441550486354817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 880098843255400648473089 660074132441550486354817)
                  ·
                    refine ⟨495055599331162864766113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 660074132441550486354817 495055599331162864766113)
                    ·
                      refine ⟨371291699498372148574585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 495055599331162864766113 371291699498372148574585)
                      ·
                        rfl

theorem cell23_723088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2, 2, 2].length) (baseStart_723088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723088 prefixEnd_723088 := by exact prefixLift 723088
  have htrace : WordTrace (prefixWord ++ tailWord_723088) baseStart_723088 baseEnd_723088 := by
    simpa [prefixWord, tailWord_723088, baseEnd_723088] using wordTrace_append hprefix tailTrace_723088
  have hstable : (prefixWord ++ tailWord_723088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723088).length < 2 ^ (prefixWord ++ tailWord_723088).sum := by decide
  have hdescent : baseEnd_723088 < baseStart_723088 := by decide
  rcases family_descends (prefixWord ++ tailWord_723088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723158 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_723158 : Nat := 118140960795 + 723158 * 2 ^ 59
def prefixEnd_723158 : Nat := 4983230072969 + 3 ^ 40 * 723158 * 2
def baseEnd_723158 : Nat := 123775881048062291566421

theorem tailTrace_723158 : CollatzResearch.WordTrace tailWord_723158 prefixEnd_723158 123775881048062291566421 := by
  unfold tailWord_723158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648483694633096649920633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17583826076086364265820085 1648483694633096649920633)
  ·
    refine ⟨1236362770974822487440475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1648483694633096649920633 1236362770974822487440475)
    ·
      refine ⟨1854544156462233731160713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236362770974822487440475 1854544156462233731160713)
      ·
        refine ⟨1390908117346675298370535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1854544156462233731160713 1390908117346675298370535)
        ·
          refine ⟨2086362176020012947555803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390908117346675298370535 2086362176020012947555803)
          ·
            refine ⟨3129543264030019421333705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086362176020012947555803 3129543264030019421333705)
            ·
              refine ⟨2347157448022514566000279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129543264030019421333705 2347157448022514566000279)
              ·
                refine ⟨3520736172033771849000419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347157448022514566000279 3520736172033771849000419)
                ·
                  refine ⟨5281104258050657773500629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520736172033771849000419 5281104258050657773500629)
                  ·
                    refine ⟨123775881048062291566421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5281104258050657773500629 123775881048062291566421)
                    ·
                      rfl

theorem cell23_723158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_723158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723158 prefixEnd_723158 := by exact prefixLift 723158
  have htrace : WordTrace (prefixWord ++ tailWord_723158) baseStart_723158 baseEnd_723158 := by
    simpa [prefixWord, tailWord_723158, baseEnd_723158] using wordTrace_append hprefix tailTrace_723158
  have hstable : (prefixWord ++ tailWord_723158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723158).length < 2 ^ (prefixWord ++ tailWord_723158).sum := by decide
  have hdescent : baseEnd_723158 < baseStart_723158 := by decide
  rcases family_descends (prefixWord ++ tailWord_723158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723161 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 1, 6, 2]
def baseStart_723161 : Nat := 118140960795 + 723161 * 2 ^ 59
def prefixEnd_723161 : Nat := 4983230072969 + 3 ^ 40 * 723161 * 2
def baseEnd_723161 : Nat := 371329183586150362961749

theorem tailTrace_723161 : CollatzResearch.WordTrace tailWord_723161 prefixEnd_723161 371329183586150362961749 := by
  unfold tailWord_723161
  simp only [CollatzResearch.WordTrace]
  refine ⟨26375848533118677911089337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17583899022079118607392891 26375848533118677911089337)
  ·
    refine ⟨19781886399839008433317003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26375848533118677911089337 19781886399839008433317003)
    ·
      refine ⟨29672829599758512649975505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19781886399839008433317003 29672829599758512649975505)
      ·
        refine ⟨22254622199818884487481629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29672829599758512649975505 22254622199818884487481629)
        ·
          refine ⟨8345483324932081682805611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22254622199818884487481629 8345483324932081682805611)
          ·
            refine ⟨12518224987398122524208417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8345483324932081682805611 12518224987398122524208417)
            ·
              refine ⟨9388668740548591893156313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12518224987398122524208417 9388668740548591893156313)
              ·
                refine ⟨7041501555411443919867235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9388668740548591893156313 7041501555411443919867235)
                ·
                  refine ⟨10562252333117165879800853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7041501555411443919867235 10562252333117165879800853)
                  ·
                    refine ⟨495105578114867150615665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10562252333117165879800853 495105578114867150615665)
                    ·
                      refine ⟨371329183586150362961749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 495105578114867150615665 371329183586150362961749)
                      ·
                        rfl

theorem cell23_723161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_723161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723161 prefixEnd_723161 := by exact prefixLift 723161
  have htrace : WordTrace (prefixWord ++ tailWord_723161) baseStart_723161 baseEnd_723161 := by
    simpa [prefixWord, tailWord_723161, baseEnd_723161] using wordTrace_append hprefix tailTrace_723161
  have hstable : (prefixWord ++ tailWord_723161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723161).length < 2 ^ (prefixWord ++ tailWord_723161).sum := by decide
  have hdescent : baseEnd_723161 < baseStart_723161 := by decide
  rcases family_descends (prefixWord ++ tailWord_723161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723198 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_723198 : Nat := 118140960795 + 723198 * 2 ^ 59
def prefixEnd_723198 : Nat := 4983230072969 + 3 ^ 40 * 723198 * 2
def baseEnd_723198 : Nat := 371348182370366718199079

theorem tailTrace_723198 : CollatzResearch.WordTrace tailWord_723198 prefixEnd_723198 371348182370366718199079 := by
  unfold tailWord_723198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3297149754248079153773281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17584798689323088820124165 3297149754248079153773281)
  ·
    refine ⟨2472862315686059365329961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3297149754248079153773281 2472862315686059365329961)
    ·
      refine ⟨1854646736764544523997471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2472862315686059365329961 1854646736764544523997471)
      ·
        refine ⟨2781970105146816785996207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854646736764544523997471 2781970105146816785996207)
        ·
          refine ⟨4172955157720225178994311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781970105146816785996207 4172955157720225178994311)
          ·
            refine ⟨6259432736580337768491467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172955157720225178994311 6259432736580337768491467)
            ·
              refine ⟨9389149104870506652737201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6259432736580337768491467 9389149104870506652737201)
              ·
                refine ⟨7041861828652879989552901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9389149104870506652737201 7041861828652879989552901)
                ·
                  refine ⟨1320349092872414998041169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7041861828652879989552901 1320349092872414998041169)
                  ·
                    refine ⟨990261819654311248530877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1320349092872414998041169 990261819654311248530877)
                    ·
                      refine ⟨371348182370366718199079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 990261819654311248530877 371348182370366718199079)
                      ·
                        rfl

theorem cell23_723198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_723198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723198 prefixEnd_723198 := by exact prefixLift 723198
  have htrace : WordTrace (prefixWord ++ tailWord_723198) baseStart_723198 baseEnd_723198 := by
    simpa [prefixWord, tailWord_723198, baseEnd_723198] using wordTrace_append hprefix tailTrace_723198
  have hstable : (prefixWord ++ tailWord_723198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723198).length < 2 ^ (prefixWord ++ tailWord_723198).sum := by decide
  have hdescent : baseEnd_723198 < baseStart_723198 := by decide
  rcases family_descends (prefixWord ++ tailWord_723198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723201 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 6]
def baseStart_723201 : Nat := 118140960795 + 723201 * 2 ^ 59
def prefixEnd_723201 : Nat := 4983230072969 + 3 ^ 40 * 723201 * 2
def baseEnd_723201 : Nat := 41261080312481134051285

theorem tailTrace_723201 : CollatzResearch.WordTrace tailWord_723201 prefixEnd_723201 41261080312481134051285 := by
  unfold tailWord_723201
  simp only [CollatzResearch.WordTrace]
  refine ⟨26377307452973764742545457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17584871635315843161696971 26377307452973764742545457)
  ·
    refine ⟨19782980589730323556909093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26377307452973764742545457 19782980589730323556909093)
    ·
      refine ⟨3709308860574435666920455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19782980589730323556909093 3709308860574435666920455)
      ·
        refine ⟨5563963290861653500380683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3709308860574435666920455 5563963290861653500380683)
        ·
          refine ⟨8345944936292480250571025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5563963290861653500380683 8345944936292480250571025)
          ·
            refine ⟨6259458702219360187928269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8345944936292480250571025 6259458702219360187928269)
            ·
              refine ⟨2347297013332260070473101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6259458702219360187928269 2347297013332260070473101)
              ·
                refine ⟨880236379999597526427413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2347297013332260070473101 880236379999597526427413)
                ·
                  refine ⟨41261080312481134051285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 880236379999597526427413 41261080312481134051285)
                  ·
                    rfl

theorem cell23_723201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 6].length) (baseStart_723201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723201 prefixEnd_723201 := by exact prefixLift 723201
  have htrace : WordTrace (prefixWord ++ tailWord_723201) baseStart_723201 baseEnd_723201 := by
    simpa [prefixWord, tailWord_723201, baseEnd_723201] using wordTrace_append hprefix tailTrace_723201
  have hstable : (prefixWord ++ tailWord_723201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723201).length < 2 ^ (prefixWord ++ tailWord_723201).sum := by decide
  have hdescent : baseEnd_723201 < baseStart_723201 := by decide
  rcases family_descends (prefixWord ++ tailWord_723201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723251 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 4]
def baseStart_723251 : Nat := 118140960795 + 723251 * 2 ^ 59
def prefixEnd_723251 : Nat := 4983230072969 + 3 ^ 40 * 723251 * 2
def baseEnd_723251 : Nat := 371375396845055010836335

theorem tailTrace_723251 : CollatzResearch.WordTrace tailWord_723251 prefixEnd_723251 371375396845055010836335 := by
  unfold tailWord_723251
  simp only [CollatzResearch.WordTrace]
  refine ⟨26379131102792623281865607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17586087401861748854577071 26379131102792623281865607)
  ·
    refine ⟨39568696654188934922798411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26379131102792623281865607 39568696654188934922798411)
    ·
      refine ⟨59353044981283402384197617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39568696654188934922798411 59353044981283402384197617)
      ·
        refine ⟨44514783735962551788148213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59353044981283402384197617 44514783735962551788148213)
        ·
          refine ⟨4173260975246489230138895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44514783735962551788148213 4173260975246489230138895)
          ·
            refine ⟨6259891462869733845208343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173260975246489230138895 6259891462869733845208343)
            ·
              refine ⟨9389837194304600767812515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6259891462869733845208343 9389837194304600767812515)
              ·
                refine ⟨14084755791456901151718773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9389837194304600767812515 14084755791456901151718773)
                ·
                  refine ⟨1320445855449084482973635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14084755791456901151718773 1320445855449084482973635)
                  ·
                    refine ⟨1980668783173626724460453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1320445855449084482973635 1980668783173626724460453)
                    ·
                      refine ⟨371375396845055010836335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1980668783173626724460453 371375396845055010836335)
                      ·
                        rfl

theorem cell23_723251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_723251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723251 prefixEnd_723251 := by exact prefixLift 723251
  have htrace : WordTrace (prefixWord ++ tailWord_723251) baseStart_723251 baseEnd_723251 := by
    simpa [prefixWord, tailWord_723251, baseEnd_723251] using wordTrace_append hprefix tailTrace_723251
  have hstable : (prefixWord ++ tailWord_723251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723251).length < 2 ^ (prefixWord ++ tailWord_723251).sum := by decide
  have hdescent : baseEnd_723251 < baseStart_723251 := by decide
  rcases family_descends (prefixWord ++ tailWord_723251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723285 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_723285 : Nat := 118140960795 + 723285 * 2 ^ 59
def prefixEnd_723285 : Nat := 4983230072969 + 3 ^ 40 * 723285 * 2
def baseEnd_723285 : Nat := 371392855187307877811179

theorem tailTrace_723285 : CollatzResearch.WordTrace tailWord_723285 prefixEnd_723285 371392855187307877811179 := by
  unfold tailWord_723285
  simp only [CollatzResearch.WordTrace]
  refine ⟨26380371184669447088603309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17586914123112964725735539 26380371184669447088603309)
  ·
    refine ⟨9892639194251042658226241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26380371184669447088603309 9892639194251042658226241)
    ·
      refine ⟨7419479395688281993669681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9892639194251042658226241 7419479395688281993669681)
      ·
        refine ⟨5564609546766211495252261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7419479395688281993669681 5564609546766211495252261)
        ·
          refine ⟨1043364290018664655359799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5564609546766211495252261 1043364290018664655359799)
          ·
            refine ⟨1565046435027996983039699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043364290018664655359799 1565046435027996983039699)
            ·
              refine ⟨2347569652541995474559549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565046435027996983039699 2347569652541995474559549)
              ·
                refine ⟨880338619703248302959831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2347569652541995474559549 880338619703248302959831)
                ·
                  refine ⟨1320507929554872454439747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880338619703248302959831 1320507929554872454439747)
                  ·
                    refine ⟨1980761894332308681659621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1320507929554872454439747 1980761894332308681659621)
                    ·
                      refine ⟨371392855187307877811179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1980761894332308681659621 371392855187307877811179)
                      ·
                        rfl

theorem cell23_723285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_723285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723285 prefixEnd_723285 := by exact prefixLift 723285
  have htrace : WordTrace (prefixWord ++ tailWord_723285) baseStart_723285 baseEnd_723285 := by
    simpa [prefixWord, tailWord_723285, baseEnd_723285] using wordTrace_append hprefix tailTrace_723285
  have hstable : (prefixWord ++ tailWord_723285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723285).length < 2 ^ (prefixWord ++ tailWord_723285).sum := by decide
  have hdescent : baseEnd_723285 < baseStart_723285 := by decide
  rcases family_descends (prefixWord ++ tailWord_723285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723351 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 4, 6]
def baseStart_723351 : Nat := 118140960795 + 723351 * 2 ^ 59
def prefixEnd_723351 : Nat := 4983230072969 + 3 ^ 40 * 723351 * 2
def baseEnd_723351 : Nat := 123808914970168206528625

theorem tailTrace_723351 : CollatzResearch.WordTrace tailWord_723351 prefixEnd_723351 123808914970168206528625 := by
  unfold tailWord_723351
  simp only [CollatzResearch.WordTrace]
  refine ⟨26382778402430340360505907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17588518934953560240337271 26382778402430340360505907)
  ·
    refine ⟨39574167603645510540758861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26382778402430340360505907 39574167603645510540758861)
    ·
      refine ⟨14840312851367066452784573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39574167603645510540758861 14840312851367066452784573)
      ·
        refine ⟨5565117319262649919794215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14840312851367066452784573 5565117319262649919794215)
        ·
          refine ⟨8347675978893974879691323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565117319262649919794215 8347675978893974879691323)
          ·
            refine ⟨12521513968340962319536985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8347675978893974879691323 12521513968340962319536985)
            ·
              refine ⟨9391135476255721739652739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12521513968340962319536985 9391135476255721739652739)
              ·
                refine ⟨14086703214383582609479109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9391135476255721739652739 14086703214383582609479109)
                ·
                  refine ⟨2641256852696921739277333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14086703214383582609479109 2641256852696921739277333)
                  ·
                    refine ⟨123808914970168206528625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2641256852696921739277333 123808914970168206528625)
                    ·
                      rfl

theorem cell23_723351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_723351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723351 prefixEnd_723351 := by exact prefixLift 723351
  have htrace : WordTrace (prefixWord ++ tailWord_723351) baseStart_723351 baseEnd_723351 := by
    simpa [prefixWord, tailWord_723351, baseEnd_723351] using wordTrace_append hprefix tailTrace_723351
  have hstable : (prefixWord ++ tailWord_723351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723351).length < 2 ^ (prefixWord ++ tailWord_723351).sum := by decide
  have hdescent : baseEnd_723351 < baseStart_723351 := by decide
  rcases family_descends (prefixWord ++ tailWord_723351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723396 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_723396 : Nat := 118140960795 + 723396 * 2 ^ 59
def prefixEnd_723396 : Nat := 4983230072969 + 3 ^ 40 * 723396 * 2
def baseEnd_723396 : Nat := 371449851539956943523169

theorem tailTrace_723396 : CollatzResearch.WordTrace tailWord_723396 prefixEnd_723396 371449851539956943523169 := by
  unfold tailWord_723396
  simp only [CollatzResearch.WordTrace]
  refine ⟨13192209843633656522947021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17589613124844875363929361 13192209843633656522947021)
  ·
    refine ⟨4947078691362621196105133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13192209843633656522947021 4947078691362621196105133)
    ·
      refine ⟨1855154509260982948539425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4947078691362621196105133 1855154509260982948539425)
      ·
        refine ⟨1391365881945737211404569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1855154509260982948539425 1391365881945737211404569)
        ·
          refine ⟨1043524411459302908553427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1391365881945737211404569 1043524411459302908553427)
          ·
            refine ⟨1565286617188954362830141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043524411459302908553427 1565286617188954362830141)
            ·
              refine ⟨586982481445857886061303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1565286617188954362830141 586982481445857886061303)
              ·
                refine ⟨880473722168786829091955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586982481445857886061303 880473722168786829091955)
                ·
                  refine ⟨1320710583253180243637933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880473722168786829091955 1320710583253180243637933)
                  ·
                    refine ⟨495266468719942591364225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1320710583253180243637933 495266468719942591364225)
                    ·
                      refine ⟨371449851539956943523169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 495266468719942591364225 371449851539956943523169)
                      ·
                        rfl

theorem cell23_723396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_723396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723396 prefixEnd_723396 := by exact prefixLift 723396
  have htrace : WordTrace (prefixWord ++ tailWord_723396) baseStart_723396 baseEnd_723396 := by
    simpa [prefixWord, tailWord_723396, baseEnd_723396] using wordTrace_append hprefix tailTrace_723396
  have hstable : (prefixWord ++ tailWord_723396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723396).length < 2 ^ (prefixWord ++ tailWord_723396).sum := by decide
  have hdescent : baseEnd_723396 < baseStart_723396 := by decide
  rcases family_descends (prefixWord ++ tailWord_723396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723426 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_723426 : Nat := 118140960795 + 723426 * 2 ^ 59
def prefixEnd_723426 : Nat := 4983230072969 + 3 ^ 40 * 723426 * 2
def baseEnd_723426 : Nat := 371465255959591826148031

theorem tailTrace_723426 : CollatzResearch.WordTrace tailWord_723426 prefixEnd_723426 371465255959591826148031 := by
  unfold tailWord_723426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6596378469289657042371533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17590342584772418779657421 6596378469289657042371533)
  ·
    refine ⟨2473641925983621390889325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6596378469289657042371533 2473641925983621390889325)
    ·
      refine ⟨927615722243858021583497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2473641925983621390889325 927615722243858021583497)
      ·
        refine ⟨695711791682893516187623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 927615722243858021583497 695711791682893516187623)
        ·
          refine ⟨1043567687524340274281435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695711791682893516187623 1043567687524340274281435)
          ·
            refine ⟨1565351531286510411422153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043567687524340274281435 1565351531286510411422153)
            ·
              refine ⟨1174013648464882808566615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1565351531286510411422153 1174013648464882808566615)
              ·
                refine ⟨1761020472697324212849923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174013648464882808566615 1761020472697324212849923)
                ·
                  refine ⟨2641530709045986319274885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761020472697324212849923 2641530709045986319274885)
                  ·
                    refine ⟨495287007946122434864041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2641530709045986319274885 495287007946122434864041)
                    ·
                      refine ⟨371465255959591826148031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 495287007946122434864041 371465255959591826148031)
                      ·
                        rfl

theorem cell23_723426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_723426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723426 prefixEnd_723426 := by exact prefixLift 723426
  have htrace : WordTrace (prefixWord ++ tailWord_723426) baseStart_723426 baseEnd_723426 := by
    simpa [prefixWord, tailWord_723426, baseEnd_723426] using wordTrace_append hprefix tailTrace_723426
  have hstable : (prefixWord ++ tailWord_723426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723426).length < 2 ^ (prefixWord ++ tailWord_723426).sum := by decide
  have hdescent : baseEnd_723426 < baseStart_723426 := by decide
  rcases family_descends (prefixWord ++ tailWord_723426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723448 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_723448 : Nat := 118140960795 + 723448 * 2 ^ 59
def prefixEnd_723448 : Nat := 4983230072969 + 3 ^ 40 * 723448 * 2
def baseEnd_723448 : Nat := 371476552533990740072929

theorem tailTrace_723448 : CollatzResearch.WordTrace tailWord_723448 prefixEnd_723448 371476552533990740072929 := by
  unfold tailWord_723448
  simp only [CollatzResearch.WordTrace]
  refine ⟨13193158141539462963393499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17590877522052617284524665 13193158141539462963393499)
  ·
    refine ⟨19789737212309194445090249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13193158141539462963393499 19789737212309194445090249)
    ·
      refine ⟨14842302909231895833817687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19789737212309194445090249 14842302909231895833817687)
      ·
        refine ⟨22263454363847843750726531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14842302909231895833817687 22263454363847843750726531)
        ·
          refine ⟨33395181545771765626089797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22263454363847843750726531 33395181545771765626089797)
          ·
            refine ⟨6261596539832206054891837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33395181545771765626089797 6261596539832206054891837)
            ·
              refine ⟨2348098702437077270584439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6261596539832206054891837 2348098702437077270584439)
              ·
                refine ⟨3522148053655615905876659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348098702437077270584439 3522148053655615905876659)
                ·
                  refine ⟨5283222080483423858814989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522148053655615905876659 5283222080483423858814989)
                  ·
                    refine ⟨1981208280181283947055621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5283222080483423858814989 1981208280181283947055621)
                    ·
                      refine ⟨371476552533990740072929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1981208280181283947055621 371476552533990740072929)
                      ·
                        rfl

theorem cell23_723448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_723448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723448 prefixEnd_723448 := by exact prefixLift 723448
  have htrace : WordTrace (prefixWord ++ tailWord_723448) baseStart_723448 baseEnd_723448 := by
    simpa [prefixWord, tailWord_723448, baseEnd_723448] using wordTrace_append hprefix tailTrace_723448
  have hstable : (prefixWord ++ tailWord_723448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723448).length < 2 ^ (prefixWord ++ tailWord_723448).sum := by decide
  have hdescent : baseEnd_723448 < baseStart_723448 := by decide
  rcases family_descends (prefixWord ++ tailWord_723448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723451 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 9]
def baseStart_723451 : Nat := 118140960795 + 723451 * 2 ^ 59
def prefixEnd_723451 : Nat := 4983230072969 + 3 ^ 40 * 723451 * 2
def baseEnd_723451 : Nat := 371478092975954228335415

theorem tailTrace_723451 : CollatzResearch.WordTrace tailWord_723451 prefixEnd_723451 371478092975954228335415 := by
  unfold tailWord_723451
  simp only [CollatzResearch.WordTrace]
  refine ⟨26386425702068057439146207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17590950468045371626097471 26386425702068057439146207)
  ·
    refine ⟨39579638553102086158719311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26386425702068057439146207 39579638553102086158719311)
    ·
      refine ⟨59369457829653129238078967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39579638553102086158719311 59369457829653129238078967)
      ·
        refine ⟨89054186744479693857118451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59369457829653129238078967 89054186744479693857118451)
        ·
          refine ⟨133581280116719540785677677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89054186744479693857118451 133581280116719540785677677)
          ·
            refine ⟨50092980043769827794629129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133581280116719540785677677 50092980043769827794629129)
            ·
              refine ⟨37569735032827370845971847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50092980043769827794629129 37569735032827370845971847)
              ·
                refine ⟨56354602549241056268957771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37569735032827370845971847 56354602549241056268957771)
                ·
                  refine ⟨84531903823861584403436657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56354602549241056268957771 84531903823861584403436657)
                  ·
                    refine ⟨63398927867896188302577493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84531903823861584403436657 63398927867896188302577493)
                    ·
                      refine ⟨371478092975954228335415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 63398927867896188302577493 371478092975954228335415)
                      ·
                        rfl

theorem cell23_723451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_723451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723451 prefixEnd_723451 := by exact prefixLift 723451
  have htrace : WordTrace (prefixWord ++ tailWord_723451) baseStart_723451 baseEnd_723451 := by
    simpa [prefixWord, tailWord_723451, baseEnd_723451] using wordTrace_append hprefix tailTrace_723451
  have hstable : (prefixWord ++ tailWord_723451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723451).length < 2 ^ (prefixWord ++ tailWord_723451).sum := by decide
  have hdescent : baseEnd_723451 < baseStart_723451 := by decide
  rcases family_descends (prefixWord ++ tailWord_723451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723475 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 3, 4]
def baseStart_723475 : Nat := 118140960795 + 723475 * 2 ^ 59
def prefixEnd_723475 : Nat := 4983230072969 + 3 ^ 40 * 723475 * 2
def baseEnd_723475 : Nat := 123830138837220711478435

theorem tailTrace_723475 : CollatzResearch.WordTrace tailWord_723475 prefixEnd_723475 123830138837220711478435 := by
  unfold tailWord_723475
  simp only [CollatzResearch.WordTrace]
  refine ⟨26387301053981109538019879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17591534035987406358679919 26387301053981109538019879)
  ·
    refine ⟨39580951580971664307029819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26387301053981109538019879 39580951580971664307029819)
    ·
      refine ⟨59371427371457496460544729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39580951580971664307029819 59371427371457496460544729)
      ·
        refine ⟨44528570528593122345408547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59371427371457496460544729 44528570528593122345408547)
        ·
          refine ⟨66792855792889683518112821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44528570528593122345408547 66792855792889683518112821)
          ·
            refine ⟨6261830230583407829823077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66792855792889683518112821 6261830230583407829823077)
            ·
              refine ⟨1174093168234388968091827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6261830230583407829823077 1174093168234388968091827)
              ·
                refine ⟨1761139752351583452137741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174093168234388968091827 1761139752351583452137741)
                ·
                  refine ⟨660427407131843794551653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1761139752351583452137741 660427407131843794551653)
                  ·
                    refine ⟨123830138837220711478435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 660427407131843794551653 123830138837220711478435)
                    ·
                      rfl

theorem cell23_723475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 4].length) (baseStart_723475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723475 prefixEnd_723475 := by exact prefixLift 723475
  have htrace : WordTrace (prefixWord ++ tailWord_723475) baseStart_723475 baseEnd_723475 := by
    simpa [prefixWord, tailWord_723475, baseEnd_723475] using wordTrace_append hprefix tailTrace_723475
  have hstable : (prefixWord ++ tailWord_723475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723475).length < 2 ^ (prefixWord ++ tailWord_723475).sum := by decide
  have hdescent : baseEnd_723475 < baseStart_723475 := by decide
  rcases family_descends (prefixWord ++ tailWord_723475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723485 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_723485 : Nat := 118140960795 + 723485 * 2 ^ 59
def prefixEnd_723485 : Nat := 4983230072969 + 3 ^ 40 * 723485 * 2
def baseEnd_723485 : Nat := 371495551318207095310259

theorem tailTrace_723485 : CollatzResearch.WordTrace tailWord_723485 prefixEnd_723485 371495551318207095310259 := by
  unfold tailWord_723485
  simp only [CollatzResearch.WordTrace]
  refine ⟨26387665783944881245883909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17591777189296587497255939 26387665783944881245883909)
  ·
    refine ⟨4947687334489665233603233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26387665783944881245883909 4947687334489665233603233)
    ·
      refine ⟨3710765500867248925202425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4947687334489665233603233 3710765500867248925202425)
      ·
        refine ⟨2783074125650436693901819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3710765500867248925202425 2783074125650436693901819)
        ·
          refine ⟨4174611188475655040852729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783074125650436693901819 4174611188475655040852729)
          ·
            refine ⟨3130958391356741280639547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4174611188475655040852729 3130958391356741280639547)
            ·
              refine ⟨4696437587035111920959321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130958391356741280639547 4696437587035111920959321)
              ·
                refine ⟨3522328190276333940719491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4696437587035111920959321 3522328190276333940719491)
                ·
                  refine ⟨5283492285414500911079237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522328190276333940719491 5283492285414500911079237)
                  ·
                    refine ⟨990654803515218920827357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5283492285414500911079237 990654803515218920827357)
                    ·
                      refine ⟨371495551318207095310259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 990654803515218920827357 371495551318207095310259)
                      ·
                        rfl

theorem cell23_723485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_723485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723485 prefixEnd_723485 := by exact prefixLift 723485
  have htrace : WordTrace (prefixWord ++ tailWord_723485) baseStart_723485 baseEnd_723485 := by
    simpa [prefixWord, tailWord_723485, baseEnd_723485] using wordTrace_append hprefix tailTrace_723485
  have hstable : (prefixWord ++ tailWord_723485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723485).length < 2 ^ (prefixWord ++ tailWord_723485).sum := by decide
  have hdescent : baseEnd_723485 < baseStart_723485 := by decide
  rcases family_descends (prefixWord ++ tailWord_723485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723526 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_723526 : Nat := 118140960795 + 723526 * 2 ^ 59
def prefixEnd_723526 : Nat := 4983230072969 + 3 ^ 40 * 723526 * 2
def baseEnd_723526 : Nat := 123838868008347144965857

theorem tailTrace_723526 : CollatzResearch.WordTrace tailWord_723526 prefixEnd_723526 123838868008347144965857 := by
  unfold tailWord_723526
  simp only [CollatzResearch.WordTrace]
  refine ⟨824661286774885789003951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17592774117864230165417621 824661286774885789003951)
  ·
    refine ⟨1236991930162328683505927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 824661286774885789003951 1236991930162328683505927)
    ·
      refine ⟨1855487895243493025258891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236991930162328683505927 1855487895243493025258891)
      ·
        refine ⟨2783231842865239537888337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855487895243493025258891 2783231842865239537888337)
        ·
          refine ⟨2087423882148929653416253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2783231842865239537888337 2087423882148929653416253)
          ·
            refine ⟨782783955805848620031095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2087423882148929653416253 782783955805848620031095)
            ·
              refine ⟨1174175933708772930046643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782783955805848620031095 1174175933708772930046643)
              ·
                refine ⟨1761263900563159395069965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174175933708772930046643 1761263900563159395069965)
                ·
                  refine ⟨660473962711184773151237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1761263900563159395069965 660473962711184773151237)
                  ·
                    refine ⟨123838868008347144965857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 660473962711184773151237 123838868008347144965857)
                    ·
                      rfl

theorem cell23_723526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_723526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723526 prefixEnd_723526 := by exact prefixLift 723526
  have htrace : WordTrace (prefixWord ++ tailWord_723526) baseStart_723526 baseEnd_723526 := by
    simpa [prefixWord, tailWord_723526, baseEnd_723526] using wordTrace_append hprefix tailTrace_723526
  have hstable : (prefixWord ++ tailWord_723526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723526).length < 2 ^ (prefixWord ++ tailWord_723526).sum := by decide
  have hdescent : baseEnd_723526 < baseStart_723526 := by decide
  rcases family_descends (prefixWord ++ tailWord_723526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723555 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 4]
def baseStart_723555 : Nat := 118140960795 + 723555 * 2 ^ 59
def prefixEnd_723555 : Nat := 4983230072969 + 3 ^ 40 * 723555 * 2
def baseEnd_723555 : Nat := 371531494964021821434937

theorem tailTrace_723555 : CollatzResearch.WordTrace tailWord_723555 prefixEnd_723555 371531494964021821434937 := by
  unfold tailWord_723555
  simp only [CollatzResearch.WordTrace]
  refine ⟨26390218893691283200932119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17593479262460855467288079 26390218893691283200932119)
  ·
    refine ⟨39585328340536924801398179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26390218893691283200932119 39585328340536924801398179)
    ·
      refine ⟨59377992510805387202097269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39585328340536924801398179 59377992510805387202097269)
      ·
        refine ⟨5566686797888005050196619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59377992510805387202097269 5566686797888005050196619)
        ·
          refine ⟨8350030196832007575294929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5566686797888005050196619 8350030196832007575294929)
          ·
            refine ⟨6262522647624005681471197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8350030196832007575294929 6262522647624005681471197)
            ·
              refine ⟨2348445992859002130551699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6262522647624005681471197 2348445992859002130551699)
              ·
                refine ⟨3522668989288503195827549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348445992859002130551699 3522668989288503195827549)
                ·
                  refine ⟨1321000870983188698435331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3522668989288503195827549 1321000870983188698435331)
                  ·
                    refine ⟨1981501306474783047652997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1321000870983188698435331 1981501306474783047652997)
                    ·
                      refine ⟨371531494964021821434937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1981501306474783047652997 371531494964021821434937)
                      ·
                        rfl

theorem cell23_723555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_723555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723555 prefixEnd_723555 := by exact prefixLift 723555
  have htrace : WordTrace (prefixWord ++ tailWord_723555) baseStart_723555 baseEnd_723555 := by
    simpa [prefixWord, tailWord_723555, baseEnd_723555] using wordTrace_append hprefix tailTrace_723555
  have hstable : (prefixWord ++ tailWord_723555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723555).length < 2 ^ (prefixWord ++ tailWord_723555).sum := by decide
  have hdescent : baseEnd_723555 < baseStart_723555 := by decide
  rcases family_descends (prefixWord ++ tailWord_723555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723565 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_723565 : Nat := 118140960795 + 723565 * 2 ^ 59
def prefixEnd_723565 : Nat := 4983230072969 + 3 ^ 40 * 723565 * 2
def baseEnd_723565 : Nat := 123845543256855594103297

theorem tailTrace_723565 : CollatzResearch.WordTrace tailWord_723565 prefixEnd_723565 123845543256855594103297 := by
  unfold tailWord_723565
  simp only [CollatzResearch.WordTrace]
  refine ⟨26390583623655054908796149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17593722415770036605864099 26390583623655054908796149)
  ·
    refine ⟨2474117214717661397699639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26390583623655054908796149 2474117214717661397699639)
    ·
      refine ⟨3711175822076492096549459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2474117214717661397699639 3711175822076492096549459)
      ·
        refine ⟨5566763733114738144824189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3711175822076492096549459 5566763733114738144824189)
        ·
          refine ⟨2087536399918026804309071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5566763733114738144824189 2087536399918026804309071)
          ·
            refine ⟨3131304599877040206463607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087536399918026804309071 3131304599877040206463607)
            ·
              refine ⟨4696956899815560309695411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131304599877040206463607 4696956899815560309695411)
              ·
                refine ⟨7045435349723340464543117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4696956899815560309695411 7045435349723340464543117)
                ·
                  refine ⟨2642038256146252674203669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7045435349723340464543117 2642038256146252674203669)
                  ·
                    refine ⟨123845543256855594103297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2642038256146252674203669 123845543256855594103297)
                    ·
                      rfl

theorem cell23_723565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_723565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723565 prefixEnd_723565 := by exact prefixLift 723565
  have htrace : WordTrace (prefixWord ++ tailWord_723565) baseStart_723565 baseEnd_723565 := by
    simpa [prefixWord, tailWord_723565, baseEnd_723565] using wordTrace_append hprefix tailTrace_723565
  have hstable : (prefixWord ++ tailWord_723565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723565).length < 2 ^ (prefixWord ++ tailWord_723565).sum := by decide
  have hdescent : baseEnd_723565 < baseStart_723565 := by decide
  rcases family_descends (prefixWord ++ tailWord_723565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723575 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 5]
def baseStart_723575 : Nat := 118140960795 + 723575 * 2 ^ 59
def prefixEnd_723575 : Nat := 4983230072969 + 3 ^ 40 * 723575 * 2
def baseEnd_723575 : Nat := 371541764577111743184845

theorem tailTrace_723575 : CollatzResearch.WordTrace tailWord_723575 prefixEnd_723575 371541764577111743184845 := by
  unfold tailWord_723575
  simp only [CollatzResearch.WordTrace]
  refine ⟨26390948353618826616660179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17593965569079217744440119 26390948353618826616660179)
  ·
    refine ⟨39586422530428239924990269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26390948353618826616660179 39586422530428239924990269)
    ·
      refine ⟨14844908448910589971871351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39586422530428239924990269 14844908448910589971871351)
      ·
        refine ⟨22267362673365884957807027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14844908448910589971871351 22267362673365884957807027)
        ·
          refine ⟨33401044010048827436710541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22267362673365884957807027 33401044010048827436710541)
          ·
            refine ⟨12525391503768310288766453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33401044010048827436710541 12525391503768310288766453)
            ·
              refine ⟨1174255453478279089571855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12525391503768310288766453 1174255453478279089571855)
              ·
                refine ⟨1761383180217418634357783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174255453478279089571855 1761383180217418634357783)
                ·
                  refine ⟨2642074770326127951536675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761383180217418634357783 2642074770326127951536675)
                  ·
                    refine ⟨3963112155489191927305013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2642074770326127951536675 3963112155489191927305013)
                    ·
                      refine ⟨371541764577111743184845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3963112155489191927305013 371541764577111743184845)
                      ·
                        rfl

theorem cell23_723575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_723575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723575 prefixEnd_723575 := by exact prefixLift 723575
  have htrace : WordTrace (prefixWord ++ tailWord_723575) baseStart_723575 baseEnd_723575 := by
    simpa [prefixWord, tailWord_723575, baseEnd_723575] using wordTrace_append hprefix tailTrace_723575
  have hstable : (prefixWord ++ tailWord_723575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723575).length < 2 ^ (prefixWord ++ tailWord_723575).sum := by decide
  have hdescent : baseEnd_723575 < baseStart_723575 := by decide
  rcases family_descends (prefixWord ++ tailWord_723575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723585 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_723585 : Nat := 118140960795 + 723585 * 2 ^ 59
def prefixEnd_723585 : Nat := 4983230072969 + 3 ^ 40 * 723585 * 2
def baseEnd_723585 : Nat := 371546899383656704059799

theorem tailTrace_723585 : CollatzResearch.WordTrace tailWord_723585 prefixEnd_723585 371546899383656704059799 := by
  unfold tailWord_723585
  simp only [CollatzResearch.WordTrace]
  refine ⟨26391313083582598324524209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17594208722388398883016139 26391313083582598324524209)
  ·
    refine ⟨19793484812686948743393157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26391313083582598324524209 19793484812686948743393157)
    ·
      refine ⟨3711278402378802889386217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19793484812686948743393157 3711278402378802889386217)
      ·
        refine ⟨2783458801784102167039663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3711278402378802889386217 2783458801784102167039663)
        ·
          refine ⟨4175188202676153250559495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783458801784102167039663 4175188202676153250559495)
          ·
            refine ⟨6262782304014229875839243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175188202676153250559495 6262782304014229875839243)
            ·
              refine ⟨9394173456021344813758865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262782304014229875839243 9394173456021344813758865)
              ·
                refine ⟨7045630092016008610319149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9394173456021344813758865 7045630092016008610319149)
                ·
                  refine ⟨2642111284506003228869681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7045630092016008610319149 2642111284506003228869681)
                  ·
                    refine ⟨1981583463379502421652261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2642111284506003228869681 1981583463379502421652261)
                    ·
                      refine ⟨371546899383656704059799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1981583463379502421652261 371546899383656704059799)
                      ·
                        rfl

theorem cell23_723585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_723585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723585 prefixEnd_723585 := by exact prefixLift 723585
  have htrace : WordTrace (prefixWord ++ tailWord_723585) baseStart_723585 baseEnd_723585 := by
    simpa [prefixWord, tailWord_723585, baseEnd_723585] using wordTrace_append hprefix tailTrace_723585
  have hstable : (prefixWord ++ tailWord_723585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723585).length < 2 ^ (prefixWord ++ tailWord_723585).sum := by decide
  have hdescent : baseEnd_723585 < baseStart_723585 := by decide
  rcases family_descends (prefixWord ++ tailWord_723585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723602 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_723602 : Nat := 118140960795 + 723602 * 2 ^ 59
def prefixEnd_723602 : Nat := 4983230072969 + 3 ^ 40 * 723602 * 2
def baseEnd_723602 : Nat := 371555628554783137547221

theorem tailTrace_723602 : CollatzResearch.WordTrace tailWord_723602 prefixEnd_723602 371555628554783137547221 := by
  unfold tailWord_723602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6597983281130252556973265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17594622083014006818595373 6597983281130252556973265)
  ·
    refine ⟨4948487460847689417729949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6597983281130252556973265 4948487460847689417729949)
    ·
      refine ⟨1855682797817883531648731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4948487460847689417729949 1855682797817883531648731)
      ·
        refine ⟨2783524196726825297473097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855682797817883531648731 2783524196726825297473097)
        ·
          refine ⟨2087643147545118973104823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2783524196726825297473097 2087643147545118973104823)
          ·
            refine ⟨3131464721317678459657235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087643147545118973104823 3131464721317678459657235)
            ·
              refine ⟨4697197081976517689485853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131464721317678459657235 4697197081976517689485853)
              ·
                refine ⟨1761448905741194133557195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4697197081976517689485853 1761448905741194133557195)
                ·
                  refine ⟨2642173358611791200335793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761448905741194133557195 2642173358611791200335793)
                  ·
                    refine ⟨1981630018958843400251845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2642173358611791200335793 1981630018958843400251845)
                    ·
                      refine ⟨371555628554783137547221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1981630018958843400251845 371555628554783137547221)
                      ·
                        rfl

theorem cell23_723602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_723602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723602 prefixEnd_723602 := by exact prefixLift 723602
  have htrace : WordTrace (prefixWord ++ tailWord_723602) baseStart_723602 baseEnd_723602 := by
    simpa [prefixWord, tailWord_723602, baseEnd_723602] using wordTrace_append hprefix tailTrace_723602
  have hstable : (prefixWord ++ tailWord_723602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723602).length < 2 ^ (prefixWord ++ tailWord_723602).sum := by decide
  have hdescent : baseEnd_723602 < baseStart_723602 := by decide
  rcases family_descends (prefixWord ++ tailWord_723602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723612 : List Nat := [2, 2, 3, 2, 2, 2, 3, 7]
def baseStart_723612 : Nat := 118140960795 + 723612 * 2 ^ 59
def prefixEnd_723612 : Nat := 4983230072969 + 3 ^ 40 * 723612 * 2
def baseEnd_723612 : Nat := 13761509754123262904525

theorem tailTrace_723612 : CollatzResearch.WordTrace tailWord_723612 prefixEnd_723612 13761509754123262904525 := by
  unfold tailWord_723612
  simp only [CollatzResearch.WordTrace]
  refine ⟨13196148927242390967878545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17594865236323187957171393 13196148927242390967878545)
  ·
    refine ⟨9897111695431793225908909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13196148927242390967878545 9897111695431793225908909)
    ·
      refine ⟨3711416885786922459715841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9897111695431793225908909 3711416885786922459715841)
      ·
        refine ⟨2783562664340191844786881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3711416885786922459715841 2783562664340191844786881)
        ·
          refine ⟨2087671998255143883590161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2783562664340191844786881 2087671998255143883590161)
          ·
            refine ⟨1565753998691357912692621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2087671998255143883590161 1565753998691357912692621)
            ·
              refine ⟨587157749509259217259733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1565753998691357912692621 587157749509259217259733)
              ·
                refine ⟨13761509754123262904525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 587157749509259217259733 13761509754123262904525)
                ·
                  rfl

theorem cell23_723612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 7].length) (baseStart_723612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723612 prefixEnd_723612 := by exact prefixLift 723612
  have htrace : WordTrace (prefixWord ++ tailWord_723612) baseStart_723612 baseEnd_723612 := by
    simpa [prefixWord, tailWord_723612, baseEnd_723612] using wordTrace_append hprefix tailTrace_723612
  have hstable : (prefixWord ++ tailWord_723612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723612).length < 2 ^ (prefixWord ++ tailWord_723612).sum := by decide
  have hdescent : baseEnd_723612 < baseStart_723612 := by decide
  rcases family_descends (prefixWord ++ tailWord_723612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723623 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_723623 : Nat := 118140960795 + 723623 * 2 ^ 59
def prefixEnd_723623 : Nat := 4983230072969 + 3 ^ 40 * 723623 * 2
def baseEnd_723623 : Nat := 371566411648527555384625

theorem tailTrace_723623 : CollatzResearch.WordTrace tailWord_723623 prefixEnd_723623 371566411648527555384625 := by
  unfold tailWord_723623
  simp only [CollatzResearch.WordTrace]
  refine ⟨26392699057444930814407523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17595132704963287209605015 26392699057444930814407523)
  ·
    refine ⟨39589048586167396221611285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26392699057444930814407523 39589048586167396221611285)
    ·
      refine ⟨1855736652476596697888029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39589048586167396221611285 1855736652476596697888029)
      ·
        refine ⟨695901244678723761708011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1855736652476596697888029 695901244678723761708011)
        ·
          refine ⟨1043851867018085642562017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695901244678723761708011 1043851867018085642562017)
          ·
            refine ⟨782888900263564231921513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1043851867018085642562017 782888900263564231921513)
            ·
              refine ⟨587166675197673173941135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782888900263564231921513 587166675197673173941135)
              ·
                refine ⟨880750012796509760911703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587166675197673173941135 880750012796509760911703)
                ·
                  refine ⟨1321125019194764641367555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880750012796509760911703 1321125019194764641367555)
                  ·
                    refine ⟨1981687528792146962051333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1321125019194764641367555 1981687528792146962051333)
                    ·
                      refine ⟨371566411648527555384625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1981687528792146962051333 371566411648527555384625)
                      ·
                        rfl

theorem cell23_723623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_723623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723623 prefixEnd_723623 := by exact prefixLift 723623
  have htrace : WordTrace (prefixWord ++ tailWord_723623) baseStart_723623 baseEnd_723623 := by
    simpa [prefixWord, tailWord_723623, baseEnd_723623] using wordTrace_append hprefix tailTrace_723623
  have hstable : (prefixWord ++ tailWord_723623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723623).length < 2 ^ (prefixWord ++ tailWord_723623).sum := by decide
  have hdescent : baseEnd_723623 < baseStart_723623 := by decide
  rcases family_descends (prefixWord ++ tailWord_723623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723633 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 2, 4]
def baseStart_723633 : Nat := 118140960795 + 723633 * 2 ^ 59
def prefixEnd_723633 : Nat := 4983230072969 + 3 ^ 40 * 723633 * 2
def baseEnd_723633 : Nat := 123857182151690838753193

theorem tailTrace_723633 : CollatzResearch.WordTrace tailWord_723633 prefixEnd_723633 123857182151690838753193 := by
  unfold tailWord_723633
  simp only [CollatzResearch.WordTrace]
  refine ⟨26393063787408702522271553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17595375858272468348181035 26393063787408702522271553)
  ·
    refine ⟨19794797840556526891703665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26393063787408702522271553 19794797840556526891703665)
    ·
      refine ⟨14846098380417395168777749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19794797840556526891703665 14846098380417395168777749)
      ·
        refine ⟨695910861582065398536457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14846098380417395168777749 695910861582065398536457)
        ·
          refine ⟨521933146186549048902343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 695910861582065398536457 521933146186549048902343)
          ·
            refine ⟨782899719279823573353515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521933146186549048902343 782899719279823573353515)
            ·
              refine ⟨1174349578919735360030273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782899719279823573353515 1174349578919735360030273)
              ·
                refine ⟨880762184189801520022705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174349578919735360030273 880762184189801520022705)
                ·
                  refine ⟨660571638142351140017029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 880762184189801520022705 660571638142351140017029)
                  ·
                    refine ⟨123857182151690838753193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 660571638142351140017029 123857182151690838753193)
                    ·
                      rfl

theorem cell23_723633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_723633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723633 prefixEnd_723633 := by exact prefixLift 723633
  have htrace : WordTrace (prefixWord ++ tailWord_723633) baseStart_723633 baseEnd_723633 := by
    simpa [prefixWord, tailWord_723633, baseEnd_723633] using wordTrace_append hprefix tailTrace_723633
  have hstable : (prefixWord ++ tailWord_723633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723633).length < 2 ^ (prefixWord ++ tailWord_723633).sum := by decide
  have hdescent : baseEnd_723633 < baseStart_723633 := by decide
  rcases family_descends (prefixWord ++ tailWord_723633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723639 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 4, 1, 3]
def baseStart_723639 : Nat := 118140960795 + 723639 * 2 ^ 59
def prefixEnd_723639 : Nat := 4983230072969 + 3 ^ 40 * 723639 * 2
def baseEnd_723639 : Nat := 371574627338999492784551

theorem tailTrace_723639 : CollatzResearch.WordTrace tailWord_723639 prefixEnd_723639 371574627338999492784551 := by
  unfold tailWord_723639
  simp only [CollatzResearch.WordTrace]
  refine ⟨26393282625386965546989971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17595521750257977031326647 26393282625386965546989971)
  ·
    refine ⟨39589923938080448320484957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26393282625386965546989971 39589923938080448320484957)
    ·
      refine ⟨14846221476780168120181859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39589923938080448320484957 14846221476780168120181859)
      ·
        refine ⟨22269332215170252180272789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14846221476780168120181859 22269332215170252180272789)
        ·
          refine ⟨1043874947586105570950287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22269332215170252180272789 1043874947586105570950287)
          ·
            refine ⟨1565812421379158356425431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043874947586105570950287 1565812421379158356425431)
            ·
              refine ⟨2348718632068737534638147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565812421379158356425431 2348718632068737534638147)
              ·
                refine ⟨3523077948103106301957221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348718632068737534638147 3523077948103106301957221)
                ·
                  refine ⟨660577115269332431616979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3523077948103106301957221 660577115269332431616979)
                  ·
                    refine ⟨990865672903998647425469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 660577115269332431616979 990865672903998647425469)
                    ·
                      refine ⟨371574627338999492784551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 990865672903998647425469 371574627338999492784551)
                      ·
                        rfl

theorem cell23_723639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_723639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723639 prefixEnd_723639 := by exact prefixLift 723639
  have htrace : WordTrace (prefixWord ++ tailWord_723639) baseStart_723639 baseEnd_723639 := by
    simpa [prefixWord, tailWord_723639, baseEnd_723639] using wordTrace_append hprefix tailTrace_723639
  have hstable : (prefixWord ++ tailWord_723639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723639).length < 2 ^ (prefixWord ++ tailWord_723639).sum := by decide
  have hdescent : baseEnd_723639 < baseStart_723639 := by decide
  rcases family_descends (prefixWord ++ tailWord_723639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723656 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 2, 1, 3]
def baseStart_723656 : Nat := 118140960795 + 723656 * 2 ^ 59
def prefixEnd_723656 : Nat := 4983230072969 + 3 ^ 40 * 723656 * 2
def baseEnd_723656 : Nat := 371583356510125926271973

theorem tailTrace_723656 : CollatzResearch.WordTrace tailWord_723656 prefixEnd_723656 371583356510125926271973 := by
  unfold tailWord_723656
  simp only [CollatzResearch.WordTrace]
  refine ⟨13196951333162688725179411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17595935110883584966905881 13196951333162688725179411)
  ·
    refine ⟨19795426999744033087769117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13196951333162688725179411 19795426999744033087769117)
    ·
      refine ⟨7423285124904012407913419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19795426999744033087769117 7423285124904012407913419)
      ·
        refine ⟨11134927687356018611870129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7423285124904012407913419 11134927687356018611870129)
        ·
          refine ⟨8351195765517013958902597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11134927687356018611870129 8351195765517013958902597)
          ·
            refine ⟨1565849206034440117294237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8351195765517013958902597 1565849206034440117294237)
            ·
              refine ⟨587193452262915043985339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1565849206034440117294237 587193452262915043985339)
              ·
                refine ⟨880790178394372565978009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587193452262915043985339 880790178394372565978009)
                ·
                  refine ⟨660592633795779424483507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 880790178394372565978009 660592633795779424483507)
                  ·
                    refine ⟨990888950693669136725261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 660592633795779424483507 990888950693669136725261)
                    ·
                      refine ⟨371583356510125926271973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 990888950693669136725261 371583356510125926271973)
                      ·
                        rfl

theorem cell23_723656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_723656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723656 prefixEnd_723656 := by exact prefixLift 723656
  have htrace : WordTrace (prefixWord ++ tailWord_723656) baseStart_723656 baseEnd_723656 := by
    simpa [prefixWord, tailWord_723656, baseEnd_723656] using wordTrace_append hprefix tailTrace_723656
  have hstable : (prefixWord ++ tailWord_723656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723656).length < 2 ^ (prefixWord ++ tailWord_723656).sum := by decide
  have hdescent : baseEnd_723656 < baseStart_723656 := by decide
  rcases family_descends (prefixWord ++ tailWord_723656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723665 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_723665 : Nat := 118140960795 + 723665 * 2 ^ 59
def prefixEnd_723665 : Nat := 4983230072969 + 3 ^ 40 * 723665 * 2
def baseEnd_723665 : Nat := 371587977836016391059431

theorem tailTrace_723665 : CollatzResearch.WordTrace tailWord_723665 prefixEnd_723665 371587977836016391059431 := by
  unfold tailWord_723665
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394230923292771987436449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17596153948861847991624299 26394230923292771987436449)
  ·
    refine ⟨19795673192469578990577337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26394230923292771987436449 19795673192469578990577337)
    ·
      refine ⟨14846754894352184242933003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19795673192469578990577337 14846754894352184242933003)
      ·
        refine ⟨22270132341528276364399505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14846754894352184242933003 22270132341528276364399505)
        ·
          refine ⟨16702599256146207273299629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22270132341528276364399505 16702599256146207273299629)
          ·
            refine ⟨6263474721054827727487361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16702599256146207273299629 6263474721054827727487361)
            ·
              refine ⟨4697606040791120795615521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6263474721054827727487361 4697606040791120795615521)
              ·
                refine ⟨3523204530593340596711641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4697606040791120795615521 3523204530593340596711641)
                ·
                  refine ⟨2642403397945005447533731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3523204530593340596711641 2642403397945005447533731)
                  ·
                    refine ⟨3963605096917508171300597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2642403397945005447533731 3963605096917508171300597)
                    ·
                      refine ⟨371587977836016391059431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3963605096917508171300597 371587977836016391059431)
                      ·
                        rfl

theorem cell23_723665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_723665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723665 prefixEnd_723665 := by exact prefixLift 723665
  have htrace : WordTrace (prefixWord ++ tailWord_723665) baseStart_723665 baseEnd_723665 := by
    simpa [prefixWord, tailWord_723665, baseEnd_723665] using wordTrace_append hprefix tailTrace_723665
  have hstable : (prefixWord ++ tailWord_723665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723665).length < 2 ^ (prefixWord ++ tailWord_723665).sum := by decide
  have hdescent : baseEnd_723665 < baseStart_723665 := by decide
  rcases family_descends (prefixWord ++ tailWord_723665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723679 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 4, 2, 2]
def baseStart_723679 : Nat := 118140960795 + 723679 * 2 ^ 59
def prefixEnd_723679 : Nat := 4983230072969 + 3 ^ 40 * 723679 * 2
def baseEnd_723679 : Nat := 371595166565179336284367

theorem tailTrace_723679 : CollatzResearch.WordTrace tailWord_723679 prefixEnd_723679 371595166565179336284367 := by
  unfold tailWord_723679
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394741545242052378446091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17596494363494701585630727 26394741545242052378446091)
  ·
    refine ⟨39592112317863078567669137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26394741545242052378446091 39592112317863078567669137)
    ·
      refine ⟨29694084238397308925751853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39592112317863078567669137 29694084238397308925751853)
      ·
        refine ⟨11135281589398990847156945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29694084238397308925751853 11135281589398990847156945)
        ·
          refine ⟨8351461192049243135367709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11135281589398990847156945 8351461192049243135367709)
          ·
            refine ⟨3131797947018466175762891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8351461192049243135367709 3131797947018466175762891)
            ·
              refine ⟨4697696920527699263644337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131797947018466175762891 4697696920527699263644337)
              ·
                refine ⟨3523272690395774447733253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4697696920527699263644337 3523272690395774447733253)
                ·
                  refine ⟨660613629449207708949985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3523272690395774447733253 660613629449207708949985)
                  ·
                    refine ⟨495460222086905781712489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 660613629449207708949985 495460222086905781712489)
                    ·
                      refine ⟨371595166565179336284367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 495460222086905781712489 371595166565179336284367)
                      ·
                        rfl

theorem cell23_723679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_723679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723679 prefixEnd_723679 := by exact prefixLift 723679
  have htrace : WordTrace (prefixWord ++ tailWord_723679) baseStart_723679 baseEnd_723679 := by
    simpa [prefixWord, tailWord_723679, baseEnd_723679] using wordTrace_append hprefix tailTrace_723679
  have hstable : (prefixWord ++ tailWord_723679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723679).length < 2 ^ (prefixWord ++ tailWord_723679).sum := by decide
  have hdescent : baseEnd_723679 < baseStart_723679 := by decide
  rcases family_descends (prefixWord ++ tailWord_723679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723715 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 6, 5]
def baseStart_723715 : Nat := 118140960795 + 723715 * 2 ^ 59
def prefixEnd_723715 : Nat := 4983230072969 + 3 ^ 40 * 723715 * 2
def baseEnd_723715 : Nat := 123871217289580398478067

theorem tailTrace_723715 : CollatzResearch.WordTrace tailWord_723715 prefixEnd_723715 123871217289580398478067 := by
  unfold tailWord_723715
  simp only [CollatzResearch.WordTrace]
  refine ⟨26396054573111630526756599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17597369715407753684504399 26396054573111630526756599)
  ·
    refine ⟨39594081859667445790134899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26396054573111630526756599 39594081859667445790134899)
    ·
      refine ⟨59391122789501168685202349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39594081859667445790134899 59391122789501168685202349)
      ·
        refine ⟨22271671046062938256950881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59391122789501168685202349 22271671046062938256950881)
        ·
          refine ⟨16703753284547203692713161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22271671046062938256950881 16703753284547203692713161)
          ·
            refine ⟨12527814963410402769534871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16703753284547203692713161 12527814963410402769534871)
            ·
              refine ⟨18791722445115604154302307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12527814963410402769534871 18791722445115604154302307)
              ·
                refine ⟨28187583667673406231453461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18791722445115604154302307 28187583667673406231453461)
                ·
                  refine ⟨1321292984422190917099381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28187583667673406231453461 1321292984422190917099381)
                  ·
                    refine ⟨123871217289580398478067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1321292984422190917099381 123871217289580398478067)
                    ·
                      rfl

theorem cell23_723715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 5].length) (baseStart_723715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723715 prefixEnd_723715 := by exact prefixLift 723715
  have htrace : WordTrace (prefixWord ++ tailWord_723715) baseStart_723715 baseEnd_723715 := by
    simpa [prefixWord, tailWord_723715, baseEnd_723715] using wordTrace_append hprefix tailTrace_723715
  have hstable : (prefixWord ++ tailWord_723715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723715).length < 2 ^ (prefixWord ++ tailWord_723715).sum := by decide
  have hdescent : baseEnd_723715 < baseStart_723715 := by decide
  rcases family_descends (prefixWord ++ tailWord_723715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723772 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_723772 : Nat := 118140960795 + 723772 * 2 ^ 59
def prefixEnd_723772 : Nat := 4983230072969 + 3 ^ 40 * 723772 * 2
def baseEnd_723772 : Nat := 371642920266047472421439

theorem tailTrace_723772 : CollatzResearch.WordTrace tailWord_723772 prefixEnd_723772 371642920266047472421439 := by
  unfold tailWord_723772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13199066766952564630790785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17598755689270086174387713 13199066766952564630790785)
  ·
    refine ⟨9899300075214423473093089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13199066766952564630790785 9899300075214423473093089)
    ·
      refine ⟨7424475056410817604819817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9899300075214423473093089 7424475056410817604819817)
      ·
        refine ⟨5568356292308113203614863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7424475056410817604819817 5568356292308113203614863)
        ·
          refine ⟨8352534438462169805422295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5568356292308113203614863 8352534438462169805422295)
          ·
            refine ⟨12528801657693254708133443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8352534438462169805422295 12528801657693254708133443)
            ·
              refine ⟨18793202486539882062200165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12528801657693254708133443 18793202486539882062200165)
              ·
                refine ⟨3523725466226227886662531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18793202486539882062200165 3523725466226227886662531)
                ·
                  refine ⟨5285588199339341829993797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523725466226227886662531 5285588199339341829993797)
                  ·
                    refine ⟨991047787376126593123837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5285588199339341829993797 991047787376126593123837)
                    ·
                      refine ⟨371642920266047472421439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 991047787376126593123837 371642920266047472421439)
                      ·
                        rfl

theorem cell23_723772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_723772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723772 prefixEnd_723772 := by exact prefixLift 723772
  have htrace : WordTrace (prefixWord ++ tailWord_723772) baseStart_723772 baseEnd_723772 := by
    simpa [prefixWord, tailWord_723772, baseEnd_723772] using wordTrace_append hprefix tailTrace_723772
  have hstable : (prefixWord ++ tailWord_723772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723772).length < 2 ^ (prefixWord ++ tailWord_723772).sum := by decide
  have hdescent : baseEnd_723772 < baseStart_723772 := by decide
  rcases family_descends (prefixWord ++ tailWord_723772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723795 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 6]
def baseStart_723795 : Nat := 118140960795 + 723795 * 2 ^ 59
def prefixEnd_723795 : Nat := 4983230072969 + 3 ^ 40 * 723795 * 2
def baseEnd_723795 : Nat := 371654730321100882433833

theorem tailTrace_723795 : CollatzResearch.WordTrace tailWord_723795 prefixEnd_723795 371654730321100882433833 := by
  unfold tailWord_723795
  simp only [CollatzResearch.WordTrace]
  refine ⟨26398972412821804189668839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17599314941881202793112559 26398972412821804189668839)
  ·
    refine ⟨39598458619232706284503259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26398972412821804189668839 39598458619232706284503259)
    ·
      refine ⟨59397687928849059426754889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39598458619232706284503259 59397687928849059426754889)
      ·
        refine ⟨44548265946636794570066167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59397687928849059426754889 44548265946636794570066167)
        ·
          refine ⟨66822398919955191855099251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44548265946636794570066167 66822398919955191855099251)
          ·
            refine ⟨100233598379932787782648877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66822398919955191855099251 100233598379932787782648877)
            ·
              refine ⟨37587599392474795418493329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100233598379932787782648877 37587599392474795418493329)
              ·
                refine ⟨28190699544356096563869997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37587599392474795418493329 28190699544356096563869997)
                ·
                  refine ⟨10571512329133536211451249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28190699544356096563869997 10571512329133536211451249)
                  ·
                    refine ⟨7928634246850152158588437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10571512329133536211451249 7928634246850152158588437)
                    ·
                      refine ⟨371654730321100882433833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7928634246850152158588437 371654730321100882433833)
                      ·
                        rfl

theorem cell23_723795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_723795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723795 prefixEnd_723795 := by exact prefixLift 723795
  have htrace : WordTrace (prefixWord ++ tailWord_723795) baseStart_723795 baseEnd_723795 := by
    simpa [prefixWord, tailWord_723795, baseEnd_723795] using wordTrace_append hprefix tailTrace_723795
  have hstable : (prefixWord ++ tailWord_723795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723795).length < 2 ^ (prefixWord ++ tailWord_723795).sum := by decide
  have hdescent : baseEnd_723795 < baseStart_723795 := by decide
  rcases family_descends (prefixWord ++ tailWord_723795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723812 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_723812 : Nat := 118140960795 + 723812 * 2 ^ 59
def prefixEnd_723812 : Nat := 4983230072969 + 3 ^ 40 * 723812 * 2
def baseEnd_723812 : Nat := 371663459492227315921255

theorem tailTrace_723812 : CollatzResearch.WordTrace tailWord_723812 prefixEnd_723812 371663459492227315921255 := by
  unfold tailWord_723812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13199796226880108046518845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17599728302506810728691793 13199796226880108046518845)
  ·
    refine ⟨4949923585080040517444567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13199796226880108046518845 4949923585080040517444567)
    ·
      refine ⟨7424885377620060776166851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4949923585080040517444567 7424885377620060776166851)
      ·
        refine ⟨11137328066430091164250277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7424885377620060776166851 11137328066430091164250277)
        ·
          refine ⟨2088249012455642093296927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11137328066430091164250277 2088249012455642093296927)
          ·
            refine ⟨3132373518683463139945391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088249012455642093296927 3132373518683463139945391)
            ·
              refine ⟨4698560278025194709918087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3132373518683463139945391 4698560278025194709918087)
              ·
                refine ⟨7047840417037792064877131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4698560278025194709918087 7047840417037792064877131)
                ·
                  refine ⟨10571760625556688097315697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7047840417037792064877131 10571760625556688097315697)
                  ·
                    refine ⟨7928820469167516072986773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10571760625556688097315697 7928820469167516072986773)
                    ·
                      refine ⟨371663459492227315921255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7928820469167516072986773 371663459492227315921255)
                      ·
                        rfl

theorem cell23_723812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_723812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723812 prefixEnd_723812 := by exact prefixLift 723812
  have htrace : WordTrace (prefixWord ++ tailWord_723812) baseStart_723812 baseEnd_723812 := by
    simpa [prefixWord, tailWord_723812, baseEnd_723812] using wordTrace_append hprefix tailTrace_723812
  have hstable : (prefixWord ++ tailWord_723812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723812).length < 2 ^ (prefixWord ++ tailWord_723812).sum := by decide
  have hdescent : baseEnd_723812 < baseStart_723812 := by decide
  rcases family_descends (prefixWord ++ tailWord_723812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723819 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 3, 1, 3]
def baseStart_723819 : Nat := 118140960795 + 723819 * 2 ^ 59
def prefixEnd_723819 : Nat := 4983230072969 + 3 ^ 40 * 723819 * 2
def baseEnd_723819 : Nat := 371667053856808788533723

theorem tailTrace_723819 : CollatzResearch.WordTrace tailWord_723819 prefixEnd_723819 371667053856808788533723 := by
  unfold tailWord_723819
  simp only [CollatzResearch.WordTrace]
  refine ⟨26399847764734856288542511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17599898509823237525695007 26399847764734856288542511)
  ·
    refine ⟨39599771647102284432813767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26399847764734856288542511 39599771647102284432813767)
    ·
      refine ⟨59399657470653426649220651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39599771647102284432813767 59399657470653426649220651)
      ·
        refine ⟨89099486205980139973830977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59399657470653426649220651 89099486205980139973830977)
        ·
          refine ⟨66824614654485104980373233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89099486205980139973830977 66824614654485104980373233)
          ·
            refine ⟨50118460990863828735279925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66824614654485104980373233 50118460990863828735279925)
            ·
              refine ⟨4698605717893483943932493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50118460990863828735279925 4698605717893483943932493)
              ·
                refine ⟨1761977144210056478974685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4698605717893483943932493 1761977144210056478974685)
                ·
                  refine ⟨660741429078771179615507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1761977144210056478974685 660741429078771179615507)
                  ·
                    refine ⟨991112143618156769423261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 660741429078771179615507 991112143618156769423261)
                    ·
                      refine ⟨371667053856808788533723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 991112143618156769423261 371667053856808788533723)
                      ·
                        rfl

theorem cell23_723819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 1, 3].length) (baseStart_723819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723819 prefixEnd_723819 := by exact prefixLift 723819
  have htrace : WordTrace (prefixWord ++ tailWord_723819) baseStart_723819 baseEnd_723819 := by
    simpa [prefixWord, tailWord_723819, baseEnd_723819] using wordTrace_append hprefix tailTrace_723819
  have hstable : (prefixWord ++ tailWord_723819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723819).length < 2 ^ (prefixWord ++ tailWord_723819).sum := by decide
  have hdescent : baseEnd_723819 < baseStart_723819 := by decide
  rcases family_descends (prefixWord ++ tailWord_723819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723852 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_723852 : Nat := 118140960795 + 723852 * 2 ^ 59
def prefixEnd_723852 : Nat := 4983230072969 + 3 ^ 40 * 723852 * 2
def baseEnd_723852 : Nat := 123894666239469053140357

theorem tailTrace_723852 : CollatzResearch.WordTrace tailWord_723852 prefixEnd_723852 123894666239469053140357 := by
  unfold tailWord_723852
  simp only [CollatzResearch.WordTrace]
  refine ⟨13200525686807651462246905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17600700915743535282995873 13200525686807651462246905)
  ·
    refine ⟨9900394265105738596685179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13200525686807651462246905 9900394265105738596685179)
    ·
      refine ⟨14850591397658607895027769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9900394265105738596685179 14850591397658607895027769)
      ·
        refine ⟨11137943548243955921270827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14850591397658607895027769 11137943548243955921270827)
        ·
          refine ⟨16706915322365933881906241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11137943548243955921270827 16706915322365933881906241)
          ·
            refine ⟨12530186491774450411429681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16706915322365933881906241 12530186491774450411429681)
            ·
              refine ⟨9397639868830837808572261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12530186491774450411429681 9397639868830837808572261)
              ·
                refine ⟨1762057475405782089107299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9397639868830837808572261 1762057475405782089107299)
                ·
                  refine ⟨2643086213108673133660949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762057475405782089107299 2643086213108673133660949)
                  ·
                    refine ⟨123894666239469053140357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2643086213108673133660949 123894666239469053140357)
                    ·
                      rfl

theorem cell23_723852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_723852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723852 prefixEnd_723852 := by exact prefixLift 723852
  have htrace : WordTrace (prefixWord ++ tailWord_723852) baseStart_723852 baseEnd_723852 := by
    simpa [prefixWord, tailWord_723852, baseEnd_723852] using wordTrace_append hprefix tailTrace_723852
  have hstable : (prefixWord ++ tailWord_723852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723852).length < 2 ^ (prefixWord ++ tailWord_723852).sum := by decide
  have hdescent : baseEnd_723852 < baseStart_723852 := by decide
  rcases family_descends (prefixWord ++ tailWord_723852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723869 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_723869 : Nat := 118140960795 + 723869 * 2 ^ 59
def prefixEnd_723869 : Nat := 4983230072969 + 3 ^ 40 * 723869 * 2
def baseEnd_723869 : Nat := 123897575963177864302831

theorem tailTrace_723869 : CollatzResearch.WordTrace tailWord_723869 prefixEnd_723869 123897575963177864302831 := by
  unfold tailWord_723869
  simp only [CollatzResearch.WordTrace]
  refine ⟨26401671414553714827862661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17601114276369143218575107 26401671414553714827862661)
  ·
    refine ⟨4950313390228821530224249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26401671414553714827862661 4950313390228821530224249)
    ·
      refine ⟨3712735042671616147668187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4950313390228821530224249 3712735042671616147668187)
      ·
        refine ⟨5569102564007424221502281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3712735042671616147668187 5569102564007424221502281)
        ·
          refine ⟨4176826923005568166126711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5569102564007424221502281 4176826923005568166126711)
          ·
            refine ⟨6265240384508352249190067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176826923005568166126711 6265240384508352249190067)
            ·
              refine ⟨9397860576762528373785101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6265240384508352249190067 9397860576762528373785101)
              ·
                refine ⟨3524197716285948140169413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9397860576762528373785101 3524197716285948140169413)
                ·
                  refine ⟨660787071803615276281765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3524197716285948140169413 660787071803615276281765)
                  ·
                    refine ⟨123897575963177864302831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 660787071803615276281765 123897575963177864302831)
                    ·
                      rfl

theorem cell23_723869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_723869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723869 prefixEnd_723869 := by exact prefixLift 723869
  have htrace : WordTrace (prefixWord ++ tailWord_723869) baseStart_723869 baseEnd_723869 := by
    simpa [prefixWord, tailWord_723869, baseEnd_723869] using wordTrace_append hprefix tailTrace_723869
  have hstable : (prefixWord ++ tailWord_723869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723869).length < 2 ^ (prefixWord ++ tailWord_723869).sum := by decide
  have hdescent : baseEnd_723869 < baseStart_723869 := by decide
  rcases family_descends (prefixWord ++ tailWord_723869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723872 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_723872 : Nat := 118140960795 + 723872 * 2 ^ 59
def prefixEnd_723872 : Nat := 4983230072969 + 3 ^ 40 * 723872 * 2
def baseEnd_723872 : Nat := 371694268331497081170979

theorem tailTrace_723872 : CollatzResearch.WordTrace tailWord_723872 prefixEnd_723872 371694268331497081170979 := by
  unfold tailWord_723872
  simp only [CollatzResearch.WordTrace]
  refine ⟨13200890416771423170110935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17601187222361897560147913 13200890416771423170110935)
  ·
    refine ⟨19801335625157134755166403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13200890416771423170110935 19801335625157134755166403)
    ·
      refine ⟨29702003437735702132749605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19801335625157134755166403 29702003437735702132749605)
      ·
        refine ⟨5569125644575444149890551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29702003437735702132749605 5569125644575444149890551)
        ·
          refine ⟨8353688466863166224835827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5569125644575444149890551 8353688466863166224835827)
          ·
            refine ⟨12530532700294749337253741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8353688466863166224835827 12530532700294749337253741)
            ·
              refine ⟨4698949762610531001470153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12530532700294749337253741 4698949762610531001470153)
              ·
                refine ⟨3524212321957898251102615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4698949762610531001470153 3524212321957898251102615)
                ·
                  refine ⟨5286318482936847376653923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524212321957898251102615 5286318482936847376653923)
                  ·
                    refine ⟨7929477724405271064980885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286318482936847376653923 7929477724405271064980885)
                    ·
                      refine ⟨371694268331497081170979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7929477724405271064980885 371694268331497081170979)
                      ·
                        rfl

theorem cell23_723872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_723872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723872 prefixEnd_723872 := by exact prefixLift 723872
  have htrace : WordTrace (prefixWord ++ tailWord_723872) baseStart_723872 baseEnd_723872 := by
    simpa [prefixWord, tailWord_723872, baseEnd_723872] using wordTrace_append hprefix tailTrace_723872
  have hstable : (prefixWord ++ tailWord_723872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723872).length < 2 ^ (prefixWord ++ tailWord_723872).sum := by decide
  have hdescent : baseEnd_723872 < baseStart_723872 := by decide
  rcases family_descends (prefixWord ++ tailWord_723872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723896 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 1, 2, 3]
def baseStart_723896 : Nat := 118140960795 + 723896 * 2 ^ 59
def prefixEnd_723896 : Nat := 4983230072969 + 3 ^ 40 * 723896 * 2
def baseEnd_723896 : Nat := 371706591867204987270869

theorem tailTrace_723896 : CollatzResearch.WordTrace tailWord_723896 prefixEnd_723896 371706591867204987270869 := by
  unfold tailWord_723896
  simp only [CollatzResearch.WordTrace]
  refine ⟨13201328092727949219547771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17601770790303932292730361 13201328092727949219547771)
  ·
    refine ⟨19801992139091923829321657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13201328092727949219547771 19801992139091923829321657)
    ·
      refine ⟨14851494104318942871991243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19801992139091923829321657 14851494104318942871991243)
      ·
        refine ⟨22277241156478414307986865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14851494104318942871991243 22277241156478414307986865)
        ·
          refine ⟨16707930867358810730990149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22277241156478414307986865 16707930867358810730990149)
          ·
            refine ⟨3132737037629777012060653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16707930867358810730990149 3132737037629777012060653)
            ·
              refine ⟨1174776389111166379522745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3132737037629777012060653 1174776389111166379522745)
              ·
                refine ⟨881082291833374784642059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174776389111166379522745 881082291833374784642059)
                ·
                  refine ⟨1321623437750062176963089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881082291833374784642059 1321623437750062176963089)
                  ·
                    refine ⟨991217578312546632722317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1321623437750062176963089 991217578312546632722317)
                    ·
                      refine ⟨371706591867204987270869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 991217578312546632722317 371706591867204987270869)
                      ·
                        rfl

theorem cell23_723896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_723896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723896 prefixEnd_723896 := by exact prefixLift 723896
  have htrace : WordTrace (prefixWord ++ tailWord_723896) baseStart_723896 baseEnd_723896 := by
    simpa [prefixWord, tailWord_723896, baseEnd_723896] using wordTrace_append hprefix tailTrace_723896
  have hstable : (prefixWord ++ tailWord_723896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723896).length < 2 ^ (prefixWord ++ tailWord_723896).sum := by decide
  have hdescent : baseEnd_723896 < baseStart_723896 := by decide
  rcases family_descends (prefixWord ++ tailWord_723896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723943 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_723943 : Nat := 118140960795 + 723943 * 2 ^ 59
def prefixEnd_723943 : Nat := 4983230072969 + 3 ^ 40 * 723943 * 2
def baseEnd_723943 : Nat := 371730725457966303383153

theorem tailTrace_723943 : CollatzResearch.WordTrace tailWord_723943 prefixEnd_723943 371730725457966303383153 := by
  unfold tailWord_723943
  simp only [CollatzResearch.WordTrace]
  refine ⟨26404370416285625466056483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17602913610857083644037655 26404370416285625466056483)
  ·
    refine ⟨39606555624428438199084725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26404370416285625466056483 39606555624428438199084725)
    ·
      refine ⟨3713114589790166081164193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39606555624428438199084725 3713114589790166081164193)
      ·
        refine ⟨2784835942342624560873145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3713114589790166081164193 2784835942342624560873145)
        ·
          refine ⟨2088626956756968420654859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2784835942342624560873145 2088626956756968420654859)
          ·
            refine ⟨3132940435135452630982289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088626956756968420654859 3132940435135452630982289)
            ·
              refine ⟨2349705326351589473236717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3132940435135452630982289 2349705326351589473236717)
              ·
                refine ⟨881139497381846052463769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2349705326351589473236717 881139497381846052463769)
                ·
                  refine ⟨660854623036384539347827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 881139497381846052463769 660854623036384539347827)
                  ·
                    refine ⟨991281934554576809021741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 660854623036384539347827 991281934554576809021741)
                    ·
                      refine ⟨371730725457966303383153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 991281934554576809021741 371730725457966303383153)
                      ·
                        rfl

theorem cell23_723943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_723943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723943 prefixEnd_723943 := by exact prefixLift 723943
  have htrace : WordTrace (prefixWord ++ tailWord_723943) baseStart_723943 baseEnd_723943 := by
    simpa [prefixWord, tailWord_723943, baseEnd_723943] using wordTrace_append hprefix tailTrace_723943
  have hstable : (prefixWord ++ tailWord_723943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723943).length < 2 ^ (prefixWord ++ tailWord_723943).sum := by decide
  have hdescent : baseEnd_723943 < baseStart_723943 := by decide
  rcases family_descends (prefixWord ++ tailWord_723943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723979 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 4]
def baseStart_723979 : Nat := 118140960795 + 723979 * 2 ^ 59
def prefixEnd_723979 : Nat := 4983230072969 + 3 ^ 40 * 723979 * 2
def baseEnd_723979 : Nat := 371749210761528162532987

theorem tailTrace_723979 : CollatzResearch.WordTrace tailWord_723979 prefixEnd_723979 371749210761528162532987 := by
  unfold tailWord_723979
  simp only [CollatzResearch.WordTrace]
  refine ⟨26405683444155203614366991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17603788962770135742911327 26405683444155203614366991)
  ·
    refine ⟨39608525166232805421550487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26405683444155203614366991 39608525166232805421550487)
    ·
      refine ⟨59412787749349208132325731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39608525166232805421550487 59412787749349208132325731)
      ·
        refine ⟨89119181624023812198488597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59412787749349208132325731 89119181624023812198488597)
        ·
          refine ⟨4177461638626116196804153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89119181624023812198488597 4177461638626116196804153)
          ·
            refine ⟨3133096228969587147603115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4177461638626116196804153 3133096228969587147603115)
            ·
              refine ⟨4699644343454380721404673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133096228969587147603115 4699644343454380721404673)
              ·
                refine ⟨3524733257590785541053505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4699644343454380721404673 3524733257590785541053505)
                ·
                  refine ⟨2643549943193089155790129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3524733257590785541053505 2643549943193089155790129)
                  ·
                    refine ⟨1982662457394816866842597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2643549943193089155790129 1982662457394816866842597)
                    ·
                      refine ⟨371749210761528162532987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1982662457394816866842597 371749210761528162532987)
                      ·
                        rfl

theorem cell23_723979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 4].length) (baseStart_723979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723979 prefixEnd_723979 := by exact prefixLift 723979
  have htrace : WordTrace (prefixWord ++ tailWord_723979) baseStart_723979 baseEnd_723979 := by
    simpa [prefixWord, tailWord_723979, baseEnd_723979] using wordTrace_append hprefix tailTrace_723979
  have hstable : (prefixWord ++ tailWord_723979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723979).length < 2 ^ (prefixWord ++ tailWord_723979).sum := by decide
  have hdescent : baseEnd_723979 < baseStart_723979 := by decide
  rcases family_descends (prefixWord ++ tailWord_723979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723989 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 7]
def baseStart_723989 : Nat := 118140960795 + 723989 * 2 ^ 59
def prefixEnd_723989 : Nat := 4983230072969 + 3 ^ 40 * 723989 * 2
def baseEnd_723989 : Nat := 41306038396452569267549

theorem tailTrace_723989 : CollatzResearch.WordTrace tailWord_723989 prefixEnd_723989 41306038396452569267549 := by
  unfold tailWord_723989
  simp only [CollatzResearch.WordTrace]
  refine ⟨26406048174118975322231021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17604032116079316881487347 26406048174118975322231021)
  ·
    refine ⟨9902268065294615745836633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26406048174118975322231021 9902268065294615745836633)
    ·
      refine ⟨7426701048970961809377475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9902268065294615745836633 7426701048970961809377475)
      ·
        refine ⟨11140051573456442714066213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7426701048970961809377475 11140051573456442714066213)
        ·
          refine ⟨2088759670023083008887415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11140051573456442714066213 2088759670023083008887415)
          ·
            refine ⟨3133139505034624513331123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088759670023083008887415 3133139505034624513331123)
            ·
              refine ⟨4699709257551936769996685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133139505034624513331123 4699709257551936769996685)
              ·
                refine ⟨1762390971581976288748757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4699709257551936769996685 1762390971581976288748757)
                ·
                  refine ⟨41306038396452569267549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1762390971581976288748757 41306038396452569267549)
                  ·
                    rfl

theorem cell23_723989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_723989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_723989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_723989 prefixEnd_723989 := by exact prefixLift 723989
  have htrace : WordTrace (prefixWord ++ tailWord_723989) baseStart_723989 baseEnd_723989 := by
    simpa [prefixWord, tailWord_723989, baseEnd_723989] using wordTrace_append hprefix tailTrace_723989
  have hstable : (prefixWord ++ tailWord_723989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723989).length < 2 ^ (prefixWord ++ tailWord_723989).sum := by decide
  have hdescent : baseEnd_723989 < baseStart_723989 := by decide
  rcases family_descends (prefixWord ++ tailWord_723989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724019 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 2, 5]
def baseStart_724019 : Nat := 118140960795 + 724019 * 2 ^ 59
def prefixEnd_724019 : Nat := 4983230072969 + 3 ^ 40 * 724019 * 2
def baseEnd_724019 : Nat := 123923249995902668677601

theorem tailTrace_724019 : CollatzResearch.WordTrace tailWord_724019 prefixEnd_724019 123923249995902668677601 := by
  unfold tailWord_724019
  simp only [CollatzResearch.WordTrace]
  refine ⟨26407142364010290445823111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17604761576006860297215407 26407142364010290445823111)
  ·
    refine ⟨39610713546015435668734667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26407142364010290445823111 39610713546015435668734667)
    ·
      refine ⟨59416070319023153503102001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39610713546015435668734667 59416070319023153503102001)
      ·
        refine ⟨44562052739267365127326501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59416070319023153503102001 44562052739267365127326501)
        ·
          refine ⟨8355384888612630961373719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44562052739267365127326501 8355384888612630961373719)
          ·
            refine ⟨12533077332918946442060579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8355384888612630961373719 12533077332918946442060579)
            ·
              refine ⟨18799615999378419663090869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12533077332918946442060579 18799615999378419663090869)
              ·
                refine ⟨1762463999941726843414769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18799615999378419663090869 1762463999941726843414769)
                ·
                  refine ⟨1321847999956295132561077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1762463999941726843414769 1321847999956295132561077)
                  ·
                    refine ⟨123923249995902668677601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1321847999956295132561077 123923249995902668677601)
                    ·
                      rfl

theorem cell23_724019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 5].length) (baseStart_724019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724019 prefixEnd_724019 := by exact prefixLift 724019
  have htrace : WordTrace (prefixWord ++ tailWord_724019) baseStart_724019 baseEnd_724019 := by
    simpa [prefixWord, tailWord_724019, baseEnd_724019] using wordTrace_append hprefix tailTrace_724019
  have hstable : (prefixWord ++ tailWord_724019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724019).length < 2 ^ (prefixWord ++ tailWord_724019).sum := by decide
  have hdescent : baseEnd_724019 < baseStart_724019 := by decide
  rcases family_descends (prefixWord ++ tailWord_724019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724056 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 1, 6, 2]
def baseStart_724056 : Nat := 118140960795 + 724056 * 2 ^ 59
def prefixEnd_724056 : Nat := 4983230072969 + 3 ^ 40 * 724056 * 2
def baseEnd_724056 : Nat := 371788748771924361270133

theorem tailTrace_724056 : CollatzResearch.WordTrace tailWord_724056 prefixEnd_724056 371788748771924361270133 := by
  unfold tailWord_724056
  simp only [CollatzResearch.WordTrace]
  refine ⟨13204245932438122882460011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17605661243250830509946681 13204245932438122882460011)
  ·
    refine ⟨19806368898657184323690017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13204245932438122882460011 19806368898657184323690017)
    ·
      refine ⟨14854776673992888242767513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19806368898657184323690017 14854776673992888242767513)
      ·
        refine ⟨11141082505494666182075635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14854776673992888242767513 11141082505494666182075635)
        ·
          refine ⟨16711623758241999273113453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11141082505494666182075635 16711623758241999273113453)
          ·
            refine ⟨6266858909340749727417545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16711623758241999273113453 6266858909340749727417545)
            ·
              refine ⟨4700144182005562295563159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6266858909340749727417545 4700144182005562295563159)
              ·
                refine ⟨7050216273008343443344739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4700144182005562295563159 7050216273008343443344739)
                ·
                  refine ⟨10575324409512515165017109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7050216273008343443344739 10575324409512515165017109)
                  ·
                    refine ⟨495718331695899148360177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10575324409512515165017109 495718331695899148360177)
                    ·
                      refine ⟨371788748771924361270133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 495718331695899148360177 371788748771924361270133)
                      ·
                        rfl

theorem cell23_724056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_724056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724056 prefixEnd_724056 := by exact prefixLift 724056
  have htrace : WordTrace (prefixWord ++ tailWord_724056) baseStart_724056 baseEnd_724056 := by
    simpa [prefixWord, tailWord_724056, baseEnd_724056] using wordTrace_append hprefix tailTrace_724056
  have hstable : (prefixWord ++ tailWord_724056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724056).length < 2 ^ (prefixWord ++ tailWord_724056).sum := by decide
  have hdescent : baseEnd_724056 < baseStart_724056 := by decide
  rcases family_descends (prefixWord ++ tailWord_724056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724086 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_724086 : Nat := 118140960795 + 724086 * 2 ^ 59
def prefixEnd_724086 : Nat := 4983230072969 + 3 ^ 40 * 724086 * 2
def baseEnd_724086 : Nat := 371804153191559243894995

theorem tailTrace_724086 : CollatzResearch.WordTrace tailWord_724086 prefixEnd_724086 371804153191559243894995 := by
  unfold tailWord_724086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1650599128422972555532007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17606390703178373925674741 1650599128422972555532007)
  ·
    refine ⟨2475898692634458833298011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1650599128422972555532007 2475898692634458833298011)
    ·
      refine ⟨3713848038951688249947017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2475898692634458833298011 3713848038951688249947017)
      ·
        refine ⟨2785386029213766187460263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3713848038951688249947017 2785386029213766187460263)
        ·
          refine ⟨4178079043820649281190395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785386029213766187460263 4178079043820649281190395)
          ·
            refine ⟨6267118565730973921785593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178079043820649281190395 6267118565730973921785593)
            ·
              refine ⟨4700338924298230441339195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6267118565730973921785593 4700338924298230441339195)
              ·
                refine ⟨7050508386447345662008793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4700338924298230441339195 7050508386447345662008793)
                ·
                  refine ⟨5287881289835509246506595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7050508386447345662008793 5287881289835509246506595)
                  ·
                    refine ⟨7931821934753263869759893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5287881289835509246506595 7931821934753263869759893)
                    ·
                      refine ⟨371804153191559243894995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7931821934753263869759893 371804153191559243894995)
                      ·
                        rfl

theorem cell23_724086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_724086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724086 prefixEnd_724086 := by exact prefixLift 724086
  have htrace : WordTrace (prefixWord ++ tailWord_724086) baseStart_724086 baseEnd_724086 := by
    simpa [prefixWord, tailWord_724086, baseEnd_724086] using wordTrace_append hprefix tailTrace_724086
  have hstable : (prefixWord ++ tailWord_724086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724086).length < 2 ^ (prefixWord ++ tailWord_724086).sum := by decide
  have hdescent : baseEnd_724086 < baseStart_724086 := by decide
  rcases family_descends (prefixWord ++ tailWord_724086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724099 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 6]
def baseStart_724099 : Nat := 118140960795 + 724099 * 2 ^ 59
def prefixEnd_724099 : Nat := 4983230072969 + 3 ^ 40 * 724099 * 2
def baseEnd_724099 : Nat := 371810828440067693032435

theorem tailTrace_724099 : CollatzResearch.WordTrace tailWord_724099 prefixEnd_724099 371810828440067693032435 := by
  unfold tailWord_724099
  simp only [CollatzResearch.WordTrace]
  refine ⟨26410060203720464108735351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17606706802480309405823567 26410060203720464108735351)
  ·
    refine ⟨39615090305580696163103027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26410060203720464108735351 39615090305580696163103027)
    ·
      refine ⟨59422635458371044244654541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39615090305580696163103027 59422635458371044244654541)
      ·
        refine ⟨22283488296889141591745453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59422635458371044244654541 22283488296889141591745453)
        ·
          refine ⟨8356308111333428096904545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22283488296889141591745453 8356308111333428096904545)
          ·
            refine ⟨6267231083500071072678409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8356308111333428096904545 6267231083500071072678409)
            ·
              refine ⟨4700423312625053304508807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6267231083500071072678409 4700423312625053304508807)
              ·
                refine ⟨7050634968937579956763211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4700423312625053304508807 7050634968937579956763211)
                ·
                  refine ⟨10575952453406369935144817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7050634968937579956763211 10575952453406369935144817)
                  ·
                    refine ⟨7931964340054777451358613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10575952453406369935144817 7931964340054777451358613)
                    ·
                      refine ⟨371810828440067693032435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7931964340054777451358613 371810828440067693032435)
                      ·
                        rfl

theorem cell23_724099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_724099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724099 prefixEnd_724099 := by exact prefixLift 724099
  have htrace : WordTrace (prefixWord ++ tailWord_724099) baseStart_724099 baseEnd_724099 := by
    simpa [prefixWord, tailWord_724099, baseEnd_724099] using wordTrace_append hprefix tailTrace_724099
  have hstable : (prefixWord ++ tailWord_724099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724099).length < 2 ^ (prefixWord ++ tailWord_724099).sum := by decide
  have hdescent : baseEnd_724099 < baseStart_724099 := by decide
  rcases family_descends (prefixWord ++ tailWord_724099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724100 : List Nat := [2, 3, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_724100 : Nat := 118140960795 + 724100 * 2 ^ 59
def prefixEnd_724100 : Nat := 4983230072969 + 3 ^ 40 * 724100 * 2
def baseEnd_724100 : Nat := 123937113973574063039977

theorem tailTrace_724100 : CollatzResearch.WordTrace tailWord_724100 prefixEnd_724100 123937113973574063039977 := by
  unfold tailWord_724100
  simp only [CollatzResearch.WordTrace]
  refine ⟨13205048338358420639760877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17606731117811227519681169 13205048338358420639760877)
  ·
    refine ⟨4951893126884407739910329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13205048338358420639760877 4951893126884407739910329)
    ·
      refine ⟨3713919845163305804932747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4951893126884407739910329 3713919845163305804932747)
      ·
        refine ⟨5570879767744958707399121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3713919845163305804932747 5570879767744958707399121)
        ·
          refine ⟨4178159825808719030549341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5570879767744958707399121 4178159825808719030549341)
          ·
            refine ⟨1566809934678269636456003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4178159825808719030549341 1566809934678269636456003)
            ·
              refine ⟨2350214902017404454684005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566809934678269636456003 2350214902017404454684005)
              ·
                refine ⟨440665294128263335253251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2350214902017404454684005 440665294128263335253251)
                ·
                  refine ⟨660997941192395002879877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440665294128263335253251 660997941192395002879877)
                  ·
                    refine ⟨123937113973574063039977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 660997941192395002879877 123937113973574063039977)
                    ·
                      rfl

theorem cell23_724100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_724100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724100 prefixEnd_724100 := by exact prefixLift 724100
  have htrace : WordTrace (prefixWord ++ tailWord_724100) baseStart_724100 baseEnd_724100 := by
    simpa [prefixWord, tailWord_724100, baseEnd_724100] using wordTrace_append hprefix tailTrace_724100
  have hstable : (prefixWord ++ tailWord_724100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724100).length < 2 ^ (prefixWord ++ tailWord_724100).sum := by decide
  have hdescent : baseEnd_724100 < baseStart_724100 := by decide
  rcases family_descends (prefixWord ++ tailWord_724100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724127 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 2, 2, 3]
def baseStart_724127 : Nat := 118140960795 + 724127 * 2 ^ 59
def prefixEnd_724127 : Nat := 4983230072969 + 3 ^ 40 * 724127 * 2
def baseEnd_724127 : Nat := 371825205898393583482307

theorem tailTrace_724127 : CollatzResearch.WordTrace tailWord_724127 prefixEnd_724127 371825205898393583482307 := by
  unfold tailWord_724127
  simp only [CollatzResearch.WordTrace]
  refine ⟨26411081447619024890754635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17607387631746016593836423 26411081447619024890754635)
  ·
    refine ⟨39616622171428537336131953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26411081447619024890754635 39616622171428537336131953)
    ·
      refine ⟨29712466628571403002098965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39616622171428537336131953 29712466628571403002098965)
      ·
        refine ⟨1392771873214284515723389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29712466628571403002098965 1392771873214284515723389)
        ·
          refine ⟨522289452455356693396271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1392771873214284515723389 522289452455356693396271)
          ·
            refine ⟨783434178683035040094407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522289452455356693396271 783434178683035040094407)
            ·
              refine ⟨1175151268024552560141611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783434178683035040094407 1175151268024552560141611)
              ·
                refine ⟨1762726902036828840212417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175151268024552560141611 1762726902036828840212417)
                ·
                  refine ⟨1322045176527621630159313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1762726902036828840212417 1322045176527621630159313)
                  ·
                    refine ⟨991533882395716222619485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1322045176527621630159313 991533882395716222619485)
                    ·
                      refine ⟨371825205898393583482307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 991533882395716222619485 371825205898393583482307)
                      ·
                        rfl

theorem cell23_724127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_724127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724127 prefixEnd_724127 := by exact prefixLift 724127
  have htrace : WordTrace (prefixWord ++ tailWord_724127) baseStart_724127 baseEnd_724127 := by
    simpa [prefixWord, tailWord_724127, baseEnd_724127] using wordTrace_append hprefix tailTrace_724127
  have hstable : (prefixWord ++ tailWord_724127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724127).length < 2 ^ (prefixWord ++ tailWord_724127).sum := by decide
  have hdescent : baseEnd_724127 < baseStart_724127 := by decide
  rcases family_descends (prefixWord ++ tailWord_724127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724133 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 1, 5, 2]
def baseStart_724133 : Nat := 118140960795 + 724133 * 2 ^ 59
def prefixEnd_724133 : Nat := 4983230072969 + 3 ^ 40 * 724133 * 2
def baseEnd_724133 : Nat := 371828286782320560007279

theorem tailTrace_724133 : CollatzResearch.WordTrace tailWord_724133 prefixEnd_724133 371828286782320560007279 := by
  unfold tailWord_724133
  simp only [CollatzResearch.WordTrace]
  refine ⟨26411300285597287915473053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17607533523731525276982035 26411300285597287915473053)
  ·
    refine ⟨9904237607098982968302395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26411300285597287915473053 9904237607098982968302395)
    ·
      refine ⟨14856356410648474452453593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9904237607098982968302395 14856356410648474452453593)
      ·
        refine ⟨11142267307986355839340195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14856356410648474452453593 11142267307986355839340195)
        ·
          refine ⟨16713400961979533759010293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11142267307986355839340195 16713400961979533759010293)
          ·
            refine ⟨1566881340185581289907215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16713400961979533759010293 1566881340185581289907215)
            ·
              refine ⟨2350322010278371934860823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566881340185581289907215 2350322010278371934860823)
              ·
                refine ⟨3525483015417557902291235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2350322010278371934860823 3525483015417557902291235)
                ·
                  refine ⟨5288224523126336853436853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525483015417557902291235 5288224523126336853436853)
                  ·
                    refine ⟨495771049043094080009705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5288224523126336853436853 495771049043094080009705)
                    ·
                      refine ⟨371828286782320560007279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 495771049043094080009705 371828286782320560007279)
                      ·
                        rfl

theorem cell23_724133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_724133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724133 prefixEnd_724133 := by exact prefixLift 724133
  have htrace : WordTrace (prefixWord ++ tailWord_724133) baseStart_724133 baseEnd_724133 := by
    simpa [prefixWord, tailWord_724133, baseEnd_724133] using wordTrace_append hprefix tailTrace_724133
  have hstable : (prefixWord ++ tailWord_724133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724133).length < 2 ^ (prefixWord ++ tailWord_724133).sum := by decide
  have hdescent : baseEnd_724133 < baseStart_724133 := by decide
  rcases family_descends (prefixWord ++ tailWord_724133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724143 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 1, 5]
def baseStart_724143 : Nat := 118140960795 + 724143 * 2 ^ 59
def prefixEnd_724143 : Nat := 4983230072969 + 3 ^ 40 * 724143 * 2
def baseEnd_724143 : Nat := 123944473862955173627411

theorem tailTrace_724143 : CollatzResearch.WordTrace tailWord_724143 prefixEnd_724143 123944473862955173627411 := by
  unfold tailWord_724143
  simp only [CollatzResearch.WordTrace]
  refine ⟨26411665015561059623337083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17607776677040706415558055 26411665015561059623337083)
  ·
    refine ⟨39617497523341589435005625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26411665015561059623337083 39617497523341589435005625)
    ·
      refine ⟨29713123142506192076254219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39617497523341589435005625 29713123142506192076254219)
      ·
        refine ⟨44569684713759288114381329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29713123142506192076254219 44569684713759288114381329)
        ·
          refine ⟨33427263535319466085785997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44569684713759288114381329 33427263535319466085785997)
          ·
            refine ⟨12535223825744799782169749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33427263535319466085785997 12535223825744799782169749)
            ·
              refine ⟨587588616831787489789207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12535223825744799782169749 587588616831787489789207)
              ·
                refine ⟨881382925247681234683811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587588616831787489789207 881382925247681234683811)
                ·
                  refine ⟨1322074387871521852025717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881382925247681234683811 1322074387871521852025717)
                  ·
                    refine ⟨123944473862955173627411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1322074387871521852025717 123944473862955173627411)
                    ·
                      rfl

theorem cell23_724143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 5].length) (baseStart_724143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724143 prefixEnd_724143 := by exact prefixLift 724143
  have htrace : WordTrace (prefixWord ++ tailWord_724143) baseStart_724143 baseEnd_724143 := by
    simpa [prefixWord, tailWord_724143, baseEnd_724143] using wordTrace_append hprefix tailTrace_724143
  have hstable : (prefixWord ++ tailWord_724143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724143).length < 2 ^ (prefixWord ++ tailWord_724143).sum := by decide
  have hdescent : baseEnd_724143 < baseStart_724143 := by decide
  rcases family_descends (prefixWord ++ tailWord_724143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724179 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 7]
def baseStart_724179 : Nat := 118140960795 + 724179 * 2 ^ 59
def prefixEnd_724179 : Nat := 4983230072969 + 3 ^ 40 * 724179 * 2
def baseEnd_724179 : Nat := 371851906892427380032067

theorem tailTrace_724179 : CollatzResearch.WordTrace tailWord_724179 prefixEnd_724179 371851906892427380032067 := by
  unfold tailWord_724179
  simp only [CollatzResearch.WordTrace]
  refine ⟨26412978043430637771647591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17608652028953758514431727 26412978043430637771647591)
  ·
    refine ⟨39619467065145956657471387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26412978043430637771647591 39619467065145956657471387)
    ·
      refine ⟨59429200597718934986207081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39619467065145956657471387 59429200597718934986207081)
      ·
        refine ⟨44571900448289201239655311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59429200597718934986207081 44571900448289201239655311)
        ·
          refine ⟨66857850672433801859482967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44571900448289201239655311 66857850672433801859482967)
          ·
            refine ⟨100286776008650702789224451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66857850672433801859482967 100286776008650702789224451)
            ·
              refine ⟨150430164012976054183836677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100286776008650702789224451 150430164012976054183836677)
              ·
                refine ⟨28205655752433010159469377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150430164012976054183836677 28205655752433010159469377)
                ·
                  refine ⟨21154241814324757619602033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28205655752433010159469377 21154241814324757619602033)
                  ·
                    refine ⟨15865681360743568214701525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21154241814324757619602033 15865681360743568214701525)
                    ·
                      refine ⟨371851906892427380032067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15865681360743568214701525 371851906892427380032067)
                      ·
                        rfl

theorem cell23_724179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_724179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724179 prefixEnd_724179 := by exact prefixLift 724179
  have htrace : WordTrace (prefixWord ++ tailWord_724179) baseStart_724179 baseEnd_724179 := by
    simpa [prefixWord, tailWord_724179, baseEnd_724179] using wordTrace_append hprefix tailTrace_724179
  have hstable : (prefixWord ++ tailWord_724179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724179).length < 2 ^ (prefixWord ++ tailWord_724179).sum := by decide
  have hdescent : baseEnd_724179 < baseStart_724179 := by decide
  rcases family_descends (prefixWord ++ tailWord_724179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724183 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 1, 2, 3]
def baseStart_724183 : Nat := 118140960795 + 724183 * 2 ^ 59
def prefixEnd_724183 : Nat := 4983230072969 + 3 ^ 40 * 724183 * 2
def baseEnd_724183 : Nat := 371853960815045364382049

theorem tailTrace_724183 : CollatzResearch.WordTrace tailWord_724183 prefixEnd_724183 371853960815045364382049 := by
  unfold tailWord_724183
  simp only [CollatzResearch.WordTrace]
  refine ⟨26413123935416146454793203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17608749290277430969862135 26413123935416146454793203)
  ·
    refine ⟨39619685903124219682189805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26413123935416146454793203 39619685903124219682189805)
    ·
      refine ⟨14857382213671582380821177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39619685903124219682189805 14857382213671582380821177)
      ·
        refine ⟨11143036660253686785615883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14857382213671582380821177 11143036660253686785615883)
        ·
          refine ⟨16714554990380530178423825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11143036660253686785615883 16714554990380530178423825)
          ·
            refine ⟨12535916242785397633817869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16714554990380530178423825 12535916242785397633817869)
            ·
              refine ⟨4700968591044524112681701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12535916242785397633817869 4700968591044524112681701)
              ·
                refine ⟨881431610820848271127819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4700968591044524112681701 881431610820848271127819)
                ·
                  refine ⟨1322147416231272406691729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881431610820848271127819 1322147416231272406691729)
                  ·
                    refine ⟨991610562173454305018797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1322147416231272406691729 991610562173454305018797)
                    ·
                      refine ⟨371853960815045364382049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 991610562173454305018797 371853960815045364382049)
                      ·
                        rfl

theorem cell23_724183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_724183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724183 prefixEnd_724183 := by exact prefixLift 724183
  have htrace : WordTrace (prefixWord ++ tailWord_724183) baseStart_724183 baseEnd_724183 := by
    simpa [prefixWord, tailWord_724183, baseEnd_724183] using wordTrace_append hprefix tailTrace_724183
  have hstable : (prefixWord ++ tailWord_724183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724183).length < 2 ^ (prefixWord ++ tailWord_724183).sum := by decide
  have hdescent : baseEnd_724183 < baseStart_724183 := by decide
  rcases family_descends (prefixWord ++ tailWord_724183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724273 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 2, 4, 3]
def baseStart_724273 : Nat := 118140960795 + 724273 * 2 ^ 59
def prefixEnd_724273 : Nat := 4983230072969 + 3 ^ 40 * 724273 * 2
def baseEnd_724273 : Nat := 371900174073950012256635

theorem tailTrace_724273 : CollatzResearch.WordTrace tailWord_724273 prefixEnd_724273 371900174073950012256635 := by
  unfold tailWord_724273
  simp only [CollatzResearch.WordTrace]
  refine ⟨26416406505090091825569473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17610937670060061217046315 26416406505090091825569473)
  ·
    refine ⟨19812304878817568869177105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26416406505090091825569473 19812304878817568869177105)
    ·
      refine ⟨14859228659113176651882829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19812304878817568869177105 14859228659113176651882829)
      ·
        refine ⟨5572210747167441244456061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14859228659113176651882829 5572210747167441244456061)
        ·
          refine ⟨2089579030187790466671023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5572210747167441244456061 2089579030187790466671023)
          ·
            refine ⟨3134368545281685700006535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089579030187790466671023 3134368545281685700006535)
            ·
              refine ⟨4701552817922528550009803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134368545281685700006535 4701552817922528550009803)
              ·
                refine ⟨7052329226883792825014705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701552817922528550009803 7052329226883792825014705)
                ·
                  refine ⟨5289246920162844618761029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7052329226883792825014705 5289246920162844618761029)
                  ·
                    refine ⟨991733797530533366017693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289246920162844618761029 991733797530533366017693)
                    ·
                      refine ⟨371900174073950012256635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 991733797530533366017693 371900174073950012256635)
                      ·
                        rfl

theorem cell23_724273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_724273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724273 prefixEnd_724273 := by exact prefixLift 724273
  have htrace : WordTrace (prefixWord ++ tailWord_724273) baseStart_724273 baseEnd_724273 := by
    simpa [prefixWord, tailWord_724273, baseEnd_724273] using wordTrace_append hprefix tailTrace_724273
  have hstable : (prefixWord ++ tailWord_724273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724273).length < 2 ^ (prefixWord ++ tailWord_724273).sum := by decide
  have hdescent : baseEnd_724273 < baseStart_724273 := by decide
  rcases family_descends (prefixWord ++ tailWord_724273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724287 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 2, 2, 2]
def baseStart_724287 : Nat := 118140960795 + 724287 * 2 ^ 59
def prefixEnd_724287 : Nat := 4983230072969 + 3 ^ 40 * 724287 * 2
def baseEnd_724287 : Nat := 371907362803112957481571

theorem tailTrace_724287 : CollatzResearch.WordTrace tailWord_724287 prefixEnd_724287 371907362803112957481571 := by
  unfold tailWord_724287
  simp only [CollatzResearch.WordTrace]
  refine ⟨26416917127039372216579115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17611278084692914811052743 26416917127039372216579115)
  ·
    refine ⟨39625375690559058324868673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26416917127039372216579115 39625375690559058324868673)
    ·
      refine ⟨29719031767919293743651505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39625375690559058324868673 29719031767919293743651505)
      ·
        refine ⟨22289273825939470307738629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29719031767919293743651505 22289273825939470307738629)
        ·
          refine ⟨4179238842363650682700993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22289273825939470307738629 4179238842363650682700993)
          ·
            refine ⟨3134429131772738012025745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4179238842363650682700993 3134429131772738012025745)
            ·
              refine ⟨2350821848829553509019309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134429131772738012025745 2350821848829553509019309)
              ·
                refine ⟨881558193311082565882241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2350821848829553509019309 881558193311082565882241)
                ·
                  refine ⟨661168644983311924411681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 881558193311082565882241 661168644983311924411681)
                  ·
                    refine ⟨495876483737483943308761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 661168644983311924411681 495876483737483943308761)
                    ·
                      refine ⟨371907362803112957481571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 495876483737483943308761 371907362803112957481571)
                      ·
                        rfl

theorem cell23_724287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_724287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724287 prefixEnd_724287 := by exact prefixLift 724287
  have htrace : WordTrace (prefixWord ++ tailWord_724287) baseStart_724287 baseEnd_724287 := by
    simpa [prefixWord, tailWord_724287, baseEnd_724287] using wordTrace_append hprefix tailTrace_724287
  have hstable : (prefixWord ++ tailWord_724287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724287).length < 2 ^ (prefixWord ++ tailWord_724287).sum := by decide
  have hdescent : baseEnd_724287 < baseStart_724287 := by decide
  rcases family_descends (prefixWord ++ tailWord_724287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724363 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 3]
def baseStart_724363 : Nat := 118140960795 + 724363 * 2 ^ 59
def prefixEnd_724363 : Nat := 4983230072969 + 3 ^ 40 * 724363 * 2
def baseEnd_724363 : Nat := 371946387332854660131221

theorem tailTrace_724363 : CollatzResearch.WordTrace tailWord_724363 prefixEnd_724363 371946387332854660131221 := by
  unfold tailWord_724363
  simp only [CollatzResearch.WordTrace]
  refine ⟨26419689074764037196345743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17613126049842691464230495 26419689074764037196345743)
  ·
    refine ⟨39629533612146055794518615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26419689074764037196345743 39629533612146055794518615)
    ·
      refine ⟨59444300418219083691777923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39629533612146055794518615 59444300418219083691777923)
      ·
        refine ⟨89166450627328625537666885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59444300418219083691777923 89166450627328625537666885)
        ·
          refine ⟨16718709492624117288312541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89166450627328625537666885 16718709492624117288312541)
          ·
            refine ⟨6269516059734043983117203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16718709492624117288312541 6269516059734043983117203)
            ·
              refine ⟨9404274089601065974675805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6269516059734043983117203 9404274089601065974675805)
              ·
                refine ⟨3526602783600399740503427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9404274089601065974675805 3526602783600399740503427)
                ·
                  refine ⟨5289904175400599610755141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526602783600399740503427 5289904175400599610755141)
                  ·
                    refine ⟨991857032887612427016589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289904175400599610755141 991857032887612427016589)
                    ·
                      refine ⟨371946387332854660131221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 991857032887612427016589 371946387332854660131221)
                      ·
                        rfl

theorem cell23_724363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 3].length) (baseStart_724363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724363 prefixEnd_724363 := by exact prefixLift 724363
  have htrace : WordTrace (prefixWord ++ tailWord_724363) baseStart_724363 baseEnd_724363 := by
    simpa [prefixWord, tailWord_724363, baseEnd_724363] using wordTrace_append hprefix tailTrace_724363
  have hstable : (prefixWord ++ tailWord_724363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724363).length < 2 ^ (prefixWord ++ tailWord_724363).sum := by decide
  have hdescent : baseEnd_724363 < baseStart_724363 := by decide
  rcases family_descends (prefixWord ++ tailWord_724363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724383 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 8]
def baseStart_724383 : Nat := 118140960795 + 724383 * 2 ^ 59
def prefixEnd_724383 : Nat := 4983230072969 + 3 ^ 40 * 724383 * 2
def baseEnd_724383 : Nat := 41328517438438286875681

theorem tailTrace_724383 : CollatzResearch.WordTrace tailWord_724383 prefixEnd_724383 41328517438438286875681 := by
  unfold tailWord_724383
  simp only [CollatzResearch.WordTrace]
  refine ⟨26420418534691580612073803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17613612356461053741382535 26420418534691580612073803)
  ·
    refine ⟨39630627802037370918110705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26420418534691580612073803 39630627802037370918110705)
    ·
      refine ⟨29722970851528028188583029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39630627802037370918110705 29722970851528028188583029)
      ·
        refine ⟨2786528517330752642679659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29722970851528028188583029 2786528517330752642679659)
        ·
          refine ⟨4179792775996128964019489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786528517330752642679659 4179792775996128964019489)
          ·
            refine ⟨3134844581997096723014617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4179792775996128964019489 3134844581997096723014617)
            ·
              refine ⟨2351133436497822542260963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134844581997096723014617 2351133436497822542260963)
              ·
                refine ⟨3526700154746733813391445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351133436497822542260963 3526700154746733813391445)
                ·
                  refine ⟨41328517438438286875681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3526700154746733813391445 41328517438438286875681)
                  ·
                    rfl

theorem cell23_724383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 8].length) (baseStart_724383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724383 prefixEnd_724383 := by exact prefixLift 724383
  have htrace : WordTrace (prefixWord ++ tailWord_724383) baseStart_724383 baseEnd_724383 := by
    simpa [prefixWord, tailWord_724383, baseEnd_724383] using wordTrace_append hprefix tailTrace_724383
  have hstable : (prefixWord ++ tailWord_724383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724383).length < 2 ^ (prefixWord ++ tailWord_724383).sum := by decide
  have hdescent : baseEnd_724383 < baseStart_724383 := by decide
  rcases family_descends (prefixWord ++ tailWord_724383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724430 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_724430 : Nat := 118140960795 + 724430 * 2 ^ 59
def prefixEnd_724430 : Nat := 4983230072969 + 3 ^ 40 * 724430 * 2
def baseEnd_724430 : Nat := 123993596845568632664471

theorem tailTrace_724430 : CollatzResearch.WordTrace tailWord_724430 prefixEnd_724430 123993596845568632664471 := by
  unfold tailWord_724430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302766595690163454879343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17614755177014205092689829 3302766595690163454879343)
  ·
    refine ⟨4954149893535245182319015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3302766595690163454879343 4954149893535245182319015)
    ·
      refine ⟨7431224840302867773478523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4954149893535245182319015 7431224840302867773478523)
      ·
        refine ⟨11146837260454301660217785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7431224840302867773478523 11146837260454301660217785)
        ·
          refine ⟨8360127945340726245163339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11146837260454301660217785 8360127945340726245163339)
          ·
            refine ⟨12540191918011089367745009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8360127945340726245163339 12540191918011089367745009)
            ·
              refine ⟨9405143938508317025808757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12540191918011089367745009 9405143938508317025808757)
              ·
                refine ⟨881732244235154721169571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9405143938508317025808757 881732244235154721169571)
                ·
                  refine ⟨1322598366352732081754357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881732244235154721169571 1322598366352732081754357)
                  ·
                    refine ⟨123993596845568632664471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1322598366352732081754357 123993596845568632664471)
                    ·
                      rfl

theorem cell23_724430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_724430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724430 prefixEnd_724430 := by exact prefixLift 724430
  have htrace : WordTrace (prefixWord ++ tailWord_724430) baseStart_724430 baseEnd_724430 := by
    simpa [prefixWord, tailWord_724430, baseEnd_724430] using wordTrace_append hprefix tailTrace_724430
  have hstable : (prefixWord ++ tailWord_724430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724430).length < 2 ^ (prefixWord ++ tailWord_724430).sum := by decide
  have hdescent : baseEnd_724430 < baseStart_724430 := by decide
  rcases family_descends (prefixWord ++ tailWord_724430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724437 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 2, 3, 2]
def baseStart_724437 : Nat := 118140960795 + 724437 * 2 ^ 59
def prefixEnd_724437 : Nat := 4983230072969 + 3 ^ 40 * 724437 * 2
def baseEnd_724437 : Nat := 371984384901287370605881

theorem tailTrace_724437 : CollatzResearch.WordTrace tailWord_724437 prefixEnd_724437 371984384901287370605881 := by
  unfold tailWord_724437
  simp only [CollatzResearch.WordTrace]
  refine ⟨26422388076495947834539565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17614925384330631889693043 26422388076495947834539565)
  ·
    refine ⟨9908395528685980437952337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26422388076495947834539565 9908395528685980437952337)
    ·
      refine ⟨7431296646514485328464253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9908395528685980437952337 7431296646514485328464253)
      ·
        refine ⟨2786736242442931998174095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7431296646514485328464253 2786736242442931998174095)
        ·
          refine ⟨4180104363664397997261143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786736242442931998174095 4180104363664397997261143)
          ·
            refine ⟨6270156545496596995891715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180104363664397997261143 6270156545496596995891715)
            ·
              refine ⟨9405234818244895493837573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6270156545496596995891715 9405234818244895493837573)
              ·
                refine ⟨1763481528420917905094545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9405234818244895493837573 1763481528420917905094545)
                ·
                  refine ⟨1322611146315688428820909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1763481528420917905094545 1322611146315688428820909)
                  ·
                    refine ⟨495979179868383160807841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1322611146315688428820909 495979179868383160807841)
                    ·
                      refine ⟨371984384901287370605881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 495979179868383160807841 371984384901287370605881)
                      ·
                        rfl

theorem cell23_724437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_724437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724437 prefixEnd_724437 := by exact prefixLift 724437
  have htrace : WordTrace (prefixWord ++ tailWord_724437) baseStart_724437 baseEnd_724437 := by
    simpa [prefixWord, tailWord_724437, baseEnd_724437] using wordTrace_append hprefix tailTrace_724437
  have hstable : (prefixWord ++ tailWord_724437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724437).length < 2 ^ (prefixWord ++ tailWord_724437).sum := by decide
  have hdescent : baseEnd_724437 < baseStart_724437 := by decide
  rcases family_descends (prefixWord ++ tailWord_724437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724438 : List Nat := [5, 2, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_724438 : Nat := 118140960795 + 724438 * 2 ^ 59
def prefixEnd_724438 : Nat := 4983230072969 + 3 ^ 40 * 724438 * 2
def baseEnd_724438 : Nat := 123994966127313955564459

theorem tailTrace_724438 : CollatzResearch.WordTrace tailWord_724438 prefixEnd_724438 123994966127313955564459 := by
  unfold tailWord_724438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651401534343270312832873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17614949699661550003550645 1651401534343270312832873)
  ·
    refine ⟨1238551150757452734624655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1651401534343270312832873 1238551150757452734624655)
    ·
      refine ⟨1857826726136179101936983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1238551150757452734624655 1857826726136179101936983)
      ·
        refine ⟨2786740089204268652905475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857826726136179101936983 2786740089204268652905475)
        ·
          refine ⟨4180110133806402979358213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786740089204268652905475 4180110133806402979358213)
          ·
            refine ⟨783770650088700558629665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4180110133806402979358213 783770650088700558629665)
            ·
              refine ⟨587827987566525418972249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783770650088700558629665 587827987566525418972249)
              ·
                refine ⟨440870990674894064229187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587827987566525418972249 440870990674894064229187)
                ·
                  refine ⟨661306486012341096343781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440870990674894064229187 661306486012341096343781)
                  ·
                    refine ⟨123994966127313955564459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 661306486012341096343781 123994966127313955564459)
                    ·
                      rfl

theorem cell23_724438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_724438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724438 prefixEnd_724438 := by exact prefixLift 724438
  have htrace : WordTrace (prefixWord ++ tailWord_724438) baseStart_724438 baseEnd_724438 := by
    simpa [prefixWord, tailWord_724438, baseEnd_724438] using wordTrace_append hprefix tailTrace_724438
  have hstable : (prefixWord ++ tailWord_724438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724438).length < 2 ^ (prefixWord ++ tailWord_724438).sum := by decide
  have hdescent : baseEnd_724438 < baseStart_724438 := by decide
  rcases family_descends (prefixWord ++ tailWord_724438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724463 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_724463 : Nat := 118140960795 + 724463 * 2 ^ 59
def prefixEnd_724463 : Nat := 4983230072969 + 3 ^ 40 * 724463 * 2
def baseEnd_724463 : Nat := 371997735398304268880761

theorem tailTrace_724463 : CollatzResearch.WordTrace tailWord_724463 prefixEnd_724463 371997735398304268880761 := by
  unfold tailWord_724463
  simp only [CollatzResearch.WordTrace]
  refine ⟨26423336374401754274986043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17615557582934502849990695 26423336374401754274986043)
  ·
    refine ⟨39635004561602631412479065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26423336374401754274986043 39635004561602631412479065)
    ·
      refine ⟨29726253421201973559359299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39635004561602631412479065 29726253421201973559359299)
      ·
        refine ⟨44589380131802960339038949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29726253421201973559359299 44589380131802960339038949)
        ·
          refine ⟨8360508774713055063569803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44589380131802960339038949 8360508774713055063569803)
          ·
            refine ⟨12540763162069582595354705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8360508774713055063569803 12540763162069582595354705)
            ·
              refine ⟨9405572371552186946516029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12540763162069582595354705 9405572371552186946516029)
              ·
                refine ⟨3527089639332070104943511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9405572371552186946516029 3527089639332070104943511)
                ·
                  refine ⟨5290634458998105157415267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527089639332070104943511 5290634458998105157415267)
                  ·
                    refine ⟨7935951688497157736122901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5290634458998105157415267 7935951688497157736122901)
                    ·
                      refine ⟨371997735398304268880761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7935951688497157736122901 371997735398304268880761)
                      ·
                        rfl

theorem cell23_724463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_724463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724463 prefixEnd_724463 := by exact prefixLift 724463
  have htrace : WordTrace (prefixWord ++ tailWord_724463) baseStart_724463 baseEnd_724463 := by
    simpa [prefixWord, tailWord_724463, baseEnd_724463] using wordTrace_append hprefix tailTrace_724463
  have hstable : (prefixWord ++ tailWord_724463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724463).length < 2 ^ (prefixWord ++ tailWord_724463).sum := by decide
  have hdescent : baseEnd_724463 < baseStart_724463 := by decide
  rcases family_descends (prefixWord ++ tailWord_724463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724481 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 1, 5]
def baseStart_724481 : Nat := 118140960795 + 724481 * 2 ^ 59
def prefixEnd_724481 : Nat := 4983230072969 + 3 ^ 40 * 724481 * 2
def baseEnd_724481 : Nat := 124002326016695066151893

theorem tailTrace_724481 : CollatzResearch.WordTrace tailWord_724481 prefixEnd_724481 124002326016695066151893 := by
  unfold tailWord_724481
  simp only [CollatzResearch.WordTrace]
  refine ⟨26423992888336543349141297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17615995258891028899427531 26423992888336543349141297)
  ·
    refine ⟨19817994666252407511855973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26423992888336543349141297 19817994666252407511855973)
    ·
      refine ⟨3715873999922326408472995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19817994666252407511855973 3715873999922326408472995)
      ·
        refine ⟨5573810999883489612709493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3715873999922326408472995 5573810999883489612709493)
        ·
          refine ⟨522544781239077151191515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5573810999883489612709493 522544781239077151191515)
          ·
            refine ⟨783817171858615726787273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522544781239077151191515 783817171858615726787273)
            ·
              refine ⟨587862878893961795090455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783817171858615726787273 587862878893961795090455)
              ·
                refine ⟨881794318340942692635683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587862878893961795090455 881794318340942692635683)
                ·
                  refine ⟨1322691477511414038953525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881794318340942692635683 1322691477511414038953525)
                  ·
                    refine ⟨124002326016695066151893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1322691477511414038953525 124002326016695066151893)
                    ·
                      rfl

theorem cell23_724481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_724481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724481 prefixEnd_724481 := by exact prefixLift 724481
  have htrace : WordTrace (prefixWord ++ tailWord_724481) baseStart_724481 baseEnd_724481 := by
    simpa [prefixWord, tailWord_724481, baseEnd_724481] using wordTrace_append hprefix tailTrace_724481
  have hstable : (prefixWord ++ tailWord_724481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724481).length < 2 ^ (prefixWord ++ tailWord_724481).sum := by decide
  have hdescent : baseEnd_724481 < baseStart_724481 := by decide
  rcases family_descends (prefixWord ++ tailWord_724481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724484 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_724484 : Nat := 118140960795 + 724484 * 2 ^ 59
def prefixEnd_724484 : Nat := 4983230072969 + 3 ^ 40 * 724484 * 2
def baseEnd_724484 : Nat := 372008518492048686718165

theorem tailTrace_724484 : CollatzResearch.WordTrace tailWord_724484 prefixEnd_724484 372008518492048686718165 := by
  unfold tailWord_724484
  simp only [CollatzResearch.WordTrace]
  refine ⟨13212051153662837430750253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17616068204883783241000337 13212051153662837430750253)
  ·
    refine ⟨4954519182623564036531345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13212051153662837430750253 4954519182623564036531345)
    ·
      refine ⟨3715889386967673027398509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4954519182623564036531345 3715889386967673027398509)
      ·
        refine ⟨1393458520112877385274441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3715889386967673027398509 1393458520112877385274441)
        ·
          refine ⟨1045093890084658038955831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1393458520112877385274441 1045093890084658038955831)
          ·
            refine ⟨1567640835126987058433747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045093890084658038955831 1567640835126987058433747)
            ·
              refine ⟨2351461252690480587650621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567640835126987058433747 2351461252690480587650621)
              ·
                refine ⟨881797969758930220368983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2351461252690480587650621 881797969758930220368983)
                ·
                  refine ⟨1322696954638395330553475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881797969758930220368983 1322696954638395330553475)
                  ·
                    refine ⟨1984045431957592995830213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1322696954638395330553475 1984045431957592995830213)
                    ·
                      refine ⟨372008518492048686718165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1984045431957592995830213 372008518492048686718165)
                      ·
                        rfl

theorem cell23_724484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_724484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724484 prefixEnd_724484 := by exact prefixLift 724484
  have htrace : WordTrace (prefixWord ++ tailWord_724484) baseStart_724484 baseEnd_724484 := by
    simpa [prefixWord, tailWord_724484, baseEnd_724484] using wordTrace_append hprefix tailTrace_724484
  have hstable : (prefixWord ++ tailWord_724484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724484).length < 2 ^ (prefixWord ++ tailWord_724484).sum := by decide
  have hdescent : baseEnd_724484 < baseStart_724484 := by decide
  rcases family_descends (prefixWord ++ tailWord_724484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724501 : List Nat := [1, 3, 2, 1, 3, 2, 2, 4, 1, 2, 2]
def baseStart_724501 : Nat := 118140960795 + 724501 * 2 ^ 59
def prefixEnd_724501 : Nat := 4983230072969 + 3 ^ 40 * 724501 * 2
def baseEnd_724501 : Nat := 372017247663175120205587

theorem tailTrace_724501 : CollatzResearch.WordTrace tailWord_724501 prefixEnd_724501 372017247663175120205587 := by
  unfold tailWord_724501
  simp only [CollatzResearch.WordTrace]
  refine ⟨26424722348264086764869357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17616481565509391176579571 26424722348264086764869357)
  ·
    refine ⟨9909270880599032536826009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26424722348264086764869357 9909270880599032536826009)
    ·
      refine ⟨7431953160449274402619507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9909270880599032536826009 7431953160449274402619507)
      ·
        refine ⟨11147929740673911603929261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7431953160449274402619507 11147929740673911603929261)
        ·
          refine ⟨4180473652752716851473473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11147929740673911603929261 4180473652752716851473473)
          ·
            refine ⟨3135355239564537638605105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4180473652752716851473473 3135355239564537638605105)
            ·
              refine ⟨2351516429673403228953829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3135355239564537638605105 2351516429673403228953829)
              ·
                refine ⟨440909330563763105428843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2351516429673403228953829 440909330563763105428843)
                ·
                  refine ⟨661363995845644658143265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440909330563763105428843 661363995845644658143265)
                  ·
                    refine ⟨496022996884233493607449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 661363995845644658143265 496022996884233493607449)
                    ·
                      refine ⟨372017247663175120205587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 496022996884233493607449 372017247663175120205587)
                      ·
                        rfl

theorem cell23_724501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_724501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724501 prefixEnd_724501 := by exact prefixLift 724501
  have htrace : WordTrace (prefixWord ++ tailWord_724501) baseStart_724501 baseEnd_724501 := by
    simpa [prefixWord, tailWord_724501, baseEnd_724501] using wordTrace_append hprefix tailTrace_724501
  have hstable : (prefixWord ++ tailWord_724501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724501).length < 2 ^ (prefixWord ++ tailWord_724501).sum := by decide
  have hdescent : baseEnd_724501 < baseStart_724501 := by decide
  rcases family_descends (prefixWord ++ tailWord_724501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724560 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 3]
def baseStart_724560 : Nat := 118140960795 + 724560 * 2 ^ 59
def prefixEnd_724560 : Nat := 4983230072969 + 3 ^ 40 * 724560 * 2
def baseEnd_724560 : Nat := 372047543021790389367815

theorem tailTrace_724560 : CollatzResearch.WordTrace tailWord_724560 prefixEnd_724560 372047543021790389367815 := by
  unfold tailWord_724560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13213437127525169920633567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17617916170033559894178089 13213437127525169920633567)
  ·
    refine ⟨19820155691287754880950351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13213437127525169920633567 19820155691287754880950351)
    ·
      refine ⟨29730233536931632321425527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19820155691287754880950351 29730233536931632321425527)
      ·
        refine ⟨44595350305397448482138291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29730233536931632321425527 44595350305397448482138291)
        ·
          refine ⟨66893025458096172723207437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44595350305397448482138291 66893025458096172723207437)
          ·
            refine ⟨25084884546786064771202789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66893025458096172723207437 25084884546786064771202789)
            ·
              refine ⟨4703415852522387144600523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25084884546786064771202789 4703415852522387144600523)
              ·
                refine ⟨7055123778783580716900785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4703415852522387144600523 7055123778783580716900785)
                ·
                  refine ⟨5291342834087685537675589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7055123778783580716900785 5291342834087685537675589)
                  ·
                    refine ⟨992126781391441038314173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5291342834087685537675589 992126781391441038314173)
                    ·
                      refine ⟨372047543021790389367815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 992126781391441038314173 372047543021790389367815)
                      ·
                        rfl

theorem cell23_724560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 3].length) (baseStart_724560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724560 prefixEnd_724560 := by exact prefixLift 724560
  have htrace : WordTrace (prefixWord ++ tailWord_724560) baseStart_724560 baseEnd_724560 := by
    simpa [prefixWord, tailWord_724560, baseEnd_724560] using wordTrace_append hprefix tailTrace_724560
  have hstable : (prefixWord ++ tailWord_724560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724560).length < 2 ^ (prefixWord ++ tailWord_724560).sum := by decide
  have hdescent : baseEnd_724560 < baseStart_724560 := by decide
  rcases family_descends (prefixWord ++ tailWord_724560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724563 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 13]
def baseStart_724563 : Nat := 118140960795 + 724563 * 2 ^ 59
def prefixEnd_724563 : Nat := 4983230072969 + 3 ^ 40 * 724563 * 2
def baseEnd_724563 : Nat := 41338787051528208625589

theorem tailTrace_724563 : CollatzResearch.WordTrace tailWord_724563 prefixEnd_724563 41338787051528208625589 := by
  unfold tailWord_724563
  simp only [CollatzResearch.WordTrace]
  refine ⟨26426983674039471353626343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17617989116026314235750895 26426983674039471353626343)
  ·
    refine ⟨39640475511059207030439515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26426983674039471353626343 39640475511059207030439515)
    ·
      refine ⟨59460713266588810545659273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39640475511059207030439515 59460713266588810545659273)
      ·
        refine ⟨44595534949941607909244455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59460713266588810545659273 44595534949941607909244455)
        ·
          refine ⟨66893302424912411863866683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44595534949941607909244455 66893302424912411863866683)
          ·
            refine ⟨100339953637368617795800025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66893302424912411863866683 100339953637368617795800025)
            ·
              refine ⟨75254965228026463346850019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100339953637368617795800025 75254965228026463346850019)
              ·
                refine ⟨112882447842039695020275029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75254965228026463346850019 112882447842039695020275029)
                ·
                  refine ⟨41338787051528208625589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 112882447842039695020275029 41338787051528208625589)
                  ·
                    rfl

theorem cell23_724563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 13].length) (baseStart_724563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724563 prefixEnd_724563 := by exact prefixLift 724563
  have htrace : WordTrace (prefixWord ++ tailWord_724563) baseStart_724563 baseEnd_724563 := by
    simpa [prefixWord, tailWord_724563, baseEnd_724563] using wordTrace_append hprefix tailTrace_724563
  have hstable : (prefixWord ++ tailWord_724563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724563).length < 2 ^ (prefixWord ++ tailWord_724563).sum := by decide
  have hdescent : baseEnd_724563 < baseStart_724563 := by decide
  rcases family_descends (prefixWord ++ tailWord_724563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724570 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_724570 : Nat := 118140960795 + 724570 * 2 ^ 59
def prefixEnd_724570 : Nat := 4983230072969 + 3 ^ 40 * 724570 * 2
def baseEnd_724570 : Nat := 372052677828335350242769

theorem tailTrace_724570 : CollatzResearch.WordTrace tailWord_724570 prefixEnd_724570 372052677828335350242769 := by
  unfold tailWord_724570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6606809746253527887282791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17618159323342741032754109 6606809746253527887282791)
  ·
    refine ⟨9910214619380291830924187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6606809746253527887282791 9910214619380291830924187)
    ·
      refine ⟨14865321929070437746386281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9910214619380291830924187 14865321929070437746386281)
      ·
        refine ⟨11148991446802828309789711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14865321929070437746386281 11148991446802828309789711)
        ·
          refine ⟨16723487170204242464684567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11148991446802828309789711 16723487170204242464684567)
          ·
            refine ⟨25085230755306363697026851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16723487170204242464684567 25085230755306363697026851)
            ·
              refine ⟨37627846132959545545540277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25085230755306363697026851 37627846132959545545540277)
              ·
                refine ⟨3527610574964957394894401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37627846132959545545540277 3527610574964957394894401)
                ·
                  refine ⟨2645707931223718046170801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3527610574964957394894401 2645707931223718046170801)
                  ·
                    refine ⟨1984280948417788534628101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2645707931223718046170801 1984280948417788534628101)
                    ·
                      refine ⟨372052677828335350242769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1984280948417788534628101 372052677828335350242769)
                      ·
                        rfl

theorem cell23_724570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_724570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724570 prefixEnd_724570 := by exact prefixLift 724570
  have htrace : WordTrace (prefixWord ++ tailWord_724570) baseStart_724570 baseEnd_724570 := by
    simpa [prefixWord, tailWord_724570, baseEnd_724570] using wordTrace_append hprefix tailTrace_724570
  have hstable : (prefixWord ++ tailWord_724570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724570).length < 2 ^ (prefixWord ++ tailWord_724570).sum := by decide
  have hdescent : baseEnd_724570 < baseStart_724570 := by decide
  rcases family_descends (prefixWord ++ tailWord_724570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724617 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 2, 5, 2]
def baseStart_724617 : Nat := 118140960795 + 724617 * 2 ^ 59
def prefixEnd_724617 : Nat := 4983230072969 + 3 ^ 40 * 724617 * 2
def baseEnd_724617 : Nat := 372076811419096666355053

theorem tailTrace_724617 : CollatzResearch.WordTrace tailWord_724617 prefixEnd_724617 372076811419096666355053 := by
  unfold tailWord_724617
  simp only [CollatzResearch.WordTrace]
  refine ⟨26428953215843838576092105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17619302143895892384061403 26428953215843838576092105)
  ·
    refine ⟨19821714911882878932069079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26428953215843838576092105 19821714911882878932069079)
    ·
      refine ⟨29732572367824318398103619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19821714911882878932069079 29732572367824318398103619)
      ·
        refine ⟨44598858551736477597155429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29732572367824318398103619 44598858551736477597155429)
        ·
          refine ⟨8362285978450589549466643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44598858551736477597155429 8362285978450589549466643)
          ·
            refine ⟨12543428967675884324199965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8362285978450589549466643 12543428967675884324199965)
            ·
              refine ⟨4703785862878456621574987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12543428967675884324199965 4703785862878456621574987)
              ·
                refine ⟨7055678794317684932362481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4703785862878456621574987 7055678794317684932362481)
                ·
                  refine ⟨5291759095738263699271861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7055678794317684932362481 5291759095738263699271861)
                  ·
                    refine ⟨496102415225462221806737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5291759095738263699271861 496102415225462221806737)
                    ·
                      refine ⟨372076811419096666355053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 496102415225462221806737 372076811419096666355053)
                      ·
                        rfl

theorem cell23_724617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 5, 2].length) (baseStart_724617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724617 prefixEnd_724617 := by exact prefixLift 724617
  have htrace : WordTrace (prefixWord ++ tailWord_724617) baseStart_724617 baseEnd_724617 := by
    simpa [prefixWord, tailWord_724617, baseEnd_724617] using wordTrace_append hprefix tailTrace_724617
  have hstable : (prefixWord ++ tailWord_724617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724617).length < 2 ^ (prefixWord ++ tailWord_724617).sum := by decide
  have hdescent : baseEnd_724617 < baseStart_724617 := by decide
  rcases family_descends (prefixWord ++ tailWord_724617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724620 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_724620 : Nat := 118140960795 + 724620 * 2 ^ 59
def prefixEnd_724620 : Nat := 4983230072969 + 3 ^ 40 * 724620 * 2
def baseEnd_724620 : Nat := 372078351861060154617539

theorem tailTrace_724620 : CollatzResearch.WordTrace tailWord_724620 prefixEnd_724620 372078351861060154617539 := by
  unfold tailWord_724620
  simp only [CollatzResearch.WordTrace]
  refine ⟨13214531317416485044225657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17619375089888646725634209 13214531317416485044225657)
  ·
    refine ⟨9910898488062363783169243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13214531317416485044225657 9910898488062363783169243)
    ·
      refine ⟨14866347732093545674753865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9910898488062363783169243 14866347732093545674753865)
      ·
        refine ⟨11149760799070159256065399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14866347732093545674753865 11149760799070159256065399)
        ·
          refine ⟨16724641198605238884098099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11149760799070159256065399 16724641198605238884098099)
          ·
            refine ⟨25086961797907858326147149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16724641198605238884098099 25086961797907858326147149)
            ·
              refine ⟨9407610674215446872305181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25086961797907858326147149 9407610674215446872305181)
              ·
                refine ⟨3527854002830792577114443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9407610674215446872305181 3527854002830792577114443)
                ·
                  refine ⟨5291781004246188865671665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527854002830792577114443 5291781004246188865671665)
                  ·
                    refine ⟨3968835753184641649253749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5291781004246188865671665 3968835753184641649253749)
                    ·
                      refine ⟨372078351861060154617539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3968835753184641649253749 372078351861060154617539)
                      ·
                        rfl

theorem cell23_724620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_724620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724620 prefixEnd_724620 := by exact prefixLift 724620
  have htrace : WordTrace (prefixWord ++ tailWord_724620) baseStart_724620 baseEnd_724620 := by
    simpa [prefixWord, tailWord_724620, baseEnd_724620] using wordTrace_append hprefix tailTrace_724620
  have hstable : (prefixWord ++ tailWord_724620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724620).length < 2 ^ (prefixWord ++ tailWord_724620).sum := by decide
  have hdescent : baseEnd_724620 < baseStart_724620 := by decide
  rcases family_descends (prefixWord ++ tailWord_724620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724644 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_724644 : Nat := 118140960795 + 724644 * 2 ^ 59
def prefixEnd_724644 : Nat := 4983230072969 + 3 ^ 40 * 724644 * 2
def baseEnd_724644 : Nat := 124030225132256020239143

theorem tailTrace_724644 : CollatzResearch.WordTrace tailWord_724644 prefixEnd_724644 124030225132256020239143 := by
  unfold tailWord_724644
  simp only [CollatzResearch.WordTrace]
  refine ⟨13214968993373011093662493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17619958657830681458216657 13214968993373011093662493)
  ·
    refine ⟨4955613372514879160123435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13214968993373011093662493 4955613372514879160123435)
    ·
      refine ⟨7433420058772318740185153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4955613372514879160123435 7433420058772318740185153)
      ·
        refine ⟨5575065044079239055138865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7433420058772318740185153 5575065044079239055138865)
        ·
          refine ⟨4181298783059429291354149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5575065044079239055138865 4181298783059429291354149)
          ·
            refine ⟨783993521823642992128903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4181298783059429291354149 783993521823642992128903)
            ·
              refine ⟨1175990282735464488193355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783993521823642992128903 1175990282735464488193355)
              ·
                refine ⟨1763985424103196732290033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175990282735464488193355 1763985424103196732290033)
                ·
                  refine ⟨1322989068077397549217525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1763985424103196732290033 1322989068077397549217525)
                  ·
                    refine ⟨124030225132256020239143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1322989068077397549217525 124030225132256020239143)
                    ·
                      rfl

theorem cell23_724644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_724644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724644 prefixEnd_724644 := by exact prefixLift 724644
  have htrace : WordTrace (prefixWord ++ tailWord_724644) baseStart_724644 baseEnd_724644 := by
    simpa [prefixWord, tailWord_724644, baseEnd_724644] using wordTrace_append hprefix tailTrace_724644
  have hstable : (prefixWord ++ tailWord_724644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724644).length < 2 ^ (prefixWord ++ tailWord_724644).sum := by decide
  have hdescent : baseEnd_724644 < baseStart_724644 := by decide
  rcases family_descends (prefixWord ++ tailWord_724644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724667 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 3]
def baseStart_724667 : Nat := 118140960795 + 724667 * 2 ^ 59
def prefixEnd_724667 : Nat := 4983230072969 + 3 ^ 40 * 724667 * 2
def baseEnd_724667 : Nat := 372102485451821470729823

theorem tailTrace_724667 : CollatzResearch.WordTrace tailWord_724667 prefixEnd_724667 372102485451821470729823 := by
  unfold tailWord_724667
  simp only [CollatzResearch.WordTrace]
  refine ⟨26430776865662697115412255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17620517910441798076941503 26430776865662697115412255)
  ·
    refine ⟨39646165298494045673118383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26430776865662697115412255 39646165298494045673118383)
    ·
      refine ⟨59469247947741068509677575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39646165298494045673118383 59469247947741068509677575)
      ·
        refine ⟨89203871921611602764516363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59469247947741068509677575 89203871921611602764516363)
        ·
          refine ⟨133805807882417404146774545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89203871921611602764516363 133805807882417404146774545)
          ·
            refine ⟨100354355911813053110080909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133805807882417404146774545 100354355911813053110080909)
            ·
              refine ⟨37632883466929894916280341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100354355911813053110080909 37632883466929894916280341)
              ·
                refine ⟨1764041412512338824200641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37632883466929894916280341 1764041412512338824200641)
                ·
                  refine ⟨1323031059384254118150481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1764041412512338824200641 1323031059384254118150481)
                  ·
                    refine ⟨992273294538190588612861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1323031059384254118150481 992273294538190588612861)
                    ·
                      refine ⟨372102485451821470729823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 992273294538190588612861 372102485451821470729823)
                      ·
                        rfl

theorem cell23_724667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 3].length) (baseStart_724667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724667 prefixEnd_724667 := by exact prefixLift 724667
  have htrace : WordTrace (prefixWord ++ tailWord_724667) baseStart_724667 baseEnd_724667 := by
    simpa [prefixWord, tailWord_724667, baseEnd_724667] using wordTrace_append hprefix tailTrace_724667
  have hstable : (prefixWord ++ tailWord_724667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724667).length < 2 ^ (prefixWord ++ tailWord_724667).sum := by decide
  have hdescent : baseEnd_724667 < baseStart_724667 := by decide
  rcases family_descends (prefixWord ++ tailWord_724667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724714 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_724714 : Nat := 118140960795 + 724714 * 2 ^ 59
def prefixEnd_724714 : Nat := 4983230072969 + 3 ^ 40 * 724714 * 2
def baseEnd_724714 : Nat := 372126619042582786842107

theorem tailTrace_724714 : CollatzResearch.WordTrace tailWord_724714 prefixEnd_724714 372126619042582786842107 := by
  unfold tailWord_724714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6608122774123106035593299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17621660730994949428248797 6608122774123106035593299)
  ·
    refine ⟨9912184161184659053389949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6608122774123106035593299 9912184161184659053389949)
    ·
      refine ⟨3717069060444247145021231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9912184161184659053389949 3717069060444247145021231)
      ·
        refine ⟨5575603590666370717531847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3717069060444247145021231 5575603590666370717531847)
        ·
          refine ⟨8363405385999556076297771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5575603590666370717531847 8363405385999556076297771)
          ·
            refine ⟨12545108078999334114446657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8363405385999556076297771 12545108078999334114446657)
            ·
              refine ⟨9408831059249500585834993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12545108078999334114446657 9408831059249500585834993)
              ·
                refine ⟨7056623294437125439376245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408831059249500585834993 7056623294437125439376245)
                ·
                  refine ⟨661558433853480509941523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7056623294437125439376245 661558433853480509941523)
                  ·
                    refine ⟨992337650780220764912285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 661558433853480509941523 992337650780220764912285)
                    ·
                      refine ⟨372126619042582786842107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 992337650780220764912285 372126619042582786842107)
                      ·
                        rfl

theorem cell23_724714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_724714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724714 prefixEnd_724714 := by exact prefixLift 724714
  have htrace : WordTrace (prefixWord ++ tailWord_724714) baseStart_724714 baseEnd_724714 := by
    simpa [prefixWord, tailWord_724714, baseEnd_724714] using wordTrace_append hprefix tailTrace_724714
  have hstable : (prefixWord ++ tailWord_724714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724714).length < 2 ^ (prefixWord ++ tailWord_724714).sum := by decide
  have hdescent : baseEnd_724714 < baseStart_724714 := by decide
  rcases family_descends (prefixWord ++ tailWord_724714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724794 : List Nat := [3, 1, 1, 1, 5, 3, 1, 8]
def baseStart_724794 : Nat := 118140960795 + 724794 * 2 ^ 59
def prefixEnd_724794 : Nat := 4983230072969 + 3 ^ 40 * 724794 * 2
def baseEnd_724794 : Nat := 13783988796108980512657

theorem tailTrace_724794 : CollatzResearch.WordTrace tailWord_724794 prefixEnd_724794 13783988796108980512657 := by
  unfold tailWord_724794
  simp only [CollatzResearch.WordTrace]
  refine ⟨6608852234050649451321359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17623605957468398536856957 6608852234050649451321359)
  ·
    refine ⟨9913278351075974176982039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6608852234050649451321359 9913278351075974176982039)
    ·
      refine ⟨14869917526613961265473059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9913278351075974176982039 14869917526613961265473059)
      ·
        refine ⟨22304876289920941898209589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14869917526613961265473059 22304876289920941898209589)
        ·
          refine ⟨2091082152180088302957149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22304876289920941898209589 2091082152180088302957149)
          ·
            refine ⟨784155807067533113608931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2091082152180088302957149 784155807067533113608931)
            ·
              refine ⟨1176233710601299670413397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784155807067533113608931 1176233710601299670413397)
              ·
                refine ⟨13783988796108980512657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1176233710601299670413397 13783988796108980512657)
                ·
                  rfl

theorem cell23_724794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 8].length) (baseStart_724794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724794 prefixEnd_724794 := by exact prefixLift 724794
  have htrace : WordTrace (prefixWord ++ tailWord_724794) baseStart_724794 baseEnd_724794 := by
    simpa [prefixWord, tailWord_724794, baseEnd_724794] using wordTrace_append hprefix tailTrace_724794
  have hstable : (prefixWord ++ tailWord_724794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724794).length < 2 ^ (prefixWord ++ tailWord_724794).sum := by decide
  have hdescent : baseEnd_724794 < baseStart_724794 := by decide
  rcases family_descends (prefixWord ++ tailWord_724794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724847 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_724847 : Nat := 118140960795 + 724847 * 2 ^ 59
def prefixEnd_724847 : Nat := 4983230072969 + 3 ^ 40 * 724847 * 2
def baseEnd_724847 : Nat := 372194911969630766478995

theorem tailTrace_724847 : CollatzResearch.WordTrace tailWord_724847 prefixEnd_724847 372194911969630766478995 := by
  unfold tailWord_724847
  simp only [CollatzResearch.WordTrace]
  refine ⟨26437342005010587856964795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17624894670007058571309863 26437342005010587856964795)
  ·
    refine ⟨39656013007515881785447193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26437342005010587856964795 39656013007515881785447193)
    ·
      refine ⟨29742009755636911339085395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39656013007515881785447193 29742009755636911339085395)
      ·
        refine ⟨44613014633455367008628093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29742009755636911339085395 44613014633455367008628093)
        ·
          refine ⟨16729880487545762628235535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44613014633455367008628093 16729880487545762628235535)
          ·
            refine ⟨25094820731318643942353303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16729880487545762628235535 25094820731318643942353303)
            ·
              refine ⟨37642231096977965913529955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25094820731318643942353303 37642231096977965913529955)
              ·
                refine ⟨56463346645466948870294933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37642231096977965913529955 56463346645466948870294933)
                ·
                  refine ⟨2646719374006263228295075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56463346645466948870294933 2646719374006263228295075)
                  ·
                    refine ⟨3970079061009394842442613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2646719374006263228295075 3970079061009394842442613)
                    ·
                      refine ⟨372194911969630766478995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3970079061009394842442613 372194911969630766478995)
                      ·
                        rfl

theorem cell23_724847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_724847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724847 prefixEnd_724847 := by exact prefixLift 724847
  have htrace : WordTrace (prefixWord ++ tailWord_724847) baseStart_724847 baseEnd_724847 := by
    simpa [prefixWord, tailWord_724847, baseEnd_724847] using wordTrace_append hprefix tailTrace_724847
  have hstable : (prefixWord ++ tailWord_724847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724847).length < 2 ^ (prefixWord ++ tailWord_724847).sum := by decide
  have hdescent : baseEnd_724847 < baseStart_724847 := by decide
  rcases family_descends (prefixWord ++ tailWord_724847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724951 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 2, 4, 2]
def baseStart_724951 : Nat := 118140960795 + 724951 * 2 ^ 59
def prefixEnd_724951 : Nat := 4983230072969 + 3 ^ 40 * 724951 * 2
def baseEnd_724951 : Nat := 372248313957698359578517

theorem tailTrace_724951 : CollatzResearch.WordTrace tailWord_724951 prefixEnd_724951 372248313957698359578517 := by
  unfold tailWord_724951
  simp only [CollatzResearch.WordTrace]
  refine ⟨26441135196633813618750707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17627423464422542412500471 26441135196633813618750707)
  ·
    refine ⟨39661702794950720428126061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26441135196633813618750707 39661702794950720428126061)
    ·
      refine ⟨14873138548106520160547273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39661702794950720428126061 14873138548106520160547273)
      ·
        refine ⟨11154853911079890120410455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14873138548106520160547273 11154853911079890120410455)
        ·
          refine ⟨16732280866619835180615683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11154853911079890120410455 16732280866619835180615683)
          ·
            refine ⟨25098421299929752770923525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16732280866619835180615683 25098421299929752770923525)
            ·
              refine ⟨4705953993736828644548161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25098421299929752770923525 4705953993736828644548161)
              ·
                refine ⟨3529465495302621483411121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4705953993736828644548161 3529465495302621483411121)
                ·
                  refine ⟨2647099121476966112558341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3529465495302621483411121 2647099121476966112558341)
                  ·
                    refine ⟨496331085276931146104689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2647099121476966112558341 496331085276931146104689)
                    ·
                      refine ⟨372248313957698359578517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 496331085276931146104689 372248313957698359578517)
                      ·
                        rfl

theorem cell23_724951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_724951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724951 prefixEnd_724951 := by exact prefixLift 724951
  have htrace : WordTrace (prefixWord ++ tailWord_724951) baseStart_724951 baseEnd_724951 := by
    simpa [prefixWord, tailWord_724951, baseEnd_724951] using wordTrace_append hprefix tailTrace_724951
  have hstable : (prefixWord ++ tailWord_724951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724951).length < 2 ^ (prefixWord ++ tailWord_724951).sum := by decide
  have hdescent : baseEnd_724951 < baseStart_724951 := by decide
  rcases family_descends (prefixWord ++ tailWord_724951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725012 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_725012 : Nat := 118140960795 + 725012 * 2 ^ 59
def prefixEnd_725012 : Nat := 4983230072969 + 3 ^ 40 * 725012 * 2
def baseEnd_725012 : Nat := 124093212092540873638579

theorem tailTrace_725012 : CollatzResearch.WordTrace tailWord_725012 prefixEnd_725012 124093212092540873638579 := by
  unfold tailWord_725012
  simp only [CollatzResearch.WordTrace]
  refine ⟨13221680024706410518360645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17628906699608547357814193 13221680024706410518360645)
  ·
    refine ⟨2479065004632451972192621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13221680024706410518360645 2479065004632451972192621)
    ·
      refine ⟨929649376737169489572233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2479065004632451972192621 929649376737169489572233)
      ·
        refine ⟨697237032552877117179175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 929649376737169489572233 697237032552877117179175)
        ·
          refine ⟨1045855548829315675768763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697237032552877117179175 1045855548829315675768763)
          ·
            refine ⟨1568783323243973513653145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045855548829315675768763 1568783323243973513653145)
            ·
              refine ⟨1176587492432980135239859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1568783323243973513653145 1176587492432980135239859)
              ·
                refine ⟨1764881238649470202859789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176587492432980135239859 1764881238649470202859789)
                ·
                  refine ⟨661830464493551326072421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1764881238649470202859789 661830464493551326072421)
                  ·
                    refine ⟨124093212092540873638579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 661830464493551326072421 124093212092540873638579)
                    ·
                      rfl

theorem cell23_725012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_725012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725012 prefixEnd_725012 := by exact prefixLift 725012
  have htrace : WordTrace (prefixWord ++ tailWord_725012) baseStart_725012 baseEnd_725012 := by
    simpa [prefixWord, tailWord_725012, baseEnd_725012] using wordTrace_append hprefix tailTrace_725012
  have hstable : (prefixWord ++ tailWord_725012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725012).length < 2 ^ (prefixWord ++ tailWord_725012).sum := by decide
  have hdescent : baseEnd_725012 < baseStart_725012 := by decide
  rcases family_descends (prefixWord ++ tailWord_725012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725018 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3]
def baseStart_725018 : Nat := 118140960795 + 725018 * 2 ^ 59
def prefixEnd_725018 : Nat := 4983230072969 + 3 ^ 40 * 725018 * 2
def baseEnd_725018 : Nat := 372282717161549597440709

theorem tailTrace_725018 : CollatzResearch.WordTrace tailWord_725018 prefixEnd_725018 372282717161549597440709 := by
  unfold tailWord_725018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6610894721847771015359927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17629052591594056040959805 6610894721847771015359927)
  ·
    refine ⟨9916342082771656523039891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6610894721847771015359927 9916342082771656523039891)
    ·
      refine ⟨14874513124157484784559837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9916342082771656523039891 14874513124157484784559837)
      ·
        refine ⟨5577942421559056794209939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14874513124157484784559837 5577942421559056794209939)
        ·
          refine ⟨8366913632338585191314909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5577942421559056794209939 8366913632338585191314909)
          ·
            refine ⟨3137592612126969446743091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8366913632338585191314909 3137592612126969446743091)
            ·
              refine ⟨4706388918190454170114637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137592612126969446743091 4706388918190454170114637)
              ·
                refine ⟨1764895844321420313792989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4706388918190454170114637 1764895844321420313792989)
                ·
                  refine ⟨661835941620532617672371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1764895844321420313792989 661835941620532617672371)
                  ·
                    refine ⟨992753912430798926508557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 661835941620532617672371 992753912430798926508557)
                    ·
                      refine ⟨372282717161549597440709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 992753912430798926508557 372282717161549597440709)
                      ·
                        rfl

theorem cell23_725018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_725018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725018 prefixEnd_725018 := by exact prefixLift 725018
  have htrace : WordTrace (prefixWord ++ tailWord_725018) baseStart_725018 baseEnd_725018 := by
    simpa [prefixWord, tailWord_725018, baseEnd_725018] using wordTrace_append hprefix tailTrace_725018
  have hstable : (prefixWord ++ tailWord_725018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725018).length < 2 ^ (prefixWord ++ tailWord_725018).sum := by decide
  have hdescent : baseEnd_725018 < baseStart_725018 := by decide
  rcases family_descends (prefixWord ++ tailWord_725018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725038 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_725038 : Nat := 118140960795 + 725038 * 2 ^ 59
def prefixEnd_725038 : Nat := 4983230072969 + 3 ^ 40 * 725038 * 2
def baseEnd_725038 : Nat := 124097662258213173063539

theorem tailTrace_725038 : CollatzResearch.WordTrace tailWord_725038 prefixEnd_725038 124097662258213173063539 := by
  unfold tailWord_725038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3305538543414828434645971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17629538898212418318111845 3305538543414828434645971)
  ·
    refine ⟨4958307815122242651968957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3305538543414828434645971 4958307815122242651968957)
    ·
      refine ⟨1859365430670840994488359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4958307815122242651968957 1859365430670840994488359)
      ·
        refine ⟨2789048146006261491732539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859365430670840994488359 2789048146006261491732539)
        ·
          refine ⟨4183572219009392237598809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2789048146006261491732539 4183572219009392237598809)
          ·
            refine ⟨3137679164257044178199107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4183572219009392237598809 3137679164257044178199107)
            ·
              refine ⟨4706518746385566267298661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137679164257044178199107 4706518746385566267298661)
              ·
                refine ⟨882472264947293675118499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4706518746385566267298661 882472264947293675118499)
                ·
                  refine ⟨1323708397420940512677749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882472264947293675118499 1323708397420940512677749)
                  ·
                    refine ⟨124097662258213173063539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1323708397420940512677749 124097662258213173063539)
                    ·
                      rfl

theorem cell23_725038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_725038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725038 prefixEnd_725038 := by exact prefixLift 725038
  have htrace : WordTrace (prefixWord ++ tailWord_725038) baseStart_725038 baseEnd_725038 := by
    simpa [prefixWord, tailWord_725038, baseEnd_725038] using wordTrace_append hprefix tailTrace_725038
  have hstable : (prefixWord ++ tailWord_725038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725038).length < 2 ^ (prefixWord ++ tailWord_725038).sum := by decide
  have hdescent : baseEnd_725038 < baseStart_725038 := by decide
  rcases family_descends (prefixWord ++ tailWord_725038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725061 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 5, 2, 3]
def baseStart_725061 : Nat := 118140960795 + 725061 * 2 ^ 59
def prefixEnd_725061 : Nat := 4983230072969 + 3 ^ 40 * 725061 * 2
def baseEnd_725061 : Nat := 372304796829692929203011

theorem tailTrace_725061 : CollatzResearch.WordTrace tailWord_725061 prefixEnd_725061 372304796829692929203011 := by
  unfold tailWord_725061
  simp only [CollatzResearch.WordTrace]
  refine ⟨26445147226235302405255037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17630098150823534936836691 26445147226235302405255037)
  ·
    refine ⟨9916930209838238401970639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26445147226235302405255037 9916930209838238401970639)
    ·
      refine ⟨14875395314757357602955959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9916930209838238401970639 14875395314757357602955959)
      ·
        refine ⟨22313092972136036404433939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14875395314757357602955959 22313092972136036404433939)
        ·
          refine ⟨33469639458204054606650909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22313092972136036404433939 33469639458204054606650909)
          ·
            refine ⟨12551114796826520477494091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33469639458204054606650909 12551114796826520477494091)
            ·
              refine ⟨18826672195239780716241137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12551114796826520477494091 18826672195239780716241137)
              ·
                refine ⟨14120004146429835537180853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18826672195239780716241137 14120004146429835537180853)
                ·
                  refine ⟨1323750388727797081610705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14120004146429835537180853 1323750388727797081610705)
                  ·
                    refine ⟨992812791545847811208029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1323750388727797081610705 992812791545847811208029)
                    ·
                      refine ⟨372304796829692929203011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 992812791545847811208029 372304796829692929203011)
                      ·
                        rfl

theorem cell23_725061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_725061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725061 prefixEnd_725061 := by exact prefixLift 725061
  have htrace : WordTrace (prefixWord ++ tailWord_725061) baseStart_725061 baseEnd_725061 := by
    simpa [prefixWord, tailWord_725061, baseEnd_725061] using wordTrace_append hprefix tailTrace_725061
  have hstable : (prefixWord ++ tailWord_725061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725061).length < 2 ^ (prefixWord ++ tailWord_725061).sum := by decide
  have hdescent : baseEnd_725061 < baseStart_725061 := by decide
  rcases family_descends (prefixWord ++ tailWord_725061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725062 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_725062 : Nat := 118140960795 + 725062 * 2 ^ 59
def prefixEnd_725062 : Nat := 4983230072969 + 3 ^ 40 * 725062 * 2
def baseEnd_725062 : Nat := 372305310310347425290507

theorem tailTrace_725062 : CollatzResearch.WordTrace tailWord_725062 prefixEnd_725062 372305310310347425290507 := by
  unfold tailWord_725062
  simp only [CollatzResearch.WordTrace]
  refine ⟨826411990600989986751295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17630122466154453050694293 826411990600989986751295)
  ·
    refine ⟨1239617985901484980126943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 826411990600989986751295 1239617985901484980126943)
    ·
      refine ⟨1859426978852227470190415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1239617985901484980126943 1859426978852227470190415)
      ·
        refine ⟨2789140468278341205285623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859426978852227470190415 2789140468278341205285623)
        ·
          refine ⟨4183710702417511807928435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2789140468278341205285623 4183710702417511807928435)
          ·
            refine ⟨6275566053626267711892653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4183710702417511807928435 6275566053626267711892653)
            ·
              refine ⟨2353337270109850391959745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6275566053626267711892653 2353337270109850391959745)
              ·
                refine ⟨1765002952582387793969809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2353337270109850391959745 1765002952582387793969809)
                ·
                  refine ⟨1323752214436790845477357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1765002952582387793969809 1323752214436790845477357)
                  ·
                    refine ⟨496407080413796567054009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323752214436790845477357 496407080413796567054009)
                    ·
                      refine ⟨372305310310347425290507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 496407080413796567054009 372305310310347425290507)
                      ·
                        rfl

theorem cell23_725062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_725062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725062 prefixEnd_725062 := by exact prefixLift 725062
  have htrace : WordTrace (prefixWord ++ tailWord_725062) baseStart_725062 baseEnd_725062 := by
    simpa [prefixWord, tailWord_725062, baseEnd_725062] using wordTrace_append hprefix tailTrace_725062
  have hstable : (prefixWord ++ tailWord_725062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725062).length < 2 ^ (prefixWord ++ tailWord_725062).sum := by decide
  have hdescent : baseEnd_725062 < baseStart_725062 := by decide
  rcases family_descends (prefixWord ++ tailWord_725062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725069 : List Nat := [1, 6, 1, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_725069 : Nat := 118140960795 + 725069 * 2 ^ 59
def prefixEnd_725069 : Nat := 4983230072969 + 3 ^ 40 * 725069 * 2
def baseEnd_725069 : Nat := 372308904674928897902975

theorem tailTrace_725069 : CollatzResearch.WordTrace tailWord_725069 prefixEnd_725069 372308904674928897902975 := by
  unfold tailWord_725069
  simp only [CollatzResearch.WordTrace]
  refine ⟨26445439010206319771546261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17630292673470879847697507 26445439010206319771546261)
  ·
    refine ⟨1239629953603421239291231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26445439010206319771546261 1239629953603421239291231)
    ·
      refine ⟨1859444930405131858936847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1239629953603421239291231 1859444930405131858936847)
      ·
        refine ⟨2789167395607697788405271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859444930405131858936847 2789167395607697788405271)
        ·
          refine ⟨4183751093411546682607907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2789167395607697788405271 4183751093411546682607907)
          ·
            refine ⟨6275626640117320023911861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4183751093411546682607907 6275626640117320023911861)
            ·
              refine ⟨588339997510998752241737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6275626640117320023911861 588339997510998752241737)
              ·
                refine ⟨441254998133249064181303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588339997510998752241737 441254998133249064181303)
                ·
                  refine ⟨661882497199873596271955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441254998133249064181303 661882497199873596271955)
                  ·
                    refine ⟨992823745799810394407933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 661882497199873596271955 992823745799810394407933)
                    ·
                      refine ⟨372308904674928897902975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 992823745799810394407933 372308904674928897902975)
                      ·
                        rfl

theorem cell23_725069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_725069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725069 prefixEnd_725069 := by exact prefixLift 725069
  have htrace : WordTrace (prefixWord ++ tailWord_725069) baseStart_725069 baseEnd_725069 := by
    simpa [prefixWord, tailWord_725069, baseEnd_725069] using wordTrace_append hprefix tailTrace_725069
  have hstable : (prefixWord ++ tailWord_725069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725069).length < 2 ^ (prefixWord ++ tailWord_725069).sum := by decide
  have hdescent : baseEnd_725069 < baseStart_725069 := by decide
  rcases family_descends (prefixWord ++ tailWord_725069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725125 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 2, 1, 3]
def baseStart_725125 : Nat := 118140960795 + 725125 * 2 ^ 59
def prefixEnd_725125 : Nat := 4983230072969 + 3 ^ 40 * 725125 * 2
def baseEnd_725125 : Nat := 372337659591580678802717

theorem tailTrace_725125 : CollatzResearch.WordTrace tailWord_725125 prefixEnd_725125 372337659591580678802717 := by
  unfold tailWord_725125
  simp only [CollatzResearch.WordTrace]
  refine ⟨26447481498003441335584829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17631654332002294223723219 26447481498003441335584829)
  ·
    refine ⟨9917805561751290500844311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26447481498003441335584829 9917805561751290500844311)
    ·
      refine ⟨14876708342626935751266467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9917805561751290500844311 14876708342626935751266467)
      ·
        refine ⟨22315062513940403626899701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14876708342626935751266467 22315062513940403626899701)
        ·
          refine ⟨2092037110681912840021847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22315062513940403626899701 2092037110681912840021847)
          ·
            refine ⟨3138055666022869260032771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092037110681912840021847 3138055666022869260032771)
            ·
              refine ⟨4707083499034303890049157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138055666022869260032771 4707083499034303890049157)
              ·
                refine ⟨882578156068931979384217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4707083499034303890049157 882578156068931979384217)
                ·
                  refine ⟨661933617051698984538163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 882578156068931979384217 661933617051698984538163)
                  ·
                    refine ⟨992900425577548476807245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 661933617051698984538163 992900425577548476807245)
                    ·
                      refine ⟨372337659591580678802717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 992900425577548476807245 372337659591580678802717)
                      ·
                        rfl

theorem cell23_725125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_725125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725125 prefixEnd_725125 := by exact prefixLift 725125
  have htrace : WordTrace (prefixWord ++ tailWord_725125) baseStart_725125 baseEnd_725125 := by
    simpa [prefixWord, tailWord_725125, baseEnd_725125] using wordTrace_append hprefix tailTrace_725125
  have hstable : (prefixWord ++ tailWord_725125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725125).length < 2 ^ (prefixWord ++ tailWord_725125).sum := by decide
  have hdescent : baseEnd_725125 < baseStart_725125 := by decide
  rcases family_descends (prefixWord ++ tailWord_725125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725141 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_725141 : Nat := 118140960795 + 725141 * 2 ^ 59
def prefixEnd_725141 : Nat := 4983230072969 + 3 ^ 40 * 725141 * 2
def baseEnd_725141 : Nat := 124115291760684205400881

theorem tailTrace_725141 : CollatzResearch.WordTrace tailWord_725141 prefixEnd_725141 124115291760684205400881 := by
  unfold tailWord_725141
  simp only [CollatzResearch.WordTrace]
  refine ⟨26448065065945476068167277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17632043377296984045444851 26448065065945476068167277)
  ·
    refine ⟨9918024399729553525562729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26448065065945476068167277 9918024399729553525562729)
    ·
      refine ⟨7438518299797165144172047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9918024399729553525562729 7438518299797165144172047)
      ·
        refine ⟨11157777449695747716258071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7438518299797165144172047 11157777449695747716258071)
        ·
          refine ⟨16736666174543621574387107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11157777449695747716258071 16736666174543621574387107)
          ·
            refine ⟨25104999261815432361580661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16736666174543621574387107 25104999261815432361580661)
            ·
              refine ⟨2353593680795196783898187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25104999261815432361580661 2353593680795196783898187)
              ·
                refine ⟨3530390521192795175847281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2353593680795196783898187 3530390521192795175847281)
                ·
                  refine ⟨2647792890894596381885461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3530390521192795175847281 2647792890894596381885461)
                  ·
                    refine ⟨124115291760684205400881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2647792890894596381885461 124115291760684205400881)
                    ·
                      rfl

theorem cell23_725141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_725141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725141 prefixEnd_725141 := by exact prefixLift 725141
  have htrace : WordTrace (prefixWord ++ tailWord_725141) baseStart_725141 baseEnd_725141 := by
    simpa [prefixWord, tailWord_725141, baseEnd_725141] using wordTrace_append hprefix tailTrace_725141
  have hstable : (prefixWord ++ tailWord_725141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725141).length < 2 ^ (prefixWord ++ tailWord_725141).sum := by decide
  have hdescent : baseEnd_725141 < baseStart_725141 := by decide
  rcases family_descends (prefixWord ++ tailWord_725141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725188 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 7]
def baseStart_725188 : Nat := 118140960795 + 725188 * 2 ^ 59
def prefixEnd_725188 : Nat := 4983230072969 + 3 ^ 40 * 725188 * 2
def baseEnd_725188 : Nat := 41374445430312659146103

theorem tailTrace_725188 : CollatzResearch.WordTrace tailWord_725188 prefixEnd_725188 41374445430312659146103 := by
  unfold tailWord_725188
  simp only [CollatzResearch.WordTrace]
  refine ⟨13224889648387601547564109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17633186197850135396752145 13224889648387601547564109)
  ·
    refine ⟨4959333618145350580336541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13224889648387601547564109 4959333618145350580336541)
    ·
      refine ⟨1859750106804506467626203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4959333618145350580336541 1859750106804506467626203)
      ·
        refine ⟨2789625160206759701439305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859750106804506467626203 2789625160206759701439305)
        ·
          refine ⟨2092218870155069776079479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2789625160206759701439305 2092218870155069776079479)
          ·
            refine ⟨3138328305232604664119219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092218870155069776079479 3138328305232604664119219)
            ·
              refine ⟨4707492457848906996178829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138328305232604664119219 4707492457848906996178829)
              ·
                refine ⟨1765309671693340123567061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4707492457848906996178829 1765309671693340123567061)
                ·
                  refine ⟨41374445430312659146103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1765309671693340123567061 41374445430312659146103)
                  ·
                    rfl

theorem cell23_725188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_725188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725188 prefixEnd_725188 := by exact prefixLift 725188
  have htrace : WordTrace (prefixWord ++ tailWord_725188) baseStart_725188 baseEnd_725188 := by
    simpa [prefixWord, tailWord_725188, baseEnd_725188] using wordTrace_append hprefix tailTrace_725188
  have hstable : (prefixWord ++ tailWord_725188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725188).length < 2 ^ (prefixWord ++ tailWord_725188).sum := by decide
  have hdescent : baseEnd_725188 < baseStart_725188 := by decide
  rcases family_descends (prefixWord ++ tailWord_725188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725201 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 1, 7]
def baseStart_725201 : Nat := 118140960795 + 725201 * 2 ^ 59
def prefixEnd_725201 : Nat := 4983230072969 + 3 ^ 40 * 725201 * 2
def baseEnd_725201 : Nat := 124125561373774127150789

theorem tailTrace_725201 : CollatzResearch.WordTrace tailWord_725201 prefixEnd_725201 124125561373774127150789 := by
  unfold tailWord_725201
  simp only [CollatzResearch.WordTrace]
  refine ⟨26450253445728106315351457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17633502297152070876900971 26450253445728106315351457)
  ·
    refine ⟨19837690084296079736513593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26450253445728106315351457 19837690084296079736513593)
    ·
      refine ⟨14878267563222059802385195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19837690084296079736513593 14878267563222059802385195)
      ·
        refine ⟨22317401344833089703577793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14878267563222059802385195 22317401344833089703577793)
        ·
          refine ⟨16738051008624817277683345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22317401344833089703577793 16738051008624817277683345)
          ·
            refine ⟨12553538256468612958262509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16738051008624817277683345 12553538256468612958262509)
            ·
              refine ⟨4707576846175729859348441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12553538256468612958262509 4707576846175729859348441)
              ·
                refine ⟨3530682634631797394511331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707576846175729859348441 3530682634631797394511331)
                ·
                  refine ⟨5296023951947696091766997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530682634631797394511331 5296023951947696091766997)
                  ·
                    refine ⟨124125561373774127150789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5296023951947696091766997 124125561373774127150789)
                    ·
                      rfl

theorem cell23_725201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_725201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725201 prefixEnd_725201 := by exact prefixLift 725201
  have htrace : WordTrace (prefixWord ++ tailWord_725201) baseStart_725201 baseEnd_725201 := by
    simpa [prefixWord, tailWord_725201, baseEnd_725201] using wordTrace_append hprefix tailTrace_725201
  have hstable : (prefixWord ++ tailWord_725201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725201).length < 2 ^ (prefixWord ++ tailWord_725201).sum := by decide
  have hdescent : baseEnd_725201 < baseStart_725201 := by decide
  rcases family_descends (prefixWord ++ tailWord_725201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725241 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_725241 : Nat := 118140960795 + 725241 * 2 ^ 59
def prefixEnd_725241 : Nat := 4983230072969 + 3 ^ 40 * 725241 * 2
def baseEnd_725241 : Nat := 372397223347502224952183

theorem tailTrace_725241 : CollatzResearch.WordTrace tailWord_725241 prefixEnd_725241 372397223347502224952183 := by
  unfold tailWord_725241
  simp only [CollatzResearch.WordTrace]
  refine ⟨26451712365583193146807577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17634474910388795431205051 26451712365583193146807577)
  ·
    refine ⟨19838784274187394860105683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26451712365583193146807577 19838784274187394860105683)
    ·
      refine ⟨29758176411281092290158525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19838784274187394860105683 29758176411281092290158525)
      ·
        refine ⟨11159316154230409608809447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29758176411281092290158525 11159316154230409608809447)
        ·
          refine ⟨16738974231345614413214171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11159316154230409608809447 16738974231345614413214171)
          ·
            refine ⟨25108461347018421619821257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16738974231345614413214171 25108461347018421619821257)
            ·
              refine ⟨18831346010263816214865943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25108461347018421619821257 18831346010263816214865943)
              ·
                refine ⟨28247019015395724322298915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18831346010263816214865943 28247019015395724322298915)
                ·
                  refine ⟨42370528523093586483448373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28247019015395724322298915 42370528523093586483448373)
                  ·
                    refine ⟨3972237049040023732823285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42370528523093586483448373 3972237049040023732823285)
                    ·
                      refine ⟨372397223347502224952183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3972237049040023732823285 372397223347502224952183)
                      ·
                        rfl

theorem cell23_725241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_725241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725241 prefixEnd_725241 := by exact prefixLift 725241
  have htrace : WordTrace (prefixWord ++ tailWord_725241) baseStart_725241 baseEnd_725241 := by
    simpa [prefixWord, tailWord_725241, baseEnd_725241] using wordTrace_append hprefix tailTrace_725241
  have hstable : (prefixWord ++ tailWord_725241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725241).length < 2 ^ (prefixWord ++ tailWord_725241).sum := by decide
  have hdescent : baseEnd_725241 < baseStart_725241 := by decide
  rcases family_descends (prefixWord ++ tailWord_725241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725258 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_725258 : Nat := 118140960795 + 725258 * 2 ^ 59
def prefixEnd_725258 : Nat := 4983230072969 + 3 ^ 40 * 725258 * 2
def baseEnd_725258 : Nat := 372405952518628658439605

theorem tailTrace_725258 : CollatzResearch.WordTrace tailWord_725258 prefixEnd_725258 372405952518628658439605 := by
  unfold tailWord_725258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6613083101630401262544107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17634888271014403366784285 6613083101630401262544107)
  ·
    refine ⟨9919624652445601893816161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6613083101630401262544107 9919624652445601893816161)
    ·
      refine ⟨7439718489334201420362121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9919624652445601893816161 7439718489334201420362121)
      ·
        refine ⟨5579788867000651065271591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7439718489334201420362121 5579788867000651065271591)
        ·
          refine ⟨8369683300500976597907387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5579788867000651065271591 8369683300500976597907387)
          ·
            refine ⟨12554524950751464896861081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8369683300500976597907387 12554524950751464896861081)
            ·
              refine ⟨9415893713063598672645811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12554524950751464896861081 9415893713063598672645811)
              ·
                refine ⟨14123840569595398008968717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9415893713063598672645811 14123840569595398008968717)
                ·
                  refine ⟨5296440213598274253363269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14123840569595398008968717 5296440213598274253363269)
                  ·
                    refine ⟨993082540049676422505613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296440213598274253363269 993082540049676422505613)
                    ·
                      refine ⟨372405952518628658439605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 993082540049676422505613 372405952518628658439605)
                      ·
                        rfl

theorem cell23_725258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_725258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725258 prefixEnd_725258 := by exact prefixLift 725258
  have htrace : WordTrace (prefixWord ++ tailWord_725258) baseStart_725258 baseEnd_725258 := by
    simpa [prefixWord, tailWord_725258, baseEnd_725258] using wordTrace_append hprefix tailTrace_725258
  have hstable : (prefixWord ++ tailWord_725258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725258).length < 2 ^ (prefixWord ++ tailWord_725258).sum := by decide
  have hdescent : baseEnd_725258 < baseStart_725258 := by decide
  rcases family_descends (prefixWord ++ tailWord_725258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725308 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_725308 : Nat := 118140960795 + 725308 * 2 ^ 59
def prefixEnd_725308 : Nat := 4983230072969 + 3 ^ 40 * 725308 * 2
def baseEnd_725308 : Nat := 124143875517117820938125

theorem tailTrace_725308 : CollatzResearch.WordTrace tailWord_725308 prefixEnd_725308 124143875517117820938125 := by
  unfold tailWord_725308
  simp only [CollatzResearch.WordTrace]
  refine ⟨13227078028170231794748289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17636104037560309059664385 13227078028170231794748289)
  ·
    refine ⟨9920308521127673846061217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13227078028170231794748289 9920308521127673846061217)
    ·
      refine ⟨7440231390845755384545913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9920308521127673846061217 7440231390845755384545913)
      ·
        refine ⟨5580173543134316538409435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7440231390845755384545913 5580173543134316538409435)
        ·
          refine ⟨8370260314701474807614153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580173543134316538409435 8370260314701474807614153)
          ·
            refine ⟨6277695236026106105710615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8370260314701474807614153 6277695236026106105710615)
            ·
              refine ⟨9416542854039159158565923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6277695236026106105710615 9416542854039159158565923)
              ·
                refine ⟨14124814281058738737848885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9416542854039159158565923 14124814281058738737848885)
                ·
                  refine ⟨1324201338849256756673333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14124814281058738737848885 1324201338849256756673333)
                  ·
                    refine ⟨124143875517117820938125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1324201338849256756673333 124143875517117820938125)
                    ·
                      rfl

theorem cell23_725308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_725308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725308 prefixEnd_725308 := by exact prefixLift 725308
  have htrace : WordTrace (prefixWord ++ tailWord_725308) baseStart_725308 baseEnd_725308 := by
    simpa [prefixWord, tailWord_725308, baseEnd_725308] using wordTrace_append hprefix tailTrace_725308
  have hstable : (prefixWord ++ tailWord_725308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725308).length < 2 ^ (prefixWord ++ tailWord_725308).sum := by decide
  have hdescent : baseEnd_725308 < baseStart_725308 := by decide
  rcases family_descends (prefixWord ++ tailWord_725308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725315 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 4, 3, 2]
def baseStart_725315 : Nat := 118140960795 + 725315 * 2 ^ 59
def prefixEnd_725315 : Nat := 4983230072969 + 3 ^ 40 * 725315 * 2
def baseEnd_725315 : Nat := 372435220915934935426843

theorem tailTrace_725315 : CollatzResearch.WordTrace tailWord_725315 prefixEnd_725315 372435220915934935426843 := by
  unfold tailWord_725315
  simp only [CollatzResearch.WordTrace]
  refine ⟨26454411367315103785001399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17636274244876735856667599 26454411367315103785001399)
  ·
    refine ⟨39681617050972655677502099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26454411367315103785001399 39681617050972655677502099)
    ·
      refine ⟨59522425576458983516253149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39681617050972655677502099 59522425576458983516253149)
      ·
        refine ⟨22320909591172118818594931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59522425576458983516253149 22320909591172118818594931)
        ·
          refine ⟨33481364386758178227892397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22320909591172118818594931 33481364386758178227892397)
          ·
            refine ⟨12555511645034316835459649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33481364386758178227892397 12555511645034316835459649)
            ·
              refine ⟨9416633733775737626594737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12555511645034316835459649 9416633733775737626594737)
              ·
                refine ⟨7062475300331803219946053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9416633733775737626594737 7062475300331803219946053)
                ·
                  refine ⟨1324214118812213103739885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7062475300331803219946053 1324214118812213103739885)
                  ·
                    refine ⟨496580294554579913902457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1324214118812213103739885 496580294554579913902457)
                    ·
                      refine ⟨372435220915934935426843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 496580294554579913902457 372435220915934935426843)
                      ·
                        rfl

theorem cell23_725315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_725315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725315 prefixEnd_725315 := by exact prefixLift 725315
  have htrace : WordTrace (prefixWord ++ tailWord_725315) baseStart_725315 baseEnd_725315 := by
    simpa [prefixWord, tailWord_725315, baseEnd_725315] using wordTrace_append hprefix tailTrace_725315
  have hstable : (prefixWord ++ tailWord_725315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725315).length < 2 ^ (prefixWord ++ tailWord_725315).sum := by decide
  have hdescent : baseEnd_725315 < baseStart_725315 := by decide
  rcases family_descends (prefixWord ++ tailWord_725315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725332 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_725332 : Nat := 118140960795 + 725332 * 2 ^ 59
def prefixEnd_725332 : Nat := 4983230072969 + 3 ^ 40 * 725332 * 2
def baseEnd_725332 : Nat := 372443950087061368914265

theorem tailTrace_725332 : CollatzResearch.WordTrace tailWord_725332 prefixEnd_725332 372443950087061368914265 := by
  unfold tailWord_725332
  simp only [CollatzResearch.WordTrace]
  refine ⟨13227515704126757844185125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17636687605502343792246833 13227515704126757844185125)
  ·
    refine ⟨2480159194523767095784711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13227515704126757844185125 2480159194523767095784711)
    ·
      refine ⟨3720238791785650643677067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2480159194523767095784711 3720238791785650643677067)
      ·
        refine ⟨5580358187678475965515601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720238791785650643677067 5580358187678475965515601)
        ·
          refine ⟨4185268640758856974136701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5580358187678475965515601 4185268640758856974136701)
          ·
            refine ⟨1569475740284571365301263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4185268640758856974136701 1569475740284571365301263)
            ·
              refine ⟨2354213610426857047951895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569475740284571365301263 2354213610426857047951895)
              ·
                refine ⟨3531320415640285571927843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354213610426857047951895 3531320415640285571927843)
                ·
                  refine ⟨5296980623460428357891765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531320415640285571927843 5296980623460428357891765)
                  ·
                    refine ⟨496591933449415158552353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5296980623460428357891765 496591933449415158552353)
                    ·
                      refine ⟨372443950087061368914265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 496591933449415158552353 372443950087061368914265)
                      ·
                        rfl

theorem cell23_725332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_725332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725332 prefixEnd_725332 := by exact prefixLift 725332
  have htrace : WordTrace (prefixWord ++ tailWord_725332) baseStart_725332 baseEnd_725332 := by
    simpa [prefixWord, tailWord_725332, baseEnd_725332] using wordTrace_append hprefix tailTrace_725332
  have hstable : (prefixWord ++ tailWord_725332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725332).length < 2 ^ (prefixWord ++ tailWord_725332).sum := by decide
  have hdescent : baseEnd_725332 < baseStart_725332 := by decide
  rcases family_descends (prefixWord ++ tailWord_725332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725365 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_725365 : Nat := 118140960795 + 725365 * 2 ^ 59
def prefixEnd_725365 : Nat := 4983230072969 + 3 ^ 40 * 725365 * 2
def baseEnd_725365 : Nat := 372460894948659739801613

theorem tailTrace_725365 : CollatzResearch.WordTrace tailWord_725365 prefixEnd_725365 372460894948659739801613 := by
  unfold tailWord_725365
  simp only [CollatzResearch.WordTrace]
  refine ⟨26456235017133962324321549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17637490011422641549547699 26456235017133962324321549)
  ·
    refine ⟨9921088131425235871620581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26456235017133962324321549 9921088131425235871620581)
    ·
      refine ⟨1860204024642231725928859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9921088131425235871620581 1860204024642231725928859)
      ·
        refine ⟨2790306036963347588893289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1860204024642231725928859 2790306036963347588893289)
        ·
          refine ⟨2092729527722510691669967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2790306036963347588893289 2092729527722510691669967)
          ·
            refine ⟨3139094291583766037504951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092729527722510691669967 3139094291583766037504951)
            ·
              refine ⟨4708641437375649056257427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139094291583766037504951 4708641437375649056257427)
              ·
                refine ⟨7062962156063473584386141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4708641437375649056257427 7062962156063473584386141)
                ·
                  refine ⟨2648610808523802594144803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7062962156063473584386141 2648610808523802594144803)
                  ·
                    refine ⟨3972916212785703891217205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2648610808523802594144803 3972916212785703891217205)
                    ·
                      refine ⟨372460894948659739801613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3972916212785703891217205 372460894948659739801613)
                      ·
                        rfl

theorem cell23_725365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_725365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725365 prefixEnd_725365 := by exact prefixLift 725365
  have htrace : WordTrace (prefixWord ++ tailWord_725365) baseStart_725365 baseEnd_725365 := by
    simpa [prefixWord, tailWord_725365, baseEnd_725365] using wordTrace_append hprefix tailTrace_725365
  have hstable : (prefixWord ++ tailWord_725365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725365).length < 2 ^ (prefixWord ++ tailWord_725365).sum := by decide
  have hdescent : baseEnd_725365 < baseStart_725365 := by decide
  rcases family_descends (prefixWord ++ tailWord_725365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725385 : List Nat := [1, 2, 1, 1, 6, 1, 4, 7]
def baseStart_725385 : Nat := 118140960795 + 725385 * 2 ^ 59
def prefixEnd_725385 : Nat := 4983230072969 + 3 ^ 40 * 725385 * 2
def baseEnd_725385 : Nat := 13795228317101839316723

theorem tailTrace_725385 : CollatzResearch.WordTrace tailWord_725385 prefixEnd_725385 13795228317101839316723 := by
  unfold tailWord_725385
  simp only [CollatzResearch.WordTrace]
  refine ⟨26456964477061505740049609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17637976318041003826699739 26456964477061505740049609)
  ·
    refine ⟨19842723357796129305037207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26456964477061505740049609 19842723357796129305037207)
    ·
      refine ⟨29764085036694193957555811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19842723357796129305037207 29764085036694193957555811)
      ·
        refine ⟨44646127555041290936333717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29764085036694193957555811 44646127555041290936333717)
        ·
          refine ⟨2092787229142560512640643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44646127555041290936333717 2092787229142560512640643)
          ·
            refine ⟨3139180843713840768960965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092787229142560512640643 3139180843713840768960965)
            ·
              refine ⟨588596408196345144180181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3139180843713840768960965 588596408196345144180181)
              ·
                refine ⟨13795228317101839316723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 588596408196345144180181 13795228317101839316723)
                ·
                  rfl

theorem cell23_725385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 7].length) (baseStart_725385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725385 prefixEnd_725385 := by exact prefixLift 725385
  have htrace : WordTrace (prefixWord ++ tailWord_725385) baseStart_725385 baseEnd_725385 := by
    simpa [prefixWord, tailWord_725385, baseEnd_725385] using wordTrace_append hprefix tailTrace_725385
  have hstable : (prefixWord ++ tailWord_725385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725385).length < 2 ^ (prefixWord ++ tailWord_725385).sum := by decide
  have hdescent : baseEnd_725385 < baseStart_725385 := by decide
  rcases family_descends (prefixWord ++ tailWord_725385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725412 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_725412 : Nat := 118140960795 + 725412 * 2 ^ 59
def prefixEnd_725412 : Nat := 4983230072969 + 3 ^ 40 * 725412 * 2
def baseEnd_725412 : Nat := 372485028539421055913897

theorem tailTrace_725412 : CollatzResearch.WordTrace tailWord_725412 prefixEnd_725412 372485028539421055913897 := by
  unfold tailWord_725412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13228974623981844675641245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17638632831975792900854993 13228974623981844675641245)
  ·
    refine ⟨4960865483993191753365467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13228974623981844675641245 4960865483993191753365467)
    ·
      refine ⟨7441298225989787630048201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4960865483993191753365467 7441298225989787630048201)
      ·
        refine ⟨5580973669492340722536151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7441298225989787630048201 5580973669492340722536151)
        ·
          refine ⟨8371460504238511083804227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580973669492340722536151 8371460504238511083804227)
          ·
            refine ⟨12557190756357766625706341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8371460504238511083804227 12557190756357766625706341)
            ·
              refine ⟨2354473266817081242319939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12557190756357766625706341 2354473266817081242319939)
              ·
                refine ⟨3531709900225621863479909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354473266817081242319939 3531709900225621863479909)
                ·
                  refine ⟨662195606292304099402483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3531709900225621863479909 662195606292304099402483)
                  ·
                    refine ⟨993293409438456149103725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 662195606292304099402483 993293409438456149103725)
                    ·
                      refine ⟨372485028539421055913897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 993293409438456149103725 372485028539421055913897)
                      ·
                        rfl

theorem cell23_725412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_725412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725412 prefixEnd_725412 := by exact prefixLift 725412
  have htrace : WordTrace (prefixWord ++ tailWord_725412) baseStart_725412 baseEnd_725412 := by
    simpa [prefixWord, tailWord_725412, baseEnd_725412] using wordTrace_append hprefix tailTrace_725412
  have hstable : (prefixWord ++ tailWord_725412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725412).length < 2 ^ (prefixWord ++ tailWord_725412).sum := by decide
  have hdescent : baseEnd_725412 < baseStart_725412 := by decide
  rcases family_descends (prefixWord ++ tailWord_725412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725462 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_725462 : Nat := 118140960795 + 725462 * 2 ^ 59
def prefixEnd_725462 : Nat := 4983230072969 + 3 ^ 40 * 725462 * 2
def baseEnd_725462 : Nat := 124170234190715286762889

theorem tailTrace_725462 : CollatzResearch.WordTrace tailWord_725462 prefixEnd_725462 124170234190715286762889 := by
  unfold tailWord_725462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653735806111409243162665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17639848598521698593735093 1653735806111409243162665)
  ·
    refine ⟨1240301854583556932371999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1653735806111409243162665 1240301854583556932371999)
    ·
      refine ⟨1860452781875335398557999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1240301854583556932371999 1860452781875335398557999)
      ·
        refine ⟨2790679172813003097836999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1860452781875335398557999 2790679172813003097836999)
        ·
          refine ⟨4186018759219504646755499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2790679172813003097836999 4186018759219504646755499)
          ·
            refine ⟨6279028138829256970133249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186018759219504646755499 6279028138829256970133249)
            ·
              refine ⟨4709271104121942727599937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6279028138829256970133249 4709271104121942727599937)
              ·
                refine ⟨3531953328091457045699953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4709271104121942727599937 3531953328091457045699953)
                ·
                  refine ⟨2648964996068592784274965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3531953328091457045699953 2648964996068592784274965)
                  ·
                    refine ⟨124170234190715286762889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2648964996068592784274965 124170234190715286762889)
                    ·
                      rfl

theorem cell23_725462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_725462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725462 prefixEnd_725462 := by exact prefixLift 725462
  have htrace : WordTrace (prefixWord ++ tailWord_725462) baseStart_725462 baseEnd_725462 := by
    simpa [prefixWord, tailWord_725462, baseEnd_725462] using wordTrace_append hprefix tailTrace_725462
  have hstable : (prefixWord ++ tailWord_725462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725462).length < 2 ^ (prefixWord ++ tailWord_725462).sum := by decide
  have hdescent : baseEnd_725462 < baseStart_725462 := by decide
  rcases family_descends (prefixWord ++ tailWord_725462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725465 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_725465 : Nat := 118140960795 + 725465 * 2 ^ 59
def prefixEnd_725465 : Nat := 4983230072969 + 3 ^ 40 * 725465 * 2
def baseEnd_725465 : Nat := 372512243014109348551153

theorem tailTrace_725465 : CollatzResearch.WordTrace tailWord_725465 prefixEnd_725465 372512243014109348551153 := by
  unfold tailWord_725465
  simp only [CollatzResearch.WordTrace]
  refine ⟨26459882316771679402961849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17639921544514452935307899 26459882316771679402961849)
  ·
    refine ⟨19844911737578759552221387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26459882316771679402961849 19844911737578759552221387)
    ·
      refine ⟨29767367606368139328332081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19844911737578759552221387 29767367606368139328332081)
      ·
        refine ⟨22325525704776104496249061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29767367606368139328332081 22325525704776104496249061)
        ·
          refine ⟨4186036069645519593046699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22325525704776104496249061 4186036069645519593046699)
          ·
            refine ⟨6279054104468279389570049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186036069645519593046699 6279054104468279389570049)
            ·
              refine ⟨4709290578351209542177537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6279054104468279389570049 4709290578351209542177537)
              ·
                refine ⟨3531967933763407156633153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4709290578351209542177537 3531967933763407156633153)
                ·
                  refine ⟨2648975950322555367474865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3531967933763407156633153 2648975950322555367474865)
                  ·
                    refine ⟨1986731962741916525606149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2648975950322555367474865 1986731962741916525606149)
                    ·
                      refine ⟨372512243014109348551153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1986731962741916525606149 372512243014109348551153)
                      ·
                        rfl

theorem cell23_725465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_725465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725465 prefixEnd_725465 := by exact prefixLift 725465
  have htrace : WordTrace (prefixWord ++ tailWord_725465) baseStart_725465 baseEnd_725465 := by
    simpa [prefixWord, tailWord_725465, baseEnd_725465] using wordTrace_append hprefix tailTrace_725465
  have hstable : (prefixWord ++ tailWord_725465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725465).length < 2 ^ (prefixWord ++ tailWord_725465).sum := by decide
  have hdescent : baseEnd_725465 < baseStart_725465 := by decide
  rcases family_descends (prefixWord ++ tailWord_725465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725482 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_725482 : Nat := 118140960795 + 725482 * 2 ^ 59
def prefixEnd_725482 : Nat := 4983230072969 + 3 ^ 40 * 725482 * 2
def baseEnd_725482 : Nat := 372520972185235782038575

theorem tailTrace_725482 : CollatzResearch.WordTrace tailWord_725482 prefixEnd_725482 372520972185235782038575 := by
  unfold tailWord_725482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6615125589427522826582675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17640334905140060870887133 6615125589427522826582675)
  ·
    refine ⟨9922688384141284239874013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6615125589427522826582675 9922688384141284239874013)
    ·
      refine ⟨3721008144052981589952755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9922688384141284239874013 3721008144052981589952755)
      ·
        refine ⟨5581512216079472384929133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721008144052981589952755 5581512216079472384929133)
        ·
          refine ⟨2093067081029802144348425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5581512216079472384929133 2093067081029802144348425)
          ·
            refine ⟨1569800310772351608261319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2093067081029802144348425 1569800310772351608261319)
            ·
              refine ⟨2354700466158527412391979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569800310772351608261319 2354700466158527412391979)
              ·
                refine ⟨3532050699237791118587969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354700466158527412391979 3532050699237791118587969)
                ·
                  refine ⟨2649038024428343338940977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532050699237791118587969 2649038024428343338940977)
                  ·
                    refine ⟨1986778518321257504205733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2649038024428343338940977 1986778518321257504205733)
                    ·
                      refine ⟨372520972185235782038575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1986778518321257504205733 372520972185235782038575)
                      ·
                        rfl

theorem cell23_725482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_725482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725482 prefixEnd_725482 := by exact prefixLift 725482
  have htrace : WordTrace (prefixWord ++ tailWord_725482) baseStart_725482 baseEnd_725482 := by
    simpa [prefixWord, tailWord_725482, baseEnd_725482] using wordTrace_append hprefix tailTrace_725482
  have hstable : (prefixWord ++ tailWord_725482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725482).length < 2 ^ (prefixWord ++ tailWord_725482).sum := by decide
  have hdescent : baseEnd_725482 < baseStart_725482 := by decide
  rcases family_descends (prefixWord ++ tailWord_725482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725486 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_725486 : Nat := 118140960795 + 725486 * 2 ^ 59
def prefixEnd_725486 : Nat := 4983230072969 + 3 ^ 40 * 725486 * 2
def baseEnd_725486 : Nat := 372523026107853766388557

theorem tailTrace_725486 : CollatzResearch.WordTrace tailWord_725486 prefixEnd_725486 372523026107853766388557 := by
  unfold tailWord_725486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307581031211949998684539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17640432166463733326317541 3307581031211949998684539)
  ·
    refine ⟨4961371546817924998026809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3307581031211949998684539 4961371546817924998026809)
    ·
      refine ⟨3721028660113443748520107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4961371546817924998026809 3721028660113443748520107)
      ·
        refine ⟨5581542990170165622780161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721028660113443748520107 5581542990170165622780161)
        ·
          refine ⟨4186157242627624217085121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5581542990170165622780161 4186157242627624217085121)
          ·
            refine ⟨3139617931970718162813841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4186157242627624217085121 3139617931970718162813841)
            ·
              refine ⟨2354713448978038622110381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3139617931970718162813841 2354713448978038622110381)
              ·
                refine ⟨883017543366764483291393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2354713448978038622110381 883017543366764483291393)
                ·
                  refine ⟨662263157525073362468545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 883017543366764483291393 662263157525073362468545)
                  ·
                    refine ⟨496697368143805021851409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 662263157525073362468545 496697368143805021851409)
                    ·
                      refine ⟨372523026107853766388557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 496697368143805021851409 372523026107853766388557)
                      ·
                        rfl

theorem cell23_725486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_725486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725486 prefixEnd_725486 := by exact prefixLift 725486
  have htrace : WordTrace (prefixWord ++ tailWord_725486) baseStart_725486 baseEnd_725486 := by
    simpa [prefixWord, tailWord_725486, baseEnd_725486] using wordTrace_append hprefix tailTrace_725486
  have hstable : (prefixWord ++ tailWord_725486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725486).length < 2 ^ (prefixWord ++ tailWord_725486).sum := by decide
  have hdescent : baseEnd_725486 < baseStart_725486 := by decide
  rcases family_descends (prefixWord ++ tailWord_725486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725552 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 3, 4]
def baseStart_725552 : Nat := 118140960795 + 725552 * 2 ^ 59
def prefixEnd_725552 : Nat := 4983230072969 + 3 ^ 40 * 725552 * 2
def baseEnd_725552 : Nat := 124185638610350169387751

theorem tailTrace_725552 : CollatzResearch.WordTrace tailWord_725552 prefixEnd_725552 124185638610350169387751 := by
  unfold tailWord_725552
  simp only [CollatzResearch.WordTrace]
  refine ⟨13231527733728246630689455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17642036978304328840919273 13231527733728246630689455)
  ·
    refine ⟨19847291600592369946034183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13231527733728246630689455 19847291600592369946034183)
    ·
      refine ⟨29770937400888554919051275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19847291600592369946034183 29770937400888554919051275)
      ·
        refine ⟨44656406101332832378576913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29770937400888554919051275 44656406101332832378576913)
        ·
          refine ⟨33492304575999624283932685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44656406101332832378576913 33492304575999624283932685)
          ·
            refine ⟨12559614215999859106474757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33492304575999624283932685 12559614215999859106474757)
            ·
              refine ⟨2354927665499973582464017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12559614215999859106474757 2354927665499973582464017)
              ·
                refine ⟨1766195749124980186848013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2354927665499973582464017 1766195749124980186848013)
                ·
                  refine ⟨662323405921867570068005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1766195749124980186848013 662323405921867570068005)
                  ·
                    refine ⟨124185638610350169387751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 662323405921867570068005 124185638610350169387751)
                    ·
                      rfl

theorem cell23_725552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3, 4].length) (baseStart_725552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725552 prefixEnd_725552 := by exact prefixLift 725552
  have htrace : WordTrace (prefixWord ++ tailWord_725552) baseStart_725552 baseEnd_725552 := by
    simpa [prefixWord, tailWord_725552, baseEnd_725552] using wordTrace_append hprefix tailTrace_725552
  have hstable : (prefixWord ++ tailWord_725552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725552).length < 2 ^ (prefixWord ++ tailWord_725552).sum := by decide
  have hdescent : baseEnd_725552 < baseStart_725552 := by decide
  rcases family_descends (prefixWord ++ tailWord_725552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725555 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 4]
def baseStart_725555 : Nat := 118140960795 + 725555 * 2 ^ 59
def prefixEnd_725555 : Nat := 4983230072969 + 3 ^ 40 * 725555 * 2
def baseEnd_725555 : Nat := 372558456273013996425739

theorem tailTrace_725555 : CollatzResearch.WordTrace tailWord_725555 prefixEnd_725555 372558456273013996425739 := by
  unfold tailWord_725555
  simp only [CollatzResearch.WordTrace]
  refine ⟨26463164886445624773738119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17642109924297083182492079 26463164886445624773738119)
  ·
    refine ⟨39694747329668437160607179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26463164886445624773738119 39694747329668437160607179)
    ·
      refine ⟨59542120994502655740910769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39694747329668437160607179 59542120994502655740910769)
      ·
        refine ⟨44656590745876991805683077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59542120994502655740910769 44656590745876991805683077)
        ·
          refine ⟨8373110764851935963565577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44656590745876991805683077 8373110764851935963565577)
          ·
            refine ⟨6279833073638951972674183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8373110764851935963565577 6279833073638951972674183)
            ·
              refine ⟨9419749610458427959011275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6279833073638951972674183 9419749610458427959011275)
              ·
                refine ⟨14129624415687641938516913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9419749610458427959011275 14129624415687641938516913)
                ·
                  refine ⟨10597218311765731453887685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14129624415687641938516913 10597218311765731453887685)
                  ·
                    refine ⟨1986978433456074647603941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10597218311765731453887685 1986978433456074647603941)
                    ·
                      refine ⟨372558456273013996425739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1986978433456074647603941 372558456273013996425739)
                      ·
                        rfl

theorem cell23_725555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_725555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725555 prefixEnd_725555 := by exact prefixLift 725555
  have htrace : WordTrace (prefixWord ++ tailWord_725555) baseStart_725555 baseEnd_725555 := by
    simpa [prefixWord, tailWord_725555, baseEnd_725555] using wordTrace_append hprefix tailTrace_725555
  have hstable : (prefixWord ++ tailWord_725555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725555).length < 2 ^ (prefixWord ++ tailWord_725555).sum := by decide
  have hdescent : baseEnd_725555 < baseStart_725555 := by decide
  rcases family_descends (prefixWord ++ tailWord_725555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725562 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3]
def baseStart_725562 : Nat := 118140960795 + 725562 * 2 ^ 59
def prefixEnd_725562 : Nat := 4983230072969 + 3 ^ 40 * 725562 * 2
def baseEnd_725562 : Nat := 372562050637595469038207

theorem tailTrace_725562 : CollatzResearch.WordTrace tailWord_725562 prefixEnd_725562 372562050637595469038207 := by
  unfold tailWord_725562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6615855049355066242310735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17642280131613509979495293 6615855049355066242310735)
  ·
    refine ⟨9923782574032599363466103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6615855049355066242310735 9923782574032599363466103)
    ·
      refine ⟨14885673861048899045199155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9923782574032599363466103 14885673861048899045199155)
      ·
        refine ⟨22328510791573348567798733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14885673861048899045199155 22328510791573348567798733)
        ·
          refine ⟨8373191546840005712924525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22328510791573348567798733 8373191546840005712924525)
          ·
            refine ⟨3139946830065002142346697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8373191546840005712924525 3139946830065002142346697)
            ·
              refine ⟨2354960122548751606760023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3139946830065002142346697 2354960122548751606760023)
              ·
                refine ⟨3532440183823127410140035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354960122548751606760023 3532440183823127410140035)
                ·
                  refine ⟨5298660275734691115210053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3532440183823127410140035 5298660275734691115210053)
                  ·
                    refine ⟨993498801700254584101885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5298660275734691115210053 993498801700254584101885)
                    ·
                      refine ⟨372562050637595469038207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 993498801700254584101885 372562050637595469038207)
                      ·
                        rfl

theorem cell23_725562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_725562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725562 prefixEnd_725562 := by exact prefixLift 725562
  have htrace : WordTrace (prefixWord ++ tailWord_725562) baseStart_725562 baseEnd_725562 := by
    simpa [prefixWord, tailWord_725562, baseEnd_725562] using wordTrace_append hprefix tailTrace_725562
  have hstable : (prefixWord ++ tailWord_725562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725562).length < 2 ^ (prefixWord ++ tailWord_725562).sum := by decide
  have hdescent : baseEnd_725562 < baseStart_725562 := by decide
  rcases family_descends (prefixWord ++ tailWord_725562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725636 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_725636 : Nat := 118140960795 + 725636 * 2 ^ 59
def prefixEnd_725636 : Nat := 4983230072969 + 3 ^ 40 * 725636 * 2
def baseEnd_725636 : Nat := 372600048206028179512867

theorem tailTrace_725636 : CollatzResearch.WordTrace tailWord_725636 prefixEnd_725636 372600048206028179512867 := by
  unfold tailWord_725636
  simp only [CollatzResearch.WordTrace]
  refine ⟨13233059599576087803718381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17644079466101450404957841 13233059599576087803718381)
  ·
    refine ⟨4962397349841032926394393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13233059599576087803718381 4962397349841032926394393)
    ·
      refine ⟨3721798012380774694795795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4962397349841032926394393 3721798012380774694795795)
      ·
        refine ⟨5582697018571162042193693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721798012380774694795795 5582697018571162042193693)
        ·
          refine ⟨2093511381964185765822635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5582697018571162042193693 2093511381964185765822635)
          ·
            refine ⟨3140267072946278648733953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093511381964185765822635 3140267072946278648733953)
            ·
              refine ⟨2355200304709708986550465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3140267072946278648733953 2355200304709708986550465)
              ·
                refine ⟨1766400228532281739912849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2355200304709708986550465 1766400228532281739912849)
                ·
                  refine ⟨1324800171399211304934637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1766400228532281739912849 1324800171399211304934637)
                  ·
                    refine ⟨496800064274704239350489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1324800171399211304934637 496800064274704239350489)
                    ·
                      refine ⟨372600048206028179512867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 496800064274704239350489 372600048206028179512867)
                      ·
                        rfl

theorem cell23_725636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_725636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725636 prefixEnd_725636 := by exact prefixLift 725636
  have htrace : WordTrace (prefixWord ++ tailWord_725636) baseStart_725636 baseEnd_725636 := by
    simpa [prefixWord, tailWord_725636, baseEnd_725636] using wordTrace_append hprefix tailTrace_725636
  have hstable : (prefixWord ++ tailWord_725636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725636).length < 2 ^ (prefixWord ++ tailWord_725636).sum := by decide
  have hdescent : baseEnd_725636 < baseStart_725636 := by decide
  rcases family_descends (prefixWord ++ tailWord_725636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725669 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 1, 2, 3]
def baseStart_725669 : Nat := 118140960795 + 725669 * 2 ^ 59
def prefixEnd_725669 : Nat := 4983230072969 + 3 ^ 40 * 725669 * 2
def baseEnd_725669 : Nat := 372616993067626550400215

theorem tailTrace_725669 : CollatzResearch.WordTrace tailWord_725669 prefixEnd_725669 372616993067626550400215 := by
  unfold tailWord_725669
  simp only [CollatzResearch.WordTrace]
  refine ⟨26467322808032622243388061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17644881872021748162258707 26467322808032622243388061)
  ·
    refine ⟨9925246053012233341270523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26467322808032622243388061 9925246053012233341270523)
    ·
      refine ⟨14887869079518350011905785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9925246053012233341270523 14887869079518350011905785)
      ·
        refine ⟨11165901809638762508929339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14887869079518350011905785 11165901809638762508929339)
        ·
          refine ⟨16748852714458143763394009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11165901809638762508929339 16748852714458143763394009)
          ·
            refine ⟨12561639535843607822545507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16748852714458143763394009 12561639535843607822545507)
            ·
              refine ⟨18842459303765411733818261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12561639535843607822545507 18842459303765411733818261)
              ·
                refine ⟨883240279864003675022731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18842459303765411733818261 883240279864003675022731)
                ·
                  refine ⟨1324860419796005512534097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883240279864003675022731 1324860419796005512534097)
                  ·
                    refine ⟨993645314847004134400573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1324860419796005512534097 993645314847004134400573)
                    ·
                      refine ⟨372616993067626550400215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 993645314847004134400573 372616993067626550400215)
                      ·
                        rfl

theorem cell23_725669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_725669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725669 prefixEnd_725669 := by exact prefixLift 725669
  have htrace : WordTrace (prefixWord ++ tailWord_725669) baseStart_725669 baseEnd_725669 := by
    simpa [prefixWord, tailWord_725669, baseEnd_725669] using wordTrace_append hprefix tailTrace_725669
  have hstable : (prefixWord ++ tailWord_725669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725669).length < 2 ^ (prefixWord ++ tailWord_725669).sum := by decide
  have hdescent : baseEnd_725669 < baseStart_725669 := by decide
  rcases family_descends (prefixWord ++ tailWord_725669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725683 : List Nat := [1, 1, 1, 2, 3, 4, 1, 5, 1, 2, 2]
def baseStart_725683 : Nat := 118140960795 + 725683 * 2 ^ 59
def prefixEnd_725683 : Nat := 4983230072969 + 3 ^ 40 * 725683 * 2
def baseEnd_725683 : Nat := 372624181796789495625151

theorem tailTrace_725683 : CollatzResearch.WordTrace tailWord_725683 prefixEnd_725683 372624181796789495625151 := by
  unfold tailWord_725683
  simp only [CollatzResearch.WordTrace]
  refine ⟨26467833429981902634397703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17645222286654601756265135 26467833429981902634397703)
  ·
    refine ⟨39701750144972853951596555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26467833429981902634397703 39701750144972853951596555)
    ·
      refine ⟨59552625217459280927394833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39701750144972853951596555 59552625217459280927394833)
      ·
        refine ⟨44664468913094460695546125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59552625217459280927394833 44664468913094460695546125)
        ·
          refine ⟨16749175842410422760829797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44664468913094460695546125 16749175842410422760829797)
          ·
            refine ⟨3140470470451954267655587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16749175842410422760829797 3140470470451954267655587)
            ·
              refine ⟨4710705705677931401483381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140470470451954267655587 4710705705677931401483381)
              ·
                refine ⟨441628659907306068889067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4710705705677931401483381 441628659907306068889067)
                ·
                  refine ⟨662442989860959103333601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441628659907306068889067 662442989860959103333601)
                  ·
                    refine ⟨496832242395719327500201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 662442989860959103333601 496832242395719327500201)
                    ·
                      refine ⟨372624181796789495625151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 496832242395719327500201 372624181796789495625151)
                      ·
                        rfl

theorem cell23_725683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 1, 2, 2].length) (baseStart_725683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725683 prefixEnd_725683 := by exact prefixLift 725683
  have htrace : WordTrace (prefixWord ++ tailWord_725683) baseStart_725683 baseEnd_725683 := by
    simpa [prefixWord, tailWord_725683, baseEnd_725683] using wordTrace_append hprefix tailTrace_725683
  have hstable : (prefixWord ++ tailWord_725683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725683).length < 2 ^ (prefixWord ++ tailWord_725683).sum := by decide
  have hdescent : baseEnd_725683 < baseStart_725683 := by decide
  rcases family_descends (prefixWord ++ tailWord_725683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725700 : List Nat := [2, 3, 3, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_725700 : Nat := 118140960795 + 725700 * 2 ^ 59
def prefixEnd_725700 : Nat := 4983230072969 + 3 ^ 40 * 725700 * 2
def baseEnd_725700 : Nat := 372632910967915929112573

theorem tailTrace_725700 : CollatzResearch.WordTrace tailWord_725700 prefixEnd_725700 372632910967915929112573 := by
  unfold tailWord_725700
  simp only [CollatzResearch.WordTrace]
  refine ⟨13234226735460157268883277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17645635647280209691844369 13234226735460157268883277)
  ·
    refine ⟨4962835025797558975831229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13234226735460157268883277 4962835025797558975831229)
    ·
      refine ⟨1861063134674084615936711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4962835025797558975831229 1861063134674084615936711)
      ·
        refine ⟨2791594702011126923905067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1861063134674084615936711 2791594702011126923905067)
        ·
          refine ⟨4187392053016690385857601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791594702011126923905067 4187392053016690385857601)
          ·
            refine ⟨3140544039762517789393201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4187392053016690385857601 3140544039762517789393201)
            ·
              refine ⟨2355408029821888342044901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3140544039762517789393201 2355408029821888342044901)
              ·
                refine ⟨441639005591604064133419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2355408029821888342044901 441639005591604064133419)
                ·
                  refine ⟨662458508387406096200129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441639005591604064133419 662458508387406096200129)
                  ·
                    refine ⟨496843881290554572150097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 662458508387406096200129 496843881290554572150097)
                    ·
                      refine ⟨372632910967915929112573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 496843881290554572150097 372632910967915929112573)
                      ·
                        rfl

theorem cell23_725700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_725700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725700 prefixEnd_725700 := by exact prefixLift 725700
  have htrace : WordTrace (prefixWord ++ tailWord_725700) baseStart_725700 baseEnd_725700 := by
    simpa [prefixWord, tailWord_725700, baseEnd_725700] using wordTrace_append hprefix tailTrace_725700
  have hstable : (prefixWord ++ tailWord_725700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725700).length < 2 ^ (prefixWord ++ tailWord_725700).sum := by decide
  have hdescent : baseEnd_725700 < baseStart_725700 := by decide
  rcases family_descends (prefixWord ++ tailWord_725700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725739 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 3, 4, 2]
def baseStart_725739 : Nat := 118140960795 + 725739 * 2 ^ 59
def prefixEnd_725739 : Nat := 4983230072969 + 3 ^ 40 * 725739 * 2
def baseEnd_725739 : Nat := 372652936713441276524893

theorem tailTrace_725739 : CollatzResearch.WordTrace tailWord_725739 prefixEnd_725739 372652936713441276524893 := by
  unfold tailWord_725739
  simp only [CollatzResearch.WordTrace]
  refine ⟨26469875917779024198436271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17646583945186016132290847 26469875917779024198436271)
  ·
    refine ⟨39704813876668536297654407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26469875917779024198436271 39704813876668536297654407)
    ·
      refine ⟨59557220815002804446481611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39704813876668536297654407 59557220815002804446481611)
      ·
        refine ⟨89335831222504206669722417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59557220815002804446481611 89335831222504206669722417)
        ·
          refine ⟨67001873416878155002291813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89335831222504206669722417 67001873416878155002291813)
          ·
            refine ⟨12562851265664654062929715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67001873416878155002291813 12562851265664654062929715)
            ·
              refine ⟨18844276898496981094394573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12562851265664654062929715 18844276898496981094394573)
              ·
                refine ⟨7066603836936367910397965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18844276898496981094394573 7066603836936367910397965)
                ·
                  refine ⟨2649976438851137966399237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7066603836936367910397965 2649976438851137966399237)
                  ·
                    refine ⟨496870582284588368699857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2649976438851137966399237 496870582284588368699857)
                    ·
                      refine ⟨372652936713441276524893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 496870582284588368699857 372652936713441276524893)
                      ·
                        rfl

theorem cell23_725739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 4, 2].length) (baseStart_725739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725739 prefixEnd_725739 := by exact prefixLift 725739
  have htrace : WordTrace (prefixWord ++ tailWord_725739) baseStart_725739 baseEnd_725739 := by
    simpa [prefixWord, tailWord_725739, baseEnd_725739] using wordTrace_append hprefix tailTrace_725739
  have hstable : (prefixWord ++ tailWord_725739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725739).length < 2 ^ (prefixWord ++ tailWord_725739).sum := by decide
  have hdescent : baseEnd_725739 < baseStart_725739 := by decide
  rcases family_descends (prefixWord ++ tailWord_725739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725809 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 2, 5]
def baseStart_725809 : Nat := 118140960795 + 725809 * 2 ^ 59
def prefixEnd_725809 : Nat := 4983230072969 + 3 ^ 40 * 725809 * 2
def baseEnd_725809 : Nat := 124229626786418667549857

theorem tailTrace_725809 : CollatzResearch.WordTrace tailWord_725809 prefixEnd_725809 124229626786418667549857 := by
  unfold tailWord_725809
  simp only [CollatzResearch.WordTrace]
  refine ⟨26472429027525426153484481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17648286018350284102322987 26472429027525426153484481)
  ·
    refine ⟨19854321770644069615113361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26472429027525426153484481 19854321770644069615113361)
    ·
      refine ⟨14890741327983052211335021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19854321770644069615113361 14890741327983052211335021)
      ·
        refine ⟨5584027997993644579250633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14890741327983052211335021 5584027997993644579250633)
        ·
          refine ⟨4188020998495233434437975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5584027997993644579250633 4188020998495233434437975)
          ·
            refine ⟨6282031497742850151656963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4188020998495233434437975 6282031497742850151656963)
            ·
              refine ⟨9423047246614275227485445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6282031497742850151656963 9423047246614275227485445)
              ·
                refine ⟨1766821358740176605153521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9423047246614275227485445 1766821358740176605153521)
                ·
                  refine ⟨1325116019055132453865141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1766821358740176605153521 1325116019055132453865141)
                  ·
                    refine ⟨124229626786418667549857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1325116019055132453865141 124229626786418667549857)
                    ·
                      rfl

theorem cell23_725809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_725809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725809 prefixEnd_725809 := by exact prefixLift 725809
  have htrace : WordTrace (prefixWord ++ tailWord_725809) baseStart_725809 baseEnd_725809 := by
    simpa [prefixWord, tailWord_725809, baseEnd_725809] using wordTrace_append hprefix tailTrace_725809
  have hstable : (prefixWord ++ tailWord_725809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725809).length < 2 ^ (prefixWord ++ tailWord_725809).sum := by decide
  have hdescent : baseEnd_725809 < baseStart_725809 := by decide
  rcases family_descends (prefixWord ++ tailWord_725809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725813 : List Nat := [1, 3, 3, 1, 3, 1, 4, 2, 5]
def baseStart_725813 : Nat := 118140960795 + 725813 * 2 ^ 59
def prefixEnd_725813 : Nat := 4983230072969 + 3 ^ 40 * 725813 * 2
def baseEnd_725813 : Nat := 41410103809097109666617

theorem tailTrace_725813 : CollatzResearch.WordTrace tailWord_725813 prefixEnd_725813 41410103809097109666617 := by
  unfold tailWord_725813
  simp only [CollatzResearch.WordTrace]
  refine ⟨26472574919510934836630093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17648383279673956557753395 26472574919510934836630093)
  ·
    refine ⟨9927215594816600563736285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26472574919510934836630093 9927215594816600563736285)
    ·
      refine ⟨3722705848056225211401107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9927215594816600563736285 3722705848056225211401107)
      ·
        refine ⟨5584058772084337817101661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722705848056225211401107 5584058772084337817101661)
        ·
          refine ⟨2094022039531626681413123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5584058772084337817101661 2094022039531626681413123)
          ·
            refine ⟨3141033059297440022119685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094022039531626681413123 3141033059297440022119685)
            ·
              refine ⟨588943698618270004147441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3141033059297440022119685 588943698618270004147441)
              ·
                refine ⟨441707773963702503110581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588943698618270004147441 441707773963702503110581)
                ·
                  refine ⟨41410103809097109666617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 441707773963702503110581 41410103809097109666617)
                  ·
                    rfl

theorem cell23_725813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_725813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725813 prefixEnd_725813 := by exact prefixLift 725813
  have htrace : WordTrace (prefixWord ++ tailWord_725813) baseStart_725813 baseEnd_725813 := by
    simpa [prefixWord, tailWord_725813, baseEnd_725813] using wordTrace_append hprefix tailTrace_725813
  have hstable : (prefixWord ++ tailWord_725813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725813).length < 2 ^ (prefixWord ++ tailWord_725813).sum := by decide
  have hdescent : baseEnd_725813 < baseStart_725813 := by decide
  rcases family_descends (prefixWord ++ tailWord_725813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725859 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 6]
def baseStart_725859 : Nat := 118140960795 + 725859 * 2 ^ 59
def prefixEnd_725859 : Nat := 4983230072969 + 3 ^ 40 * 725859 * 2
def baseEnd_725859 : Nat := 372714554391980807024341

theorem tailTrace_725859 : CollatzResearch.WordTrace tailWord_725859 prefixEnd_725859 372714554391980807024341 := by
  unfold tailWord_725859
  simp only [CollatzResearch.WordTrace]
  refine ⟨26474252677344284692804631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17649501784896189795203087 26474252677344284692804631)
  ·
    refine ⟨39711379016016427039206947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26474252677344284692804631 39711379016016427039206947)
    ·
      refine ⟨59567068524024640558810421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39711379016016427039206947 59567068524024640558810421)
      ·
        refine ⟨5584412674127310052388477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59567068524024640558810421 5584412674127310052388477)
        ·
          refine ⟨2094154752797741269645679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5584412674127310052388477 2094154752797741269645679)
          ·
            refine ⟨3141232129196611904468519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094154752797741269645679 3141232129196611904468519)
            ·
              refine ⟨4711848193794917856702779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141232129196611904468519 4711848193794917856702779)
              ·
                refine ⟨7067772290692376785054169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711848193794917856702779 7067772290692376785054169)
                ·
                  refine ⟨5300829218019282588790627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7067772290692376785054169 5300829218019282588790627)
                  ·
                    refine ⟨7951243827028923883185941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5300829218019282588790627 7951243827028923883185941)
                    ·
                      refine ⟨372714554391980807024341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7951243827028923883185941 372714554391980807024341)
                      ·
                        rfl

theorem cell23_725859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_725859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725859 prefixEnd_725859 := by exact prefixLift 725859
  have htrace : WordTrace (prefixWord ++ tailWord_725859) baseStart_725859 baseEnd_725859 := by
    simpa [prefixWord, tailWord_725859, baseEnd_725859] using wordTrace_append hprefix tailTrace_725859
  have hstable : (prefixWord ++ tailWord_725859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725859).length < 2 ^ (prefixWord ++ tailWord_725859).sum := by decide
  have hdescent : baseEnd_725859 < baseStart_725859 := by decide
  rcases family_descends (prefixWord ++ tailWord_725859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725873 : List Nat := [1, 2, 2, 2, 1, 4, 2, 4, 1, 4]
def baseStart_725873 : Nat := 118140960795 + 725873 * 2 ^ 59
def prefixEnd_725873 : Nat := 4983230072969 + 3 ^ 40 * 725873 * 2
def baseEnd_725873 : Nat := 124240581040381250749759

theorem tailTrace_725873 : CollatzResearch.WordTrace tailWord_725873 prefixEnd_725873 124240581040381250749759 := by
  unfold tailWord_725873
  simp only [CollatzResearch.WordTrace]
  refine ⟨26474763299293565083814273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17649842199529043389209515 26474763299293565083814273)
  ·
    refine ⟨19856072474470173812860705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26474763299293565083814273 19856072474470173812860705)
    ·
      refine ⟨14892054355852630359645529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19856072474470173812860705 14892054355852630359645529)
      ·
        refine ⟨11169040766889472769734147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14892054355852630359645529 11169040766889472769734147)
        ·
          refine ⟨16753561150334209154601221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169040766889472769734147 16753561150334209154601221)
          ·
            refine ⟨3141292715687664216487729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16753561150334209154601221 3141292715687664216487729)
            ·
              refine ⟨2355969536765748162365797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3141292715687664216487729 2355969536765748162365797)
              ·
                refine ⟨441744288143577780443587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2355969536765748162365797 441744288143577780443587)
                ·
                  refine ⟨662616432215366670665381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441744288143577780443587 662616432215366670665381)
                  ·
                    refine ⟨124240581040381250749759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 662616432215366670665381 124240581040381250749759)
                    ·
                      rfl

theorem cell23_725873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_725873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725873 prefixEnd_725873 := by exact prefixLift 725873
  have htrace : WordTrace (prefixWord ++ tailWord_725873) baseStart_725873 baseEnd_725873 := by
    simpa [prefixWord, tailWord_725873, baseEnd_725873] using wordTrace_append hprefix tailTrace_725873
  have hstable : (prefixWord ++ tailWord_725873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725873).length < 2 ^ (prefixWord ++ tailWord_725873).sum := by decide
  have hdescent : baseEnd_725873 < baseStart_725873 := by decide
  rcases family_descends (prefixWord ++ tailWord_725873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725899 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 3, 5]
def baseStart_725899 : Nat := 118140960795 + 725899 * 2 ^ 59
def prefixEnd_725899 : Nat := 4983230072969 + 3 ^ 40 * 725899 * 2
def baseEnd_725899 : Nat := 124245031206053550174719

theorem tailTrace_725899 : CollatzResearch.WordTrace tailWord_725899 prefixEnd_725899 124245031206053550174719 := by
  unfold tailWord_725899
  simp only [CollatzResearch.WordTrace]
  refine ⟨26475711597199371524260751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17650474398132914349507167 26475711597199371524260751)
  ·
    refine ⟨39713567395799057286391127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26475711597199371524260751 39713567395799057286391127)
    ·
      refine ⟨59570351093698585929586691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39713567395799057286391127 59570351093698585929586691)
      ·
        refine ⟨89355526640547878894380037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59570351093698585929586691 89355526640547878894380037)
        ·
          refine ⟨16754161245102727292696257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89355526640547878894380037 16754161245102727292696257)
          ·
            refine ⟨12565620933827045469522193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16754161245102727292696257 12565620933827045469522193)
            ·
              refine ⟨9424215700370284102141645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12565620933827045469522193 9424215700370284102141645)
              ·
                refine ⟨3534080887638856538303117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9424215700370284102141645 3534080887638856538303117)
                ·
                  refine ⟨1325280332864571201863669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3534080887638856538303117 1325280332864571201863669)
                  ·
                    refine ⟨124245031206053550174719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1325280332864571201863669 124245031206053550174719)
                    ·
                      rfl

theorem cell23_725899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 5].length) (baseStart_725899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725899 prefixEnd_725899 := by exact prefixLift 725899
  have htrace : WordTrace (prefixWord ++ tailWord_725899) baseStart_725899 baseEnd_725899 := by
    simpa [prefixWord, tailWord_725899, baseEnd_725899] using wordTrace_append hprefix tailTrace_725899
  have hstable : (prefixWord ++ tailWord_725899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725899).length < 2 ^ (prefixWord ++ tailWord_725899).sum := by decide
  have hdescent : baseEnd_725899 < baseStart_725899 := by decide
  rcases family_descends (prefixWord ++ tailWord_725899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725939 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 5]
def baseStart_725939 : Nat := 118140960795 + 725939 * 2 ^ 59
def prefixEnd_725939 : Nat := 4983230072969 + 3 ^ 40 * 725939 * 2
def baseEnd_725939 : Nat := 372755632844340494023973

theorem tailTrace_725939 : CollatzResearch.WordTrace tailWord_725939 prefixEnd_725939 372755632844340494023973 := by
  unfold tailWord_725939
  simp only [CollatzResearch.WordTrace]
  refine ⟨26477170517054458355716871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17651447011369638903811247 26477170517054458355716871)
  ·
    refine ⟨39715755775581687533575307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26477170517054458355716871 39715755775581687533575307)
    ·
      refine ⟨59573633663372531300362961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39715755775581687533575307 59573633663372531300362961)
      ·
        refine ⟨44680225247529398475272221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59573633663372531300362961 44680225247529398475272221)
        ·
          refine ⟨16755084467823524428227083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44680225247529398475272221 16755084467823524428227083)
          ·
            refine ⟨25132626701735286642340625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16755084467823524428227083 25132626701735286642340625)
            ·
              refine ⟨18849470026301464981755469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25132626701735286642340625 18849470026301464981755469)
              ·
                refine ⟨7068551259863049368158301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18849470026301464981755469 7068551259863049368158301)
                ·
                  refine ⟨2650706722448643513059363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7068551259863049368158301 2650706722448643513059363)
                  ·
                    refine ⟨3976060083672965269589045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2650706722448643513059363 3976060083672965269589045)
                    ·
                      refine ⟨372755632844340494023973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3976060083672965269589045 372755632844340494023973)
                      ·
                        rfl

theorem cell23_725939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_725939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725939 prefixEnd_725939 := by exact prefixLift 725939
  have htrace : WordTrace (prefixWord ++ tailWord_725939) baseStart_725939 baseEnd_725939 := by
    simpa [prefixWord, tailWord_725939, baseEnd_725939] using wordTrace_append hprefix tailTrace_725939
  have hstable : (prefixWord ++ tailWord_725939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725939).length < 2 ^ (prefixWord ++ tailWord_725939).sum := by decide
  have hdescent : baseEnd_725939 < baseStart_725939 := by decide
  rcases family_descends (prefixWord ++ tailWord_725939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725959 : List Nat := [1, 1, 4, 1, 1, 2, 4, 9]
def baseStart_725959 : Nat := 118140960795 + 725959 * 2 ^ 59
def prefixEnd_725959 : Nat := 4983230072969 + 3 ^ 40 * 725959 * 2
def baseEnd_725959 : Nat := 13806144535460385769403

theorem tailTrace_725959 : CollatzResearch.WordTrace tailWord_725959 prefixEnd_725959 13806144535460385769403 := by
  unfold tailWord_725959
  simp only [CollatzResearch.WordTrace]
  refine ⟨26477899976982001771444931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17651933317988001180963287 26477899976982001771444931)
  ·
    refine ⟨39716849965473002657167397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26477899976982001771444931 39716849965473002657167397)
    ·
      refine ⟨7446909368526187998218887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39716849965473002657167397 7446909368526187998218887)
      ·
        refine ⟨11170364052789281997328331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7446909368526187998218887 11170364052789281997328331)
        ·
          refine ⟨16755546079183922995992497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11170364052789281997328331 16755546079183922995992497)
          ·
            refine ⟨12566659559387942246994373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16755546079183922995992497 12566659559387942246994373)
            ·
              refine ⟨2356248667385239171311445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12566659559387942246994373 2356248667385239171311445)
              ·
                refine ⟨13806144535460385769403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2356248667385239171311445 13806144535460385769403)
                ·
                  rfl

theorem cell23_725959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 9].length) (baseStart_725959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725959 prefixEnd_725959 := by exact prefixLift 725959
  have htrace : WordTrace (prefixWord ++ tailWord_725959) baseStart_725959 baseEnd_725959 := by
    simpa [prefixWord, tailWord_725959, baseEnd_725959] using wordTrace_append hprefix tailTrace_725959
  have hstable : (prefixWord ++ tailWord_725959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725959).length < 2 ^ (prefixWord ++ tailWord_725959).sum := by decide
  have hdescent : baseEnd_725959 < baseStart_725959 := by decide
  rcases family_descends (prefixWord ++ tailWord_725959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725966 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_725966 : Nat := 118140960795 + 725966 * 2 ^ 59
def prefixEnd_725966 : Nat := 4983230072969 + 3 ^ 40 * 725966 * 2
def baseEnd_725966 : Nat := 372769496822011888386349

theorem tailTrace_725966 : CollatzResearch.WordTrace tailWord_725966 prefixEnd_725966 372769496822011888386349 := by
  unfold tailWord_725966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3309769410994580245868719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17652103525304427977966501 3309769410994580245868719)
  ·
    refine ⟨4964654116491870368803079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3309769410994580245868719 4964654116491870368803079)
    ·
      refine ⟨7446981174737805553204619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4964654116491870368803079 7446981174737805553204619)
      ·
        refine ⟨11170471762106708329806929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7446981174737805553204619 11170471762106708329806929)
        ·
          refine ⟨8377853821580031247355197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11170471762106708329806929 8377853821580031247355197)
          ·
            refine ⟨3141695183092511717758199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8377853821580031247355197 3141695183092511717758199)
            ·
              refine ⟨4712542774638767576637299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141695183092511717758199 4712542774638767576637299)
              ·
                refine ⟨7068814161958151364955949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4712542774638767576637299 7068814161958151364955949)
                ·
                  refine ⟨2650805310734306761858481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7068814161958151364955949 2650805310734306761858481)
                  ·
                    refine ⟨1988103983050730071393861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2650805310734306761858481 1988103983050730071393861)
                    ·
                      refine ⟨372769496822011888386349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1988103983050730071393861 372769496822011888386349)
                      ·
                        rfl

theorem cell23_725966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_725966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725966 prefixEnd_725966 := by exact prefixLift 725966
  have htrace : WordTrace (prefixWord ++ tailWord_725966) baseStart_725966 baseEnd_725966 := by
    simpa [prefixWord, tailWord_725966, baseEnd_725966] using wordTrace_append hprefix tailTrace_725966
  have hstable : (prefixWord ++ tailWord_725966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725966).length < 2 ^ (prefixWord ++ tailWord_725966).sum := by decide
  have hdescent : baseEnd_725966 < baseStart_725966 := by decide
  rcases family_descends (prefixWord ++ tailWord_725966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725987 : List Nat := [1, 1, 1, 6, 1, 1, 3, 4, 1, 2, 2]
def baseStart_725987 : Nat := 118140960795 + 725987 * 2 ^ 59
def prefixEnd_725987 : Nat := 4983230072969 + 3 ^ 40 * 725987 * 2
def baseEnd_725987 : Nat := 372780279915756306223753

theorem tailTrace_725987 : CollatzResearch.WordTrace tailWord_725987 prefixEnd_725987 372780279915756306223753 := by
  unfold tailWord_725987
  simp only [CollatzResearch.WordTrace]
  refine ⟨26478921220880562553464215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17652614147253708368976143 26478921220880562553464215)
  ·
    refine ⟨39718381831320843830196323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26478921220880562553464215 39718381831320843830196323)
    ·
      refine ⟨59577572746981265745294485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39718381831320843830196323 59577572746981265745294485)
      ·
        refine ⟨2792698722514746831810679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59577572746981265745294485 2792698722514746831810679)
        ·
          refine ⟨4189048083772120247716019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2792698722514746831810679 4189048083772120247716019)
          ·
            refine ⟨6283572125658180371574029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189048083772120247716019 6283572125658180371574029)
            ·
              refine ⟨2356339547121817639340261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6283572125658180371574029 2356339547121817639340261)
              ·
                refine ⟨441813665085340807376299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2356339547121817639340261 441813665085340807376299)
                ·
                  refine ⟨662720497628011211064449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441813665085340807376299 662720497628011211064449)
                  ·
                    refine ⟨497040373221008408298337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 662720497628011211064449 497040373221008408298337)
                    ·
                      refine ⟨372780279915756306223753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497040373221008408298337 372780279915756306223753)
                      ·
                        rfl

theorem cell23_725987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_725987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_725987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_725987 prefixEnd_725987 := by exact prefixLift 725987
  have htrace : WordTrace (prefixWord ++ tailWord_725987) baseStart_725987 baseEnd_725987 := by
    simpa [prefixWord, tailWord_725987, baseEnd_725987] using wordTrace_append hprefix tailTrace_725987
  have hstable : (prefixWord ++ tailWord_725987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725987).length < 2 ^ (prefixWord ++ tailWord_725987).sum := by decide
  have hdescent : baseEnd_725987 < baseStart_725987 := by decide
  rcases family_descends (prefixWord ++ tailWord_725987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726037 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_726037 : Nat := 118140960795 + 726037 * 2 ^ 59
def prefixEnd_726037 : Nat := 4983230072969 + 3 ^ 40 * 726037 * 2
def baseEnd_726037 : Nat := 372805953948481110598523

theorem tailTrace_726037 : CollatzResearch.WordTrace tailWord_726037 prefixEnd_726037 372805953948481110598523 := by
  unfold tailWord_726037
  simp only [CollatzResearch.WordTrace]
  refine ⟨26480744870699421092784365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17653829913799614061856243 26480744870699421092784365)
  ·
    refine ⟨9930279326512282909794137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26480744870699421092784365 9930279326512282909794137)
    ·
      refine ⟨7447709494884212182345603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9930279326512282909794137 7447709494884212182345603)
      ·
        refine ⟨11171564242326318273518405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7447709494884212182345603 11171564242326318273518405)
        ·
          refine ⟨2094668295436184676284701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11171564242326318273518405 2094668295436184676284701)
          ·
            refine ⟨785500610788569253606763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2094668295436184676284701 785500610788569253606763)
            ·
              refine ⟨1178250916182853880410145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785500610788569253606763 1178250916182853880410145)
              ·
                refine ⟨883688187137140410307609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178250916182853880410145 883688187137140410307609)
                ·
                  refine ⟨662766140352855307730707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 883688187137140410307609 662766140352855307730707)
                  ·
                    refine ⟨994149210529282961596061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 662766140352855307730707 994149210529282961596061)
                    ·
                      refine ⟨372805953948481110598523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 994149210529282961596061 372805953948481110598523)
                      ·
                        rfl

theorem cell23_726037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_726037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726037 prefixEnd_726037 := by exact prefixLift 726037
  have htrace : WordTrace (prefixWord ++ tailWord_726037) baseStart_726037 baseEnd_726037 := by
    simpa [prefixWord, tailWord_726037, baseEnd_726037] using wordTrace_append hprefix tailTrace_726037
  have hstable : (prefixWord ++ tailWord_726037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726037).length < 2 ^ (prefixWord ++ tailWord_726037).sum := by decide
  have hdescent : baseEnd_726037 < baseStart_726037 := by decide
  rcases family_descends (prefixWord ++ tailWord_726037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726066 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 7]
def baseStart_726066 : Nat := 118140960795 + 726066 * 2 ^ 59
def prefixEnd_726066 : Nat := 4983230072969 + 3 ^ 40 * 726066 * 2
def baseEnd_726066 : Nat := 41424538320829055237321

theorem tailTrace_726066 : CollatzResearch.WordTrace tailWord_726066 prefixEnd_726066 41424538320829055237321 := by
  unfold tailWord_726066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6620450646898589761397513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17654535058396239363726701 6620450646898589761397513)
  ·
    refine ⟨4965337985173942321048135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6620450646898589761397513 4965337985173942321048135)
    ·
      refine ⟨7448006977760913481572203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4965337985173942321048135 7448006977760913481572203)
      ·
        refine ⟨11172010466641370222358305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7448006977760913481572203 11172010466641370222358305)
        ·
          refine ⟨8379007849981027666768729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11172010466641370222358305 8379007849981027666768729)
          ·
            refine ⟨6284255887485770750076547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8379007849981027666768729 6284255887485770750076547)
            ·
              refine ⟨9426383831228656125114821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6284255887485770750076547 9426383831228656125114821)
              ·
                refine ⟨1767446968355373023459029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9426383831228656125114821 1767446968355373023459029)
                ·
                  refine ⟨41424538320829055237321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1767446968355373023459029 41424538320829055237321)
                  ·
                    rfl

theorem cell23_726066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_726066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726066 prefixEnd_726066 := by exact prefixLift 726066
  have htrace : WordTrace (prefixWord ++ tailWord_726066) baseStart_726066 baseEnd_726066 := by
    simpa [prefixWord, tailWord_726066, baseEnd_726066] using wordTrace_append hprefix tailTrace_726066
  have hstable : (prefixWord ++ tailWord_726066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726066).length < 2 ^ (prefixWord ++ tailWord_726066).sum := by decide
  have hdescent : baseEnd_726066 < baseStart_726066 := by decide
  rcases family_descends (prefixWord ++ tailWord_726066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726103 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 2, 5, 2]
def baseStart_726103 : Nat := 118140960795 + 726103 * 2 ^ 59
def prefixEnd_726103 : Nat := 4983230072969 + 3 ^ 40 * 726103 * 2
def baseEnd_726103 : Nat := 372839843671677852373219

theorem tailTrace_726103 : CollatzResearch.WordTrace tailWord_726103 prefixEnd_726103 372839843671677852373219 := by
  unfold tailWord_726103
  simp only [CollatzResearch.WordTrace]
  refine ⟨26483152088460314364686963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17655434725640209576457975 26483152088460314364686963)
  ·
    refine ⟨39724728132690471547030445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26483152088460314364686963 39724728132690471547030445)
    ·
      refine ⟨14896773049758926830136417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39724728132690471547030445 14896773049758926830136417)
      ·
        refine ⟨11172579787319195122602313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14896773049758926830136417 11172579787319195122602313)
        ·
          refine ⟨8379434840489396341951735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11172579787319195122602313 8379434840489396341951735)
          ·
            refine ⟨12569152260734094512927603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8379434840489396341951735 12569152260734094512927603)
            ·
              refine ⟨18853728391101141769391405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12569152260734094512927603 18853728391101141769391405)
              ·
                refine ⟨7070148146662928163521777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18853728391101141769391405 7070148146662928163521777)
                ·
                  refine ⟨5302611109997196122641333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7070148146662928163521777 5302611109997196122641333)
                  ·
                    refine ⟨497119791562237136497625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5302611109997196122641333 497119791562237136497625)
                    ·
                      refine ⟨372839843671677852373219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497119791562237136497625 372839843671677852373219)
                      ·
                        rfl

theorem cell23_726103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_726103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726103 prefixEnd_726103 := by exact prefixLift 726103
  have htrace : WordTrace (prefixWord ++ tailWord_726103) baseStart_726103 baseEnd_726103 := by
    simpa [prefixWord, tailWord_726103, baseEnd_726103] using wordTrace_append hprefix tailTrace_726103
  have hstable : (prefixWord ++ tailWord_726103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726103).length < 2 ^ (prefixWord ++ tailWord_726103).sum := by decide
  have hdescent : baseEnd_726103 < baseStart_726103 := by decide
  rcases family_descends (prefixWord ++ tailWord_726103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726156 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 8]
def baseStart_726156 : Nat := 118140960795 + 726156 * 2 ^ 59
def prefixEnd_726156 : Nat := 4983230072969 + 3 ^ 40 * 726156 * 2
def baseEnd_726156 : Nat := 41429673127374016112275

theorem tailTrace_726156 : CollatzResearch.WordTrace tailWord_726156 prefixEnd_726156 41429673127374016112275 := by
  unfold tailWord_726156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13242542578634152208183161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17656723438178869610910881 13242542578634152208183161)
  ·
    refine ⟨9931906933975614156137371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13242542578634152208183161 9931906933975614156137371)
    ·
      refine ⟨14897860400963421234206057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9931906933975614156137371 14897860400963421234206057)
      ·
        refine ⟨11173395300722565925654543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14897860400963421234206057 11173395300722565925654543)
        ·
          refine ⟨16760092951083848888481815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11173395300722565925654543 16760092951083848888481815)
          ·
            refine ⟨25140139426625773332722723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16760092951083848888481815 25140139426625773332722723)
            ·
              refine ⟨37710209139938659999084085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25140139426625773332722723 37710209139938659999084085)
              ·
                refine ⟨3535332106869249374914133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37710209139938659999084085 3535332106869249374914133)
                ·
                  refine ⟨41429673127374016112275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3535332106869249374914133 41429673127374016112275)
                  ·
                    rfl

theorem cell23_726156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_726156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726156 prefixEnd_726156 := by exact prefixLift 726156
  have htrace : WordTrace (prefixWord ++ tailWord_726156) baseStart_726156 baseEnd_726156 := by
    simpa [prefixWord, tailWord_726156, baseEnd_726156] using wordTrace_append hprefix tailTrace_726156
  have hstable : (prefixWord ++ tailWord_726156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726156).length < 2 ^ (prefixWord ++ tailWord_726156).sum := by decide
  have hdescent : baseEnd_726156 < baseStart_726156 := by decide
  rcases family_descends (prefixWord ++ tailWord_726156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726173 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 6]
def baseStart_726173 : Nat := 118140960795 + 726173 * 2 ^ 59
def prefixEnd_726173 : Nat := 4983230072969 + 3 ^ 40 * 726173 * 2
def baseEnd_726173 : Nat := 41430643035276953166433

theorem tailTrace_726173 : CollatzResearch.WordTrace tailWord_726173 prefixEnd_726173 41430643035276953166433 := by
  unfold tailWord_726173
  simp only [CollatzResearch.WordTrace]
  refine ⟨26485705198206716319735173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17657136798804477546490115 26485705198206716319735173)
  ·
    refine ⟨4966069724663759309950345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26485705198206716319735173 4966069724663759309950345)
    ·
      refine ⟨3724552293497819482462759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4966069724663759309950345 3724552293497819482462759)
      ·
        refine ⟨5586828440246729223694139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3724552293497819482462759 5586828440246729223694139)
        ·
          refine ⟨8380242660370093835541209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5586828440246729223694139 8380242660370093835541209)
          ·
            refine ⟨6285181995277570376655907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8380242660370093835541209 6285181995277570376655907)
            ·
              refine ⟨9427772992916355564983861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6285181995277570376655907 9427772992916355564983861)
              ·
                refine ⟨883853718085908334217237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9427772992916355564983861 883853718085908334217237)
                ·
                  refine ⟨41430643035276953166433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 883853718085908334217237 41430643035276953166433)
                  ·
                    rfl

theorem cell23_726173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_726173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726173 prefixEnd_726173 := by exact prefixLift 726173
  have htrace : WordTrace (prefixWord ++ tailWord_726173) baseStart_726173 baseEnd_726173 := by
    simpa [prefixWord, tailWord_726173, baseEnd_726173] using wordTrace_append hprefix tailTrace_726173
  have hstable : (prefixWord ++ tailWord_726173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726173).length < 2 ^ (prefixWord ++ tailWord_726173).sum := by decide
  have hdescent : baseEnd_726173 < baseStart_726173 := by decide
  rcases family_descends (prefixWord ++ tailWord_726173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726223 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 4]
def baseStart_726223 : Nat := 118140960795 + 726223 * 2 ^ 59
def prefixEnd_726223 : Nat := 4983230072969 + 3 ^ 40 * 726223 * 2
def baseEnd_726223 : Nat := 372901461350217382872667

theorem tailTrace_726223 : CollatzResearch.WordTrace tailWord_726223 prefixEnd_726223 372901461350217382872667 := by
  unfold tailWord_726223
  simp only [CollatzResearch.WordTrace]
  refine ⟨26487528848025574859055323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17658352565350383239370215 26487528848025574859055323)
  ·
    refine ⟨39731293272038362288582985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26487528848025574859055323 39731293272038362288582985)
    ·
      refine ⟨29798469954028771716437239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39731293272038362288582985 29798469954028771716437239)
      ·
        refine ⟨44697704931043157574655859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29798469954028771716437239 44697704931043157574655859)
        ·
          refine ⟨67046557396564736361983789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44697704931043157574655859 67046557396564736361983789)
          ·
            refine ⟨25142459023711776135743921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67046557396564736361983789 25142459023711776135743921)
            ·
              refine ⟨18856844267783832101807941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25142459023711776135743921 18856844267783832101807941)
              ·
                refine ⟨3535658300209468519088989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18856844267783832101807941 3535658300209468519088989)
                ·
                  refine ⟨1325871862578550694658371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3535658300209468519088989 1325871862578550694658371)
                  ·
                    refine ⟨1988807793867826041987557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1325871862578550694658371 1988807793867826041987557)
                    ·
                      refine ⟨372901461350217382872667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1988807793867826041987557 372901461350217382872667)
                      ·
                        rfl

theorem cell23_726223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_726223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726223 prefixEnd_726223 := by exact prefixLift 726223
  have htrace : WordTrace (prefixWord ++ tailWord_726223) baseStart_726223 baseEnd_726223 := by
    simpa [prefixWord, tailWord_726223, baseEnd_726223] using wordTrace_append hprefix tailTrace_726223
  have hstable : (prefixWord ++ tailWord_726223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726223).length < 2 ^ (prefixWord ++ tailWord_726223).sum := by decide
  have hdescent : baseEnd_726223 < baseStart_726223 := by decide
  rcases family_descends (prefixWord ++ tailWord_726223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726240 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 4]
def baseStart_726240 : Nat := 118140960795 + 726240 * 2 ^ 59
def prefixEnd_726240 : Nat := 4983230072969 + 3 ^ 40 * 726240 * 2
def baseEnd_726240 : Nat := 372910190521343816360089

theorem tailTrace_726240 : CollatzResearch.WordTrace tailWord_726240 prefixEnd_726240 372910190521343816360089 := by
  unfold tailWord_726240
  simp only [CollatzResearch.WordTrace]
  refine ⟨13244074444481993381212087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17658765925975991174949449 13244074444481993381212087)
  ·
    refine ⟨19866111666722990071818131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13244074444481993381212087 19866111666722990071818131)
    ·
      refine ⟨29799167500084485107727197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19866111666722990071818131 29799167500084485107727197)
      ·
        refine ⟨11174687812531681915397699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29799167500084485107727197 11174687812531681915397699)
        ·
          refine ⟨16762031718797522873096549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11174687812531681915397699 16762031718797522873096549)
          ·
            refine ⟨3142880947274535538705603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16762031718797522873096549 3142880947274535538705603)
            ·
              refine ⟨4714321420911803308058405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3142880947274535538705603 4714321420911803308058405)
              ·
                refine ⟨883935266420963120260951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4714321420911803308058405 883935266420963120260951)
                ·
                  refine ⟨1325902899631444680391427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883935266420963120260951 1325902899631444680391427)
                  ·
                    refine ⟨1988854349447167020587141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1325902899631444680391427 1988854349447167020587141)
                    ·
                      refine ⟨372910190521343816360089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1988854349447167020587141 372910190521343816360089)
                      ·
                        rfl

theorem cell23_726240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_726240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726240 prefixEnd_726240 := by exact prefixLift 726240
  have htrace : WordTrace (prefixWord ++ tailWord_726240) baseStart_726240 baseEnd_726240 := by
    simpa [prefixWord, tailWord_726240, baseEnd_726240] using wordTrace_append hprefix tailTrace_726240
  have hstable : (prefixWord ++ tailWord_726240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726240).length < 2 ^ (prefixWord ++ tailWord_726240).sum := by decide
  have hdescent : baseEnd_726240 < baseStart_726240 := by decide
  rcases family_descends (prefixWord ++ tailWord_726240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726250 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_726250 : Nat := 118140960795 + 726250 * 2 ^ 59
def prefixEnd_726250 : Nat := 4983230072969 + 3 ^ 40 * 726250 * 2
def baseEnd_726250 : Nat := 124305108442629592411681

theorem tailTrace_726250 : CollatzResearch.WordTrace tailWord_726250 prefixEnd_726250 124305108442629592411681 := by
  unfold tailWord_726250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6622128404731939617572051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17659009079285172313525469 6622128404731939617572051)
  ·
    refine ⟨9933192607097909426358077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6622128404731939617572051 9933192607097909426358077)
    ·
      refine ⟨3724947227661716034884279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9933192607097909426358077 3724947227661716034884279)
      ·
        refine ⟨5587420841492574052326419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3724947227661716034884279 5587420841492574052326419)
        ·
          refine ⟨8381131262238861078489629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5587420841492574052326419 8381131262238861078489629)
          ·
            refine ⟨3142924223339572904433611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8381131262238861078489629 3142924223339572904433611)
            ·
              refine ⟨4714386335009359356650417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3142924223339572904433611 4714386335009359356650417)
              ·
                refine ⟨3535789751257019517487813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714386335009359356650417 3535789751257019517487813)
                ·
                  refine ⟨662960578360691159528965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3535789751257019517487813 662960578360691159528965)
                  ·
                    refine ⟨124305108442629592411681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 662960578360691159528965 124305108442629592411681)
                    ·
                      rfl

theorem cell23_726250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_726250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726250 prefixEnd_726250 := by exact prefixLift 726250
  have htrace : WordTrace (prefixWord ++ tailWord_726250) baseStart_726250 baseEnd_726250 := by
    simpa [prefixWord, tailWord_726250, baseEnd_726250] using wordTrace_append hprefix tailTrace_726250
  have hstable : (prefixWord ++ tailWord_726250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726250).length < 2 ^ (prefixWord ++ tailWord_726250).sum := by decide
  have hdescent : baseEnd_726250 < baseStart_726250 := by decide
  rcases family_descends (prefixWord ++ tailWord_726250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726270 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_726270 : Nat := 118140960795 + 726270 * 2 ^ 59
def prefixEnd_726270 : Nat := 4983230072969 + 3 ^ 40 * 726270 * 2
def baseEnd_726270 : Nat := 372925594940978698984951

theorem tailTrace_726270 : CollatzResearch.WordTrace tailWord_726270 prefixEnd_726270 372925594940978698984951 := by
  unfold tailWord_726270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311155384856912735752033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17659495385903534590677509 3311155384856912735752033)
  ·
    refine ⟨2483366538642684551814025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3311155384856912735752033 2483366538642684551814025)
    ·
      refine ⟨1862524903982013413860519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2483366538642684551814025 1862524903982013413860519)
      ·
        refine ⟨2793787355973020120790779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1862524903982013413860519 2793787355973020120790779)
        ·
          refine ⟨4190681033959530181186169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2793787355973020120790779 4190681033959530181186169)
          ·
            refine ⟨3143010775469647635889627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4190681033959530181186169 3143010775469647635889627)
            ·
              refine ⟨4714516163204471453834441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143010775469647635889627 4714516163204471453834441)
              ·
                refine ⟨3535887122403353590375831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714516163204471453834441 3535887122403353590375831)
                ·
                  refine ⟨5303830683605030385563747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535887122403353590375831 5303830683605030385563747)
                  ·
                    refine ⟨7955746025407545578345621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5303830683605030385563747 7955746025407545578345621)
                    ·
                      refine ⟨372925594940978698984951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7955746025407545578345621 372925594940978698984951)
                      ·
                        rfl

theorem cell23_726270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_726270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726270 prefixEnd_726270 := by exact prefixLift 726270
  have htrace : WordTrace (prefixWord ++ tailWord_726270) baseStart_726270 baseEnd_726270 := by
    simpa [prefixWord, tailWord_726270, baseEnd_726270] using wordTrace_append hprefix tailTrace_726270
  have hstable : (prefixWord ++ tailWord_726270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726270).length < 2 ^ (prefixWord ++ tailWord_726270).sum := by decide
  have hdescent : baseEnd_726270 < baseStart_726270 := by decide
  rcases family_descends (prefixWord ++ tailWord_726270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726280 : List Nat := [2, 1, 3, 2, 4, 1, 2, 8]
def baseStart_726280 : Nat := 118140960795 + 726280 * 2 ^ 59
def prefixEnd_726280 : Nat := 4983230072969 + 3 ^ 40 * 726280 * 2
def baseEnd_726280 : Nat := 13812249249908283698515

theorem tailTrace_726280 : CollatzResearch.WordTrace tailWord_726280 prefixEnd_726280 13812249249908283698515 := by
  unfold tailWord_726280
  simp only [CollatzResearch.WordTrace]
  refine ⟨13244803904409536796940147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17659738539212715729253529 13244803904409536796940147)
  ·
    refine ⟨19867205856614305195410221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13244803904409536796940147 19867205856614305195410221)
    ·
      refine ⟨7450202196230364448278833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19867205856614305195410221 7450202196230364448278833)
      ·
        refine ⟨5587651647172773336209125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7450202196230364448278833 5587651647172773336209125)
        ·
          refine ⟨1047684683844895000539211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5587651647172773336209125 1047684683844895000539211)
          ·
            refine ⟨1571527025767342500808817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047684683844895000539211 1571527025767342500808817)
            ·
              refine ⟨1178645269325506875606613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1571527025767342500808817 1178645269325506875606613)
              ·
                refine ⟨13812249249908283698515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1178645269325506875606613 13812249249908283698515)
                ·
                  rfl

theorem cell23_726280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 8].length) (baseStart_726280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726280 prefixEnd_726280 := by exact prefixLift 726280
  have htrace : WordTrace (prefixWord ++ tailWord_726280) baseStart_726280 baseEnd_726280 := by
    simpa [prefixWord, tailWord_726280, baseEnd_726280] using wordTrace_append hprefix tailTrace_726280
  have hstable : (prefixWord ++ tailWord_726280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726280).length < 2 ^ (prefixWord ++ tailWord_726280).sum := by decide
  have hdescent : baseEnd_726280 < baseStart_726280 := by decide
  rcases family_descends (prefixWord ++ tailWord_726280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726284 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 2, 4]
def baseStart_726284 : Nat := 118140960795 + 726284 * 2 ^ 59
def prefixEnd_726284 : Nat := 4983230072969 + 3 ^ 40 * 726284 * 2
def baseEnd_726284 : Nat := 124310927890047214736629

theorem tailTrace_726284 : CollatzResearch.WordTrace tailWord_726284 prefixEnd_726284 124310927890047214736629 := by
  unfold tailWord_726284
  simp only [CollatzResearch.WordTrace]
  refine ⟨13244876850402291138512953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17659835800536388184683937 13244876850402291138512953)
  ·
    refine ⟨9933657637801718353884715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13244876850402291138512953 9933657637801718353884715)
    ·
      refine ⟨14900486456702577530827073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9933657637801718353884715 14900486456702577530827073)
      ·
        refine ⟨11175364842526933148120305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14900486456702577530827073 11175364842526933148120305)
        ·
          refine ⟨8381523631895199861090229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11175364842526933148120305 8381523631895199861090229)
          ·
            refine ⟨785767840490174986977209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8381523631895199861090229 785767840490174986977209)
            ·
              refine ⟨589325880367631240232907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785767840490174986977209 589325880367631240232907)
              ·
                refine ⟨883988820551446860349361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589325880367631240232907 883988820551446860349361)
                ·
                  refine ⟨662991615413585145262021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 883988820551446860349361 662991615413585145262021)
                  ·
                    refine ⟨124310927890047214736629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 662991615413585145262021 124310927890047214736629)
                    ·
                      rfl

theorem cell23_726284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_726284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726284 prefixEnd_726284 := by exact prefixLift 726284
  have htrace : WordTrace (prefixWord ++ tailWord_726284) baseStart_726284 baseEnd_726284 := by
    simpa [prefixWord, tailWord_726284, baseEnd_726284] using wordTrace_append hprefix tailTrace_726284
  have hstable : (prefixWord ++ tailWord_726284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726284).length < 2 ^ (prefixWord ++ tailWord_726284).sum := by decide
  have hdescent : baseEnd_726284 < baseStart_726284 := by decide
  rcases family_descends (prefixWord ++ tailWord_726284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726350 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_726350 : Nat := 118140960795 + 726350 * 2 ^ 59
def prefixEnd_726350 : Nat := 4983230072969 + 3 ^ 40 * 726350 * 2
def baseEnd_726350 : Nat := 372966673393338385984583

theorem tailTrace_726350 : CollatzResearch.WordTrace tailWord_726350 prefixEnd_726350 372966673393338385984583 := by
  unfold tailWord_726350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311520114820684443616063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17661440612376983699285669 3311520114820684443616063)
  ·
    refine ⟨4967280172231026665424095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3311520114820684443616063 4967280172231026665424095)
    ·
      refine ⟨7450920258346539998136143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4967280172231026665424095 7450920258346539998136143)
      ·
        refine ⟨11176380387519809997204215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7450920258346539998136143 11176380387519809997204215)
        ·
          refine ⟨16764570581279714995806323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11176380387519809997204215 16764570581279714995806323)
          ·
            refine ⟨25146855871919572493709485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16764570581279714995806323 25146855871919572493709485)
            ·
              refine ⟨9430070951969839685141057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25146855871919572493709485 9430070951969839685141057)
              ·
                refine ⟨7072553213977379763855793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9430070951969839685141057 7072553213977379763855793)
                ·
                  refine ⟨5304414910483034822891845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7072553213977379763855793 5304414910483034822891845)
                  ·
                    refine ⟨994577795715569029292221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5304414910483034822891845 994577795715569029292221)
                    ·
                      refine ⟨372966673393338385984583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 994577795715569029292221 372966673393338385984583)
                      ·
                        rfl

theorem cell23_726350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_726350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726350 prefixEnd_726350 := by exact prefixLift 726350
  have htrace : WordTrace (prefixWord ++ tailWord_726350) baseStart_726350 baseEnd_726350 := by
    simpa [prefixWord, tailWord_726350, baseEnd_726350] using wordTrace_append hprefix tailTrace_726350
  have hstable : (prefixWord ++ tailWord_726350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726350).length < 2 ^ (prefixWord ++ tailWord_726350).sum := by decide
  have hdescent : baseEnd_726350 < baseStart_726350 := by decide
  rcases family_descends (prefixWord ++ tailWord_726350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726370 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 9]
def baseStart_726370 : Nat := 118140960795 + 726370 * 2 ^ 59
def prefixEnd_726370 : Nat := 4983230072969 + 3 ^ 40 * 726370 * 2
def baseEnd_726370 : Nat := 41441882556269811970499

theorem tailTrace_726370 : CollatzResearch.WordTrace tailWord_726370 prefixEnd_726370 41441882556269811970499 := by
  unfold tailWord_726370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623222594623254741164141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17661926918995345976437709 6623222594623254741164141)
  ·
    refine ⟨2483708472983720527936553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6623222594623254741164141 2483708472983720527936553)
    ·
      refine ⟨1862781354737790395952415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2483708472983720527936553 1862781354737790395952415)
      ·
        refine ⟨2794172032106685593928623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1862781354737790395952415 2794172032106685593928623)
        ·
          refine ⟨4191258048160028390892935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794172032106685593928623 4191258048160028390892935)
          ·
            refine ⟨6286887072240042586339403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4191258048160028390892935 6286887072240042586339403)
            ·
              refine ⟨9430330608360063879509105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6286887072240042586339403 9430330608360063879509105)
              ·
                refine ⟨7072747956270047909631829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9430330608360063879509105 7072747956270047909631829)
                ·
                  refine ⟨41441882556269811970499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7072747956270047909631829 41441882556269811970499)
                  ·
                    rfl

theorem cell23_726370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_726370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726370 prefixEnd_726370 := by exact prefixLift 726370
  have htrace : WordTrace (prefixWord ++ tailWord_726370) baseStart_726370 baseEnd_726370 := by
    simpa [prefixWord, tailWord_726370, baseEnd_726370] using wordTrace_append hprefix tailTrace_726370
  have hstable : (prefixWord ++ tailWord_726370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726370).length < 2 ^ (prefixWord ++ tailWord_726370).sum := by decide
  have hdescent : baseEnd_726370 < baseStart_726370 := by decide
  rcases family_descends (prefixWord ++ tailWord_726370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726381 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_726381 : Nat := 118140960795 + 726381 * 2 ^ 59
def prefixEnd_726381 : Nat := 4983230072969 + 3 ^ 40 * 726381 * 2
def baseEnd_726381 : Nat := 372982591293627764696941

theorem tailTrace_726381 : CollatzResearch.WordTrace tailWord_726381 prefixEnd_726381 372982591293627764696941 := by
  unfold tailWord_726381
  simp only [CollatzResearch.WordTrace]
  refine ⟨26493291581453167843306997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17662194387635445228871331 26493291581453167843306997)
  ·
    refine ⟨2483746085761234485310031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26493291581453167843306997 2483746085761234485310031)
    ·
      refine ⟨3725619128641851727965047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483746085761234485310031 3725619128641851727965047)
      ·
        refine ⟨5588428692962777591947571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725619128641851727965047 5588428692962777591947571)
        ·
          refine ⟨8382643039444166387921357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5588428692962777591947571 8382643039444166387921357)
          ·
            refine ⟨3143491139791562395470509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8382643039444166387921357 3143491139791562395470509)
            ·
              refine ⟨1178809177421835898301441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3143491139791562395470509 1178809177421835898301441)
              ·
                refine ⟨884106883066376923726081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178809177421835898301441 884106883066376923726081)
                ·
                  refine ⟨663080162299782692794561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 884106883066376923726081 663080162299782692794561)
                  ·
                    refine ⟨497310121724837019595921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 663080162299782692794561 497310121724837019595921)
                    ·
                      refine ⟨372982591293627764696941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497310121724837019595921 372982591293627764696941)
                      ·
                        rfl

theorem cell23_726381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_726381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726381 prefixEnd_726381 := by exact prefixLift 726381
  have htrace : WordTrace (prefixWord ++ tailWord_726381) baseStart_726381 baseEnd_726381 := by
    simpa [prefixWord, tailWord_726381, baseEnd_726381] using wordTrace_append hprefix tailTrace_726381
  have hstable : (prefixWord ++ tailWord_726381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726381).length < 2 ^ (prefixWord ++ tailWord_726381).sum := by decide
  have hdescent : baseEnd_726381 < baseStart_726381 := by decide
  rcases family_descends (prefixWord ++ tailWord_726381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726437 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 2, 4, 2]
def baseStart_726437 : Nat := 118140960795 + 726437 * 2 ^ 59
def prefixEnd_726437 : Nat := 4983230072969 + 3 ^ 40 * 726437 * 2
def baseEnd_726437 : Nat := 373011346210279545596683

theorem tailTrace_726437 : CollatzResearch.WordTrace tailWord_726437 prefixEnd_726437 373011346210279545596683 := by
  unfold tailWord_726437
  simp only [CollatzResearch.WordTrace]
  refine ⟨26495334069250289407345565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17663556046166859604897043 26495334069250289407345565)
  ·
    refine ⟨9935750275968858527754587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26495334069250289407345565 9935750275968858527754587)
    ·
      refine ⟨14903625413953287791631881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935750275968858527754587 14903625413953287791631881)
      ·
        refine ⟨11177719060464965843723911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14903625413953287791631881 11177719060464965843723911)
        ·
          refine ⟨16766578590697448765585867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11177719060464965843723911 16766578590697448765585867)
          ·
            refine ⟨25149867886046173148378801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16766578590697448765585867 25149867886046173148378801)
            ·
              refine ⟨18862400914534629861284101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25149867886046173148378801 18862400914534629861284101)
              ·
                refine ⟨3536700171475243098990769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18862400914534629861284101 3536700171475243098990769)
                ·
                  refine ⟨2652525128606432324243077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3536700171475243098990769 2652525128606432324243077)
                  ·
                    refine ⟨497348461613706060795577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2652525128606432324243077 497348461613706060795577)
                    ·
                      refine ⟨373011346210279545596683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497348461613706060795577 373011346210279545596683)
                      ·
                        rfl

theorem cell23_726437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_726437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726437 prefixEnd_726437 := by exact prefixLift 726437
  have htrace : WordTrace (prefixWord ++ tailWord_726437) baseStart_726437 baseEnd_726437 := by
    simpa [prefixWord, tailWord_726437, baseEnd_726437] using wordTrace_append hprefix tailTrace_726437
  have hstable : (prefixWord ++ tailWord_726437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726437).length < 2 ^ (prefixWord ++ tailWord_726437).sum := by decide
  have hdescent : baseEnd_726437 < baseStart_726437 := by decide
  rcases family_descends (prefixWord ++ tailWord_726437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726450 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_726450 : Nat := 118140960795 + 726450 * 2 ^ 59
def prefixEnd_726450 : Nat := 4983230072969 + 3 ^ 40 * 726450 * 2
def baseEnd_726450 : Nat := 373018021458787994734123

theorem tailTrace_726450 : CollatzResearch.WordTrace tailWord_726450 prefixEnd_726450 373018021458787994734123 := by
  unfold tailWord_726450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623952054550798156892201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17663872145468795085045869 6623952054550798156892201)
  ·
    refine ⟨4967964040913098617669151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6623952054550798156892201 4967964040913098617669151)
    ·
      refine ⟨7451946061369647926503727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4967964040913098617669151 7451946061369647926503727)
      ·
        refine ⟨11177919092054471889755591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7451946061369647926503727 11177919092054471889755591)
        ·
          refine ⟨16766878638081707834633387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11177919092054471889755591 16766878638081707834633387)
          ·
            refine ⟨25150317957122561751950081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16766878638081707834633387 25150317957122561751950081)
            ·
              refine ⟨18862738467841921313962561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25150317957122561751950081 18862738467841921313962561)
              ·
                refine ⟨14147053850881440985471921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18862738467841921313962561 14147053850881440985471921)
                ·
                  refine ⟨10610290388161080739103941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14147053850881440985471921 10610290388161080739103941)
                  ·
                    refine ⟨1989429447780202638581989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10610290388161080739103941 1989429447780202638581989)
                    ·
                      refine ⟨373018021458787994734123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1989429447780202638581989 373018021458787994734123)
                      ·
                        rfl

theorem cell23_726450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_726450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726450 prefixEnd_726450 := by exact prefixLift 726450
  have htrace : WordTrace (prefixWord ++ tailWord_726450) baseStart_726450 baseEnd_726450 := by
    simpa [prefixWord, tailWord_726450, baseEnd_726450] using wordTrace_append hprefix tailTrace_726450
  have hstable : (prefixWord ++ tailWord_726450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726450).length < 2 ^ (prefixWord ++ tailWord_726450).sum := by decide
  have hdescent : baseEnd_726450 < baseStart_726450 := by decide
  rcases family_descends (prefixWord ++ tailWord_726450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726474 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_726474 : Nat := 118140960795 + 726474 * 2 ^ 59
def prefixEnd_726474 : Nat := 4983230072969 + 3 ^ 40 * 726474 * 2
def baseEnd_726474 : Nat := 373030344994495900834013

theorem tailTrace_726474 : CollatzResearch.WordTrace tailWord_726474 prefixEnd_726474 373030344994495900834013 := by
  unfold tailWord_726474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6624170892529061181610619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17664455713410829817628317 6624170892529061181610619)
  ·
    refine ⟨9936256338793591772415929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6624170892529061181610619 9936256338793591772415929)
    ·
      refine ⟨7452192254095193829311947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9936256338793591772415929 7452192254095193829311947)
      ·
        refine ⟨11178288381142790743967921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7452192254095193829311947 11178288381142790743967921)
        ·
          refine ⟨8383716285857093057975941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11178288381142790743967921 8383716285857093057975941)
          ·
            refine ⟨1571946803598204948370489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8383716285857093057975941 1571946803598204948370489)
            ·
              refine ⟨1178960102698653711277867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1571946803598204948370489 1178960102698653711277867)
              ·
                refine ⟨1768440154047980566916801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178960102698653711277867 1768440154047980566916801)
                ·
                  refine ⟨1326330115535985425187601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1768440154047980566916801 1326330115535985425187601)
                  ·
                    refine ⟨994747586651989068890701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1326330115535985425187601 994747586651989068890701)
                    ·
                      refine ⟨373030344994495900834013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 994747586651989068890701 373030344994495900834013)
                      ·
                        rfl

theorem cell23_726474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_726474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726474 prefixEnd_726474 := by exact prefixLift 726474
  have htrace : WordTrace (prefixWord ++ tailWord_726474) baseStart_726474 baseEnd_726474 := by
    simpa [prefixWord, tailWord_726474, baseEnd_726474] using wordTrace_append hprefix tailTrace_726474
  have hstable : (prefixWord ++ tailWord_726474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726474).length < 2 ^ (prefixWord ++ tailWord_726474).sum := by decide
  have hdescent : baseEnd_726474 < baseStart_726474 := by decide
  rcases family_descends (prefixWord ++ tailWord_726474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726500 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_726500 : Nat := 118140960795 + 726500 * 2 ^ 59
def prefixEnd_726500 : Nat := 4983230072969 + 3 ^ 40 * 726500 * 2
def baseEnd_726500 : Nat := 373043695491512799108893

theorem tailTrace_726500 : CollatzResearch.WordTrace tailWord_726500 prefixEnd_726500 373043695491512799108893 := by
  unfold tailWord_726500
  simp only [CollatzResearch.WordTrace]
  refine ⟨13248815934011025583444477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17665087912014700777925969 13248815934011025583444477)
  ·
    refine ⟨4968305975254134593791679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13248815934011025583444477 4968305975254134593791679)
    ·
      refine ⟨7452458962881201890687519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4968305975254134593791679 7452458962881201890687519)
      ·
        refine ⟨11178688444321802836031279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7452458962881201890687519 11178688444321802836031279)
        ·
          refine ⟨16768032666482704254046919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11178688444321802836031279 16768032666482704254046919)
          ·
            refine ⟨25152048999724056381070379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16768032666482704254046919 25152048999724056381070379)
            ·
              refine ⟨37728073499586084571605569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25152048999724056381070379 37728073499586084571605569)
              ·
                refine ⟨28296055124689563428704177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37728073499586084571605569 28296055124689563428704177)
                ·
                  refine ⟨21222041343517172571528133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28296055124689563428704177 21222041343517172571528133)
                  ·
                    refine ⟨3979132751909469857161525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21222041343517172571528133 3979132751909469857161525)
                    ·
                      refine ⟨373043695491512799108893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3979132751909469857161525 373043695491512799108893)
                      ·
                        rfl

theorem cell23_726500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_726500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726500 prefixEnd_726500 := by exact prefixLift 726500
  have htrace : WordTrace (prefixWord ++ tailWord_726500) baseStart_726500 baseEnd_726500 := by
    simpa [prefixWord, tailWord_726500, baseEnd_726500] using wordTrace_append hprefix tailTrace_726500
  have hstable : (prefixWord ++ tailWord_726500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726500).length < 2 ^ (prefixWord ++ tailWord_726500).sum := by decide
  have hdescent : baseEnd_726500 < baseStart_726500 := by decide
  rcases family_descends (prefixWord ++ tailWord_726500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726504 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_726504 : Nat := 118140960795 + 726504 * 2 ^ 59
def prefixEnd_726504 : Nat := 4983230072969 + 3 ^ 40 * 726504 * 2
def baseEnd_726504 : Nat := 373045749414130783458875

theorem tailTrace_726504 : CollatzResearch.WordTrace tailWord_726504 prefixEnd_726504 373045749414130783458875 := by
  unfold tailWord_726504
  simp only [CollatzResearch.WordTrace]
  refine ⟨13248888880003779925017283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17665185173338373233356377 13248888880003779925017283)
  ·
    refine ⟨19873333320005669887525925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13248888880003779925017283 19873333320005669887525925)
    ·
      refine ⟨3726249997501063103911111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19873333320005669887525925 3726249997501063103911111)
      ·
        refine ⟨5589374996251594655866667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3726249997501063103911111 5589374996251594655866667)
        ·
          refine ⟨8384062494377391983800001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5589374996251594655866667 8384062494377391983800001)
          ·
            refine ⟨6288046870783043987850001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8384062494377391983800001 6288046870783043987850001)
            ·
              refine ⟨4716035153087282990887501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6288046870783043987850001 4716035153087282990887501)
              ·
                refine ⟨1768513182407731121582813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4716035153087282990887501 1768513182407731121582813)
                ·
                  refine ⟨663192443402899170593555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1768513182407731121582813 663192443402899170593555)
                  ·
                    refine ⟨994788665104348755890333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 663192443402899170593555 994788665104348755890333)
                    ·
                      refine ⟨373045749414130783458875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 994788665104348755890333 373045749414130783458875)
                      ·
                        rfl

theorem cell23_726504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_726504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726504 prefixEnd_726504 := by exact prefixLift 726504
  have htrace : WordTrace (prefixWord ++ tailWord_726504) baseStart_726504 baseEnd_726504 := by
    simpa [prefixWord, tailWord_726504, baseEnd_726504] using wordTrace_append hprefix tailTrace_726504
  have hstable : (prefixWord ++ tailWord_726504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726504).length < 2 ^ (prefixWord ++ tailWord_726504).sum := by decide
  have hdescent : baseEnd_726504 < baseStart_726504 := by decide
  rcases family_descends (prefixWord ++ tailWord_726504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726527 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 1, 8, 2]
def baseStart_726527 : Nat := 118140960795 + 726527 * 2 ^ 59
def prefixEnd_726527 : Nat := 4983230072969 + 3 ^ 40 * 726527 * 2
def baseEnd_726527 : Nat := 373057559469184193471269

theorem tailTrace_726527 : CollatzResearch.WordTrace tailWord_726527 prefixEnd_726527 373057559469184193471269 := by
  unfold tailWord_726527
  simp only [CollatzResearch.WordTrace]
  refine ⟨26498616638924234778121835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17665744425949489852081223 26498616638924234778121835)
  ·
    refine ⟨39747924958386352167182753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26498616638924234778121835 39747924958386352167182753)
    ·
      refine ⟨29810943718789764125387065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39747924958386352167182753 29810943718789764125387065)
      ·
        refine ⟨22358207789092323094040299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29810943718789764125387065 22358207789092323094040299)
        ·
          refine ⟨33537311683638484641060449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22358207789092323094040299 33537311683638484641060449)
          ·
            refine ⟨25152983762728863480795337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33537311683638484641060449 25152983762728863480795337)
            ·
              refine ⟨18864737822046647610596503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25152983762728863480795337 18864737822046647610596503)
              ·
                refine ⟨28297106733069971415894755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18864737822046647610596503 28297106733069971415894755)
                ·
                  refine ⟨42445660099604957123842133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28297106733069971415894755 42445660099604957123842133)
                  ·
                    refine ⟨497410079292245591295025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42445660099604957123842133 497410079292245591295025)
                    ·
                      refine ⟨373057559469184193471269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497410079292245591295025 373057559469184193471269)
                      ·
                        rfl

theorem cell23_726527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_726527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726527 prefixEnd_726527 := by exact prefixLift 726527
  have htrace : WordTrace (prefixWord ++ tailWord_726527) baseStart_726527 baseEnd_726527 := by
    simpa [prefixWord, tailWord_726527, baseEnd_726527] using wordTrace_append hprefix tailTrace_726527
  have hstable : (prefixWord ++ tailWord_726527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726527).length < 2 ^ (prefixWord ++ tailWord_726527).sum := by decide
  have hdescent : baseEnd_726527 < baseStart_726527 := by decide
  rcases family_descends (prefixWord ++ tailWord_726527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726537 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 4, 4]
def baseStart_726537 : Nat := 118140960795 + 726537 * 2 ^ 59
def prefixEnd_726537 : Nat := 4983230072969 + 3 ^ 40 * 726537 * 2
def baseEnd_726537 : Nat := 124354231425243051448741

theorem tailTrace_726537 : CollatzResearch.WordTrace tailWord_726537 prefixEnd_726537 124354231425243051448741 := by
  unfold tailWord_726537
  simp only [CollatzResearch.WordTrace]
  refine ⟨26498981368888006485985865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17665987579258670990657243 26498981368888006485985865)
  ·
    refine ⟨19874236026666004864489399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26498981368888006485985865 19874236026666004864489399)
    ·
      refine ⟨29811354039999007296734099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19874236026666004864489399 29811354039999007296734099)
      ·
        refine ⟨44717031059998510945101149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29811354039999007296734099 44717031059998510945101149)
        ·
          refine ⟨16768886647499441604412931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44717031059998510945101149 16768886647499441604412931)
          ·
            refine ⟨25153329971249162406619397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16768886647499441604412931 25153329971249162406619397)
            ·
              refine ⟨4716249369609217951241137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25153329971249162406619397 4716249369609217951241137)
              ·
                refine ⟨3537187027206913463430853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4716249369609217951241137 3537187027206913463430853)
                ·
                  refine ⟨663222567601296274393285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3537187027206913463430853 663222567601296274393285)
                  ·
                    refine ⟨124354231425243051448741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 663222567601296274393285 124354231425243051448741)
                    ·
                      rfl

theorem cell23_726537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 4].length) (baseStart_726537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726537 prefixEnd_726537 := by exact prefixLift 726537
  have htrace : WordTrace (prefixWord ++ tailWord_726537) baseStart_726537 baseEnd_726537 := by
    simpa [prefixWord, tailWord_726537, baseEnd_726537] using wordTrace_append hprefix tailTrace_726537
  have hstable : (prefixWord ++ tailWord_726537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726537).length < 2 ^ (prefixWord ++ tailWord_726537).sum := by decide
  have hdescent : baseEnd_726537 < baseStart_726537 := by decide
  rcases family_descends (prefixWord ++ tailWord_726537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726538 : List Nat := [3, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3]
def baseStart_726538 : Nat := 118140960795 + 726538 * 2 ^ 59
def prefixEnd_726538 : Nat := 4983230072969 + 3 ^ 40 * 726538 * 2
def baseEnd_726538 : Nat := 373063207756383650433719

theorem tailTrace_726538 : CollatzResearch.WordTrace tailWord_726538 prefixEnd_726538 373063207756383650433719 := by
  unfold tailWord_726538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6624754460471095914193067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17666011894589589104514845 6624754460471095914193067)
  ·
    refine ⟨9937131690706643871289601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6624754460471095914193067 9937131690706643871289601)
    ·
      refine ⟨7452848768029982903467201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9937131690706643871289601 7452848768029982903467201)
      ·
        refine ⟨5589636576022487177600401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7452848768029982903467201 5589636576022487177600401)
        ·
          refine ⟨4192227432016865383200301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5589636576022487177600401 4192227432016865383200301)
          ·
            refine ⟨1572085287006324518700113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4192227432016865383200301 1572085287006324518700113)
            ·
              refine ⟨1179063965254743389025085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1572085287006324518700113 1179063965254743389025085)
              ·
                refine ⟨442148986970528770884407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1179063965254743389025085 442148986970528770884407)
                ·
                  refine ⟨663223480455793156326611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442148986970528770884407 663223480455793156326611)
                  ·
                    refine ⟨994835220683689734489917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 663223480455793156326611 994835220683689734489917)
                    ·
                      refine ⟨373063207756383650433719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 994835220683689734489917 373063207756383650433719)
                      ·
                        rfl

theorem cell23_726538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_726538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726538 prefixEnd_726538 := by exact prefixLift 726538
  have htrace : WordTrace (prefixWord ++ tailWord_726538) baseStart_726538 baseEnd_726538 := by
    simpa [prefixWord, tailWord_726538, baseEnd_726538] using wordTrace_append hprefix tailTrace_726538
  have hstable : (prefixWord ++ tailWord_726538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726538).length < 2 ^ (prefixWord ++ tailWord_726538).sum := by decide
  have hdescent : baseEnd_726538 < baseStart_726538 := by decide
  rcases family_descends (prefixWord ++ tailWord_726538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726557 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_726557 : Nat := 118140960795 + 726557 * 2 ^ 59
def prefixEnd_726557 : Nat := 4983230072969 + 3 ^ 40 * 726557 * 2
def baseEnd_726557 : Nat := 373072963888819076096131

theorem tailTrace_726557 : CollatzResearch.WordTrace tailWord_726557 prefixEnd_726557 373072963888819076096131 := by
  unfold tailWord_726557
  simp only [CollatzResearch.WordTrace]
  refine ⟨26499710828815549901713925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17666473885877033267809283 26499710828815549901713925)
  ·
    refine ⟨4968695780402915606571361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26499710828815549901713925 4968695780402915606571361)
    ·
      refine ⟨3726521835302186704928521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4968695780402915606571361 3726521835302186704928521)
      ·
        refine ⟨2794891376476640028696391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3726521835302186704928521 2794891376476640028696391)
        ·
          refine ⟨4192337064714960043044587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794891376476640028696391 4192337064714960043044587)
          ·
            refine ⟨6288505597072440064566881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192337064714960043044587 6288505597072440064566881)
            ·
              refine ⟨4716379197804330048425161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6288505597072440064566881 4716379197804330048425161)
              ·
                refine ⟨3537284398353247536318871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4716379197804330048425161 3537284398353247536318871)
                ·
                  refine ⟨5305926597529871304478307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537284398353247536318871 5305926597529871304478307)
                  ·
                    refine ⟨7958889896294806956717461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5305926597529871304478307 7958889896294806956717461)
                    ·
                      refine ⟨373072963888819076096131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7958889896294806956717461 373072963888819076096131)
                      ·
                        rfl

theorem cell23_726557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_726557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726557 prefixEnd_726557 := by exact prefixLift 726557
  have htrace : WordTrace (prefixWord ++ tailWord_726557) baseStart_726557 baseEnd_726557 := by
    simpa [prefixWord, tailWord_726557, baseEnd_726557] using wordTrace_append hprefix tailTrace_726557
  have hstable : (prefixWord ++ tailWord_726557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726557).length < 2 ^ (prefixWord ++ tailWord_726557).sum := by decide
  have hdescent : baseEnd_726557 < baseStart_726557 := by decide
  rcases family_descends (prefixWord ++ tailWord_726557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726561 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 3, 2, 2]
def baseStart_726561 : Nat := 118140960795 + 726561 * 2 ^ 59
def prefixEnd_726561 : Nat := 4983230072969 + 3 ^ 40 * 726561 * 2
def baseEnd_726561 : Nat := 373075017811437060446113

theorem tailTrace_726561 : CollatzResearch.WordTrace tailWord_726561 prefixEnd_726561 373075017811437060446113 := by
  unfold tailWord_726561
  simp only [CollatzResearch.WordTrace]
  refine ⟨26499856720801058584859537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17666571147200705723239691 26499856720801058584859537)
  ·
    refine ⟨19874892540600793938644653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26499856720801058584859537 19874892540600793938644653)
    ·
      refine ⟨7453084702725297726991745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19874892540600793938644653 7453084702725297726991745)
      ·
        refine ⟨5589813527043973295243809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7453084702725297726991745 5589813527043973295243809)
        ·
          refine ⟨4192360145282979971432857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5589813527043973295243809 4192360145282979971432857)
          ·
            refine ⟨3144270108962234978574643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4192360145282979971432857 3144270108962234978574643)
            ·
              refine ⟨4716405163443352467861965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144270108962234978574643 4716405163443352467861965)
              ·
                refine ⟨1768651936291257175448237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4716405163443352467861965 1768651936291257175448237)
                ·
                  refine ⟨663244476109221440793089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1768651936291257175448237 663244476109221440793089)
                  ·
                    refine ⟨497433357081916080594817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 663244476109221440793089 497433357081916080594817)
                    ·
                      refine ⟨373075017811437060446113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497433357081916080594817 373075017811437060446113)
                      ·
                        rfl

theorem cell23_726561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_726561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726561 prefixEnd_726561 := by exact prefixLift 726561
  have htrace : WordTrace (prefixWord ++ tailWord_726561) baseStart_726561 baseEnd_726561 := by
    simpa [prefixWord, tailWord_726561, baseEnd_726561] using wordTrace_append hprefix tailTrace_726561
  have hstable : (prefixWord ++ tailWord_726561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726561).length < 2 ^ (prefixWord ++ tailWord_726561).sum := by decide
  have hdescent : baseEnd_726561 < baseStart_726561 := by decide
  rcases family_descends (prefixWord ++ tailWord_726561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726574 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_726574 : Nat := 118140960795 + 726574 * 2 ^ 59
def prefixEnd_726574 : Nat := 4983230072969 + 3 ^ 40 * 726574 * 2
def baseEnd_726574 : Nat := 373081693059945509583553

theorem tailTrace_726574 : CollatzResearch.WordTrace tailWord_726574 prefixEnd_726574 373081693059945509583553 := by
  unfold tailWord_726574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3312541358719245225635347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17666887246502641203388517 3312541358719245225635347)
  ·
    refine ⟨4968812038078867838453021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3312541358719245225635347 4968812038078867838453021)
    ·
      refine ⟨1863304514279575439419883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4968812038078867838453021 1863304514279575439419883)
      ·
        refine ⟨2794956771419363159129825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863304514279575439419883 2794956771419363159129825)
        ·
          refine ⟨2096217578564522369347369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2794956771419363159129825 2096217578564522369347369)
          ·
            refine ⟨1572163183923391777010527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2096217578564522369347369 1572163183923391777010527)
            ·
              refine ⟨2358244775885087665515791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572163183923391777010527 2358244775885087665515791)
              ·
                refine ⟨3537367163827631498273687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358244775885087665515791 3537367163827631498273687)
                ·
                  refine ⟨5306050745741447247410531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537367163827631498273687 5306050745741447247410531)
                  ·
                    refine ⟨7959076118612170871115797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5306050745741447247410531 7959076118612170871115797)
                    ·
                      refine ⟨373081693059945509583553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7959076118612170871115797 373081693059945509583553)
                      ·
                        rfl

theorem cell23_726574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_726574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726574 prefixEnd_726574 := by exact prefixLift 726574
  have htrace : WordTrace (prefixWord ++ tailWord_726574) baseStart_726574 baseEnd_726574 := by
    simpa [prefixWord, tailWord_726574, baseEnd_726574] using wordTrace_append hprefix tailTrace_726574
  have hstable : (prefixWord ++ tailWord_726574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726574).length < 2 ^ (prefixWord ++ tailWord_726574).sum := by decide
  have hdescent : baseEnd_726574 < baseStart_726574 := by decide
  rcases family_descends (prefixWord ++ tailWord_726574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726581 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_726581 : Nat := 118140960795 + 726581 * 2 ^ 59
def prefixEnd_726581 : Nat := 4983230072969 + 3 ^ 40 * 726581 * 2
def baseEnd_726581 : Nat := 373085287424526982196021

theorem tailTrace_726581 : CollatzResearch.WordTrace tailWord_726581 prefixEnd_726581 373085287424526982196021 := by
  unfold tailWord_726581
  simp only [CollatzResearch.WordTrace]
  refine ⟨26500586180728602000587597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17667057453819068000391731 26500586180728602000587597)
  ·
    refine ⟨9937719817773225750220349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26500586180728602000587597 9937719817773225750220349)
    ·
      refine ⟨3726644931664959656332631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9937719817773225750220349 3726644931664959656332631)
      ·
        refine ⟨5589967397497439484498947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3726644931664959656332631 5589967397497439484498947)
        ·
          refine ⟨8384951096246159226748421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5589967397497439484498947 8384951096246159226748421)
          ·
            refine ⟨1572178330546154855015329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8384951096246159226748421 1572178330546154855015329)
            ·
              refine ⟨1179133747909616141261497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1572178330546154855015329 1179133747909616141261497)
              ·
                refine ⟨884350310932212105946123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1179133747909616141261497 884350310932212105946123)
                ·
                  refine ⟨1326525466398318158919185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884350310932212105946123 1326525466398318158919185)
                  ·
                    refine ⟨994894099798738619189389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1326525466398318158919185 994894099798738619189389)
                    ·
                      refine ⟨373085287424526982196021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 994894099798738619189389 373085287424526982196021)
                      ·
                        rfl

theorem cell23_726581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_726581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726581 prefixEnd_726581 := by exact prefixLift 726581
  have htrace : WordTrace (prefixWord ++ tailWord_726581) baseStart_726581 baseEnd_726581 := by
    simpa [prefixWord, tailWord_726581, baseEnd_726581] using wordTrace_append hprefix tailTrace_726581
  have hstable : (prefixWord ++ tailWord_726581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726581).length < 2 ^ (prefixWord ++ tailWord_726581).sum := by decide
  have hdescent : baseEnd_726581 < baseStart_726581 := by decide
  rcases family_descends (prefixWord ++ tailWord_726581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726584 : List Nat := [2, 1, 2, 1, 4, 4, 2, 7]
def baseStart_726584 : Nat := 118140960795 + 726584 * 2 ^ 59
def prefixEnd_726584 : Nat := 4983230072969 + 3 ^ 40 * 726584 * 2
def baseEnd_726584 : Nat := 13818030661721869276241

theorem tailTrace_726584 : CollatzResearch.WordTrace tailWord_726584 prefixEnd_726584 13818030661721869276241 := by
  unfold tailWord_726584
  simp only [CollatzResearch.WordTrace]
  refine ⟨13250347799858866756473403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17667130399811822341964537 13250347799858866756473403)
  ·
    refine ⟨19875521699788300134710105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13250347799858866756473403 19875521699788300134710105)
    ·
      refine ⟨14906641274841225101032579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19875521699788300134710105 14906641274841225101032579)
      ·
        refine ⟨22359961912261837651548869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14906641274841225101032579 22359961912261837651548869)
        ·
          refine ⟨4192492858549094559665413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22359961912261837651548869 4192492858549094559665413)
          ·
            refine ⟨786092410977955229937265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4192492858549094559665413 786092410977955229937265)
            ·
              refine ⟨589569308233466422452949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786092410977955229937265 589569308233466422452949)
              ·
                refine ⟨13818030661721869276241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 589569308233466422452949 13818030661721869276241)
                ·
                  rfl

theorem cell23_726584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 7].length) (baseStart_726584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726584 prefixEnd_726584 := by exact prefixLift 726584
  have htrace : WordTrace (prefixWord ++ tailWord_726584) baseStart_726584 baseEnd_726584 := by
    simpa [prefixWord, tailWord_726584, baseEnd_726584] using wordTrace_append hprefix tailTrace_726584
  have hstable : (prefixWord ++ tailWord_726584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726584).length < 2 ^ (prefixWord ++ tailWord_726584).sum := by decide
  have hdescent : baseEnd_726584 < baseStart_726584 := by decide
  rcases family_descends (prefixWord ++ tailWord_726584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726598 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_726598 : Nat := 118140960795 + 726598 * 2 ^ 59
def prefixEnd_726598 : Nat := 4983230072969 + 3 ^ 40 * 726598 * 2
def baseEnd_726598 : Nat := 373094016595653415683443

theorem tailTrace_726598 : CollatzResearch.WordTrace tailWord_726598 prefixEnd_726598 373094016595653415683443 := by
  unfold tailWord_726598
  simp only [CollatzResearch.WordTrace]
  refine ⟨828162694427094184498639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17667470814444675935970965 828162694427094184498639)
  ·
    refine ⟨1242244041640641276747959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 828162694427094184498639 1242244041640641276747959)
    ·
      refine ⟨1863366062460961915121939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1242244041640641276747959 1863366062460961915121939)
      ·
        refine ⟨2795049093691442872682909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863366062460961915121939 2795049093691442872682909)
        ·
          refine ⟨1048143410134291077256091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2795049093691442872682909 1048143410134291077256091)
          ·
            refine ⟨1572215115201436615884137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048143410134291077256091 1572215115201436615884137)
            ·
              refine ⟨1179161336401077461913103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1572215115201436615884137 1179161336401077461913103)
              ·
                refine ⟨1768742004601616192869655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179161336401077461913103 1768742004601616192869655)
                ·
                  refine ⟨2653113006902424289304483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768742004601616192869655 2653113006902424289304483)
                  ·
                    refine ⟨3979669510353636433956725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2653113006902424289304483 3979669510353636433956725)
                    ·
                      refine ⟨373094016595653415683443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3979669510353636433956725 373094016595653415683443)
                      ·
                        rfl

theorem cell23_726598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_726598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726598 prefixEnd_726598 := by exact prefixLift 726598
  have htrace : WordTrace (prefixWord ++ tailWord_726598) baseStart_726598 baseEnd_726598 := by
    simpa [prefixWord, tailWord_726598, baseEnd_726598] using wordTrace_append hprefix tailTrace_726598
  have hstable : (prefixWord ++ tailWord_726598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726598).length < 2 ^ (prefixWord ++ tailWord_726598).sum := by decide
  have hdescent : baseEnd_726598 < baseStart_726598 := by decide
  rcases family_descends (prefixWord ++ tailWord_726598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726628 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 2, 1, 3]
def baseStart_726628 : Nat := 118140960795 + 726628 * 2 ^ 59
def prefixEnd_726628 : Nat := 4983230072969 + 3 ^ 40 * 726628 * 2
def baseEnd_726628 : Nat := 373109421015288298308305

theorem tailTrace_726628 : CollatzResearch.WordTrace tailWord_726628 prefixEnd_726628 373109421015288298308305 := by
  unfold tailWord_726628
  simp only [CollatzResearch.WordTrace]
  refine ⟨13251150205779164513774269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17668200274372219351699025 13251150205779164513774269)
  ·
    refine ⟨4969181327167186692665351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13251150205779164513774269 4969181327167186692665351)
    ·
      refine ⟨7453771990750780038998027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4969181327167186692665351 7453771990750780038998027)
      ·
        refine ⟨11180657986126170058497041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7453771990750780038998027 11180657986126170058497041)
        ·
          refine ⟨8385493489594627543872781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11180657986126170058497041 8385493489594627543872781)
          ·
            refine ⟨3144560058597985328952293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8385493489594627543872781 3144560058597985328952293)
            ·
              refine ⟨589605010987122249178555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3144560058597985328952293 589605010987122249178555)
              ·
                refine ⟨884407516480683373767833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589605010987122249178555 884407516480683373767833)
                ·
                  refine ⟨663305637360512530325875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 884407516480683373767833 663305637360512530325875)
                  ·
                    refine ⟨994958456040768795488813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 663305637360512530325875 994958456040768795488813)
                    ·
                      refine ⟨373109421015288298308305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 994958456040768795488813 373109421015288298308305)
                      ·
                        rfl

theorem cell23_726628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_726628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726628 prefixEnd_726628 := by exact prefixLift 726628
  have htrace : WordTrace (prefixWord ++ tailWord_726628) baseStart_726628 baseEnd_726628 := by
    simpa [prefixWord, tailWord_726628, baseEnd_726628] using wordTrace_append hprefix tailTrace_726628
  have hstable : (prefixWord ++ tailWord_726628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726628).length < 2 ^ (prefixWord ++ tailWord_726628).sum := by decide
  have hdescent : baseEnd_726628 < baseStart_726628 := by decide
  rcases family_descends (prefixWord ++ tailWord_726628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726638 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_726638 : Nat := 118140960795 + 726638 * 2 ^ 59
def prefixEnd_726638 : Nat := 4983230072969 + 3 ^ 40 * 726638 * 2
def baseEnd_726638 : Nat := 373114555821833259183259

theorem tailTrace_726638 : CollatzResearch.WordTrace tailWord_726638 prefixEnd_726638 373114555821833259183259 := by
  unfold tailWord_726638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3312833142690262591926571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17668443427681400490275045 3312833142690262591926571)
  ·
    refine ⟨4969249714035393887889857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3312833142690262591926571 4969249714035393887889857)
    ·
      refine ⟨3726937285526545415917393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4969249714035393887889857 3726937285526545415917393)
      ·
        refine ⟨2795202964144909061938045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3726937285526545415917393 2795202964144909061938045)
        ·
          refine ⟨1048201111554340898226767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2795202964144909061938045 1048201111554340898226767)
          ·
            refine ⟨1572301667331511347340151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048201111554340898226767 1572301667331511347340151)
            ·
              refine ⟨2358452500997267021010227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572301667331511347340151 2358452500997267021010227)
              ·
                refine ⟨3537678751495900531515341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358452500997267021010227 3537678751495900531515341)
                ·
                  refine ⟨1326629531810962699318253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3537678751495900531515341 1326629531810962699318253)
                  ·
                    refine ⟨497486074429111012244345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1326629531810962699318253 497486074429111012244345)
                    ·
                      refine ⟨373114555821833259183259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497486074429111012244345 373114555821833259183259)
                      ·
                        rfl

theorem cell23_726638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_726638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726638 prefixEnd_726638 := by exact prefixLift 726638
  have htrace : WordTrace (prefixWord ++ tailWord_726638) baseStart_726638 baseEnd_726638 := by
    simpa [prefixWord, tailWord_726638, baseEnd_726638] using wordTrace_append hprefix tailTrace_726638
  have hstable : (prefixWord ++ tailWord_726638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726638).length < 2 ^ (prefixWord ++ tailWord_726638).sum := by decide
  have hdescent : baseEnd_726638 < baseStart_726638 := by decide
  rcases family_descends (prefixWord ++ tailWord_726638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726647 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_726647 : Nat := 118140960795 + 726647 * 2 ^ 59
def prefixEnd_726647 : Nat := 4983230072969 + 3 ^ 40 * 726647 * 2
def baseEnd_726647 : Nat := 373119177147723723970717

theorem tailTrace_726647 : CollatzResearch.WordTrace tailWord_726647 prefixEnd_726647 373119177147723723970717 := by
  unfold tailWord_726647
  simp only [CollatzResearch.WordTrace]
  refine ⟨26502993398489495272490195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17668662265659663514993463 26502993398489495272490195)
  ·
    refine ⟨39754490097734242908735293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26502993398489495272490195 39754490097734242908735293)
    ·
      refine ⟨14907933786650341090775735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39754490097734242908735293 14907933786650341090775735)
      ·
        refine ⟨22361900679975511636163603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14907933786650341090775735 22361900679975511636163603)
        ·
          refine ⟨33542851019963267454245405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22361900679975511636163603 33542851019963267454245405)
          ·
            refine ⟨12578569132486225295342027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33542851019963267454245405 12578569132486225295342027)
            ·
              refine ⟨18867853698729337943013041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12578569132486225295342027 18867853698729337943013041)
              ·
                refine ⟨14150890274047003457259781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18867853698729337943013041 14150890274047003457259781)
                ·
                  refine ⟨2653291926383813148236209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14150890274047003457259781 2653291926383813148236209)
                  ·
                    refine ⟨1989968944787859861177157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2653291926383813148236209 1989968944787859861177157)
                    ·
                      refine ⟨373119177147723723970717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1989968944787859861177157 373119177147723723970717)
                      ·
                        rfl

theorem cell23_726647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_726647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726647 prefixEnd_726647 := by exact prefixLift 726647
  have htrace : WordTrace (prefixWord ++ tailWord_726647) baseStart_726647 baseEnd_726647 := by
    simpa [prefixWord, tailWord_726647, baseEnd_726647] using wordTrace_append hprefix tailTrace_726647
  have hstable : (prefixWord ++ tailWord_726647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726647).length < 2 ^ (prefixWord ++ tailWord_726647).sum := by decide
  have hdescent : baseEnd_726647 < baseStart_726647 := by decide
  rcases family_descends (prefixWord ++ tailWord_726647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726668 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 2, 2, 2]
def baseStart_726668 : Nat := 118140960795 + 726668 * 2 ^ 59
def prefixEnd_726668 : Nat := 4983230072969 + 3 ^ 40 * 726668 * 2
def baseEnd_726668 : Nat := 373129960241468141808121

theorem tailTrace_726668 : CollatzResearch.WordTrace tailWord_726668 prefixEnd_726668 373129960241468141808121 := by
  unfold tailWord_726668
  simp only [CollatzResearch.WordTrace]
  refine ⟨13251879665706707929502329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17669172887608943906003105 13251879665706707929502329)
  ·
    refine ⟨9938909749280030947126747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13251879665706707929502329 9938909749280030947126747)
    ·
      refine ⟨14908364623920046420690121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9938909749280030947126747 14908364623920046420690121)
      ·
        refine ⟨11181273467940034815517591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14908364623920046420690121 11181273467940034815517591)
        ·
          refine ⟨16771910201910052223276387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11181273467940034815517591 16771910201910052223276387)
          ·
            refine ⟨25157865302865078334914581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16771910201910052223276387 25157865302865078334914581)
            ·
              refine ⟨1179274936071800546949121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25157865302865078334914581 1179274936071800546949121)
              ·
                refine ⟨884456202053850410211841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1179274936071800546949121 884456202053850410211841)
                ·
                  refine ⟨663342151540387807658881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 884456202053850410211841 663342151540387807658881)
                  ·
                    refine ⟨497506613655290855744161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 663342151540387807658881 497506613655290855744161)
                    ·
                      refine ⟨373129960241468141808121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497506613655290855744161 373129960241468141808121)
                      ·
                        rfl

theorem cell23_726668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_726668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726668 prefixEnd_726668 := by exact prefixLift 726668
  have htrace : WordTrace (prefixWord ++ tailWord_726668) baseStart_726668 baseEnd_726668 := by
    simpa [prefixWord, tailWord_726668, baseEnd_726668] using wordTrace_append hprefix tailTrace_726668
  have hstable : (prefixWord ++ tailWord_726668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726668).length < 2 ^ (prefixWord ++ tailWord_726668).sum := by decide
  have hdescent : baseEnd_726668 < baseStart_726668 := by decide
  rcases family_descends (prefixWord ++ tailWord_726668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726704 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 2, 5]
def baseStart_726704 : Nat := 118140960795 + 726704 * 2 ^ 59
def prefixEnd_726704 : Nat := 4983230072969 + 3 ^ 40 * 726704 * 2
def baseEnd_726704 : Nat := 124382815181676666985985

theorem tailTrace_726704 : CollatzResearch.WordTrace tailWord_726704 prefixEnd_726704 124382815181676666985985 := by
  unfold tailWord_726704
  simp only [CollatzResearch.WordTrace]
  refine ⟨13252536179641497003657583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17670048239521996004876777 13252536179641497003657583)
  ·
    refine ⟨19878804269462245505486375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13252536179641497003657583 19878804269462245505486375)
    ·
      refine ⟨29818206404193368258229563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19878804269462245505486375 29818206404193368258229563)
      ·
        refine ⟨44727309606290052387344345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29818206404193368258229563 44727309606290052387344345)
        ·
          refine ⟨33545482204717539290508259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44727309606290052387344345 33545482204717539290508259)
          ·
            refine ⟨50318223307076308935762389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33545482204717539290508259 50318223307076308935762389)
            ·
              refine ⟨1179333358759600990681931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 50318223307076308935762389 1179333358759600990681931)
              ·
                refine ⟨1769000038139401486022897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179333358759600990681931 1769000038139401486022897)
                ·
                  refine ⟨1326750028604551114517173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1769000038139401486022897 1326750028604551114517173)
                  ·
                    refine ⟨124382815181676666985985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1326750028604551114517173 124382815181676666985985)
                    ·
                      rfl

theorem cell23_726704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 5].length) (baseStart_726704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726704 prefixEnd_726704 := by exact prefixLift 726704
  have htrace : WordTrace (prefixWord ++ tailWord_726704) baseStart_726704 baseEnd_726704 := by
    simpa [prefixWord, tailWord_726704, baseEnd_726704] using wordTrace_append hprefix tailTrace_726704
  have hstable : (prefixWord ++ tailWord_726704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726704).length < 2 ^ (prefixWord ++ tailWord_726704).sum := by decide
  have hdescent : baseEnd_726704 < baseStart_726704 := by decide
  rcases family_descends (prefixWord ++ tailWord_726704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726744 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 3, 4, 3]
def baseStart_726744 : Nat := 118140960795 + 726744 * 2 ^ 59
def prefixEnd_726744 : Nat := 4983230072969 + 3 ^ 40 * 726744 * 2
def baseEnd_726744 : Nat := 373168984771209844457771

theorem tailTrace_726744 : CollatzResearch.WordTrace tailWord_726744 prefixEnd_726744 373168984771209844457771 := by
  unfold tailWord_726744
  simp only [CollatzResearch.WordTrace]
  refine ⟨13253265639569040419385643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17671020852758720559180857 13253265639569040419385643)
  ·
    refine ⟨19879898459353560629078465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13253265639569040419385643 19879898459353560629078465)
    ·
      refine ⟨14909923844515170471808849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19879898459353560629078465 14909923844515170471808849)
      ·
        refine ⟨11182442883386377853856637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14909923844515170471808849 11182442883386377853856637)
        ·
          refine ⟨4193416081269891695196239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11182442883386377853856637 4193416081269891695196239)
          ·
            refine ⟨6290124121904837542794359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193416081269891695196239 6290124121904837542794359)
            ·
              refine ⟨9435186182857256314191539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6290124121904837542794359 9435186182857256314191539)
              ·
                refine ⟨14152779274285884471287309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9435186182857256314191539 14152779274285884471287309)
                ·
                  refine ⟨5307292227857206676732741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14152779274285884471287309 5307292227857206676732741)
                  ·
                    refine ⟨995117292723226251887389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5307292227857206676732741 995117292723226251887389)
                    ·
                      refine ⟨373168984771209844457771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995117292723226251887389 373168984771209844457771)
                      ·
                        rfl

theorem cell23_726744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_726744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726744 prefixEnd_726744 := by exact prefixLift 726744
  have htrace : WordTrace (prefixWord ++ tailWord_726744) baseStart_726744 baseEnd_726744 := by
    simpa [prefixWord, tailWord_726744, baseEnd_726744] using wordTrace_append hprefix tailTrace_726744
  have hstable : (prefixWord ++ tailWord_726744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726744).length < 2 ^ (prefixWord ++ tailWord_726744).sum := by decide
  have hdescent : baseEnd_726744 < baseStart_726744 := by decide
  rcases family_descends (prefixWord ++ tailWord_726744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726801 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 6, 3, 2]
def baseStart_726801 : Nat := 118140960795 + 726801 * 2 ^ 59
def prefixEnd_726801 : Nat := 4983230072969 + 3 ^ 40 * 726801 * 2
def baseEnd_726801 : Nat := 373198253168516121445009

theorem tailTrace_726801 : CollatzResearch.WordTrace tailWord_726801 prefixEnd_726801 373198253168516121445009 := by
  unfold tailWord_726801
  simp only [CollatzResearch.WordTrace]
  refine ⟨26508610239931579573596257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17672406826621053049064171 26508610239931579573596257)
  ·
    refine ⟨19881457679948684680197193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26508610239931579573596257 19881457679948684680197193)
    ·
      refine ⟨14911093259961513510147895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19881457679948684680197193 14911093259961513510147895)
      ·
        refine ⟨22366639889942270265221843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14911093259961513510147895 22366639889942270265221843)
        ·
          refine ⟨33549959834913405397832765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22366639889942270265221843 33549959834913405397832765)
          ·
            refine ⟨12581234938092527024187287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33549959834913405397832765 12581234938092527024187287)
            ·
              refine ⟨18871852407138790536280931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12581234938092527024187287 18871852407138790536280931)
              ·
                refine ⟨28307778610708185804421397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18871852407138790536280931 28307778610708185804421397)
                ·
                  refine ⟨1326927122376946209582253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28307778610708185804421397 1326927122376946209582253)
                  ·
                    refine ⟨497597670891354828593345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1326927122376946209582253 497597670891354828593345)
                    ·
                      refine ⟨373198253168516121445009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497597670891354828593345 373198253168516121445009)
                      ·
                        rfl

theorem cell23_726801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_726801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726801 prefixEnd_726801 := by exact prefixLift 726801
  have htrace : WordTrace (prefixWord ++ tailWord_726801) baseStart_726801 baseEnd_726801 := by
    simpa [prefixWord, tailWord_726801, baseEnd_726801] using wordTrace_append hprefix tailTrace_726801
  have hstable : (prefixWord ++ tailWord_726801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726801).length < 2 ^ (prefixWord ++ tailWord_726801).sum := by decide
  have hdescent : baseEnd_726801 < baseStart_726801 := by decide
  rcases family_descends (prefixWord ++ tailWord_726801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726828 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 1, 5]
def baseStart_726828 : Nat := 118140960795 + 726828 * 2 ^ 59
def prefixEnd_726828 : Nat := 4983230072969 + 3 ^ 40 * 726828 * 2
def baseEnd_726828 : Nat := 124404039048729171935795

theorem tailTrace_726828 : CollatzResearch.WordTrace tailWord_726828 prefixEnd_726828 124404039048729171935795 := by
  unfold tailWord_726828
  simp only [CollatzResearch.WordTrace]
  refine ⟨13254797505416881592414569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17673063340555842123219425 13254797505416881592414569)
  ·
    refine ⟨9941098129062661194310927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13254797505416881592414569 9941098129062661194310927)
    ·
      refine ⟨14911647193593991791466391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9941098129062661194310927 14911647193593991791466391)
      ·
        refine ⟨22367470790390987687199587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14911647193593991791466391 22367470790390987687199587)
        ·
          refine ⟨33551206185586481530799381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22367470790390987687199587 33551206185586481530799381)
          ·
            refine ⟨1572712789949366321756221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33551206185586481530799381 1572712789949366321756221)
            ·
              refine ⟨589767296231012370658583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1572712789949366321756221 589767296231012370658583)
              ·
                refine ⟨884650944346518555987875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589767296231012370658583 884650944346518555987875)
                ·
                  refine ⟨1326976416519777833981813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884650944346518555987875 1326976416519777833981813)
                  ·
                    refine ⟨124404039048729171935795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1326976416519777833981813 124404039048729171935795)
                    ·
                      rfl

theorem cell23_726828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_726828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726828 prefixEnd_726828 := by exact prefixLift 726828
  have htrace : WordTrace (prefixWord ++ tailWord_726828) baseStart_726828 baseEnd_726828 := by
    simpa [prefixWord, tailWord_726828, baseEnd_726828] using wordTrace_append hprefix tailTrace_726828
  have hstable : (prefixWord ++ tailWord_726828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726828).length < 2 ^ (prefixWord ++ tailWord_726828).sum := by decide
  have hdescent : baseEnd_726828 < baseStart_726828 := by decide
  rcases family_descends (prefixWord ++ tailWord_726828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726842 : List Nat := [3, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3]
def baseStart_726842 : Nat := 118140960795 + 726842 * 2 ^ 59
def prefixEnd_726842 : Nat := 4983230072969 + 3 ^ 40 * 726842 * 2
def baseEnd_726842 : Nat := 373219305875350461032321

theorem tailTrace_726842 : CollatzResearch.WordTrace tailWord_726842 prefixEnd_726842 373219305875350461032321 := by
  unfold tailWord_726842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6627526408195760893959695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17673403755188695717225853 6627526408195760893959695)
  ·
    refine ⟨9941289612293641340939543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6627526408195760893959695 9941289612293641340939543)
    ·
      refine ⟨14911934418440462011409315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9941289612293641340939543 14911934418440462011409315)
      ·
        refine ⟨22367901627660693017113973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14911934418440462011409315 22367901627660693017113973)
        ·
          refine ⟨2096990777593189970354435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22367901627660693017113973 2096990777593189970354435)
          ·
            refine ⟨3145486166389784955531653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096990777593189970354435 3145486166389784955531653)
            ·
              refine ⟨589778656198084679162185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3145486166389784955531653 589778656198084679162185)
              ·
                refine ⟨442333992148563509371639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589778656198084679162185 442333992148563509371639)
                ·
                  refine ⟨663500988222845264057459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442333992148563509371639 663500988222845264057459)
                  ·
                    refine ⟨995251482334267896086189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 663500988222845264057459 995251482334267896086189)
                    ·
                      refine ⟨373219305875350461032321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995251482334267896086189 373219305875350461032321)
                      ·
                        rfl

theorem cell23_726842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3].length) (baseStart_726842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726842 prefixEnd_726842 := by exact prefixLift 726842
  have htrace : WordTrace (prefixWord ++ tailWord_726842) baseStart_726842 baseEnd_726842 := by
    simpa [prefixWord, tailWord_726842, baseEnd_726842] using wordTrace_append hprefix tailTrace_726842
  have hstable : (prefixWord ++ tailWord_726842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726842).length < 2 ^ (prefixWord ++ tailWord_726842).sum := by decide
  have hdescent : baseEnd_726842 < baseStart_726842 := by decide
  rcases family_descends (prefixWord ++ tailWord_726842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726844 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_726844 : Nat := 118140960795 + 726844 * 2 ^ 59
def prefixEnd_726844 : Nat := 4983230072969 + 3 ^ 40 * 726844 * 2
def baseEnd_726844 : Nat := 373220332836659453207311

theorem tailTrace_726844 : CollatzResearch.WordTrace tailWord_726844 prefixEnd_726844 373220332836659453207311 := by
  unfold tailWord_726844
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255089289387898958705793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17673452385850531944941057 13255089289387898958705793)
  ·
    refine ⟨9941316967040924219029345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13255089289387898958705793 9941316967040924219029345)
    ·
      refine ⟨7455987725280693164272009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9941316967040924219029345 7455987725280693164272009)
      ·
        refine ⟨5591990793960519873204007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7455987725280693164272009 5591990793960519873204007)
        ·
          refine ⟨8387986190940779809806011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591990793960519873204007 8387986190940779809806011)
          ·
            refine ⟨12581979286411169714709017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8387986190940779809806011 12581979286411169714709017)
            ·
              refine ⟨9436484464808377286031763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12581979286411169714709017 9436484464808377286031763)
              ·
                refine ⟨14154726697212565929047645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9436484464808377286031763 14154726697212565929047645)
                ·
                  refine ⟨5308022511454712223392867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14154726697212565929047645 5308022511454712223392867)
                  ·
                    refine ⟨7962033767182068335089301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5308022511454712223392867 7962033767182068335089301)
                    ·
                      refine ⟨373220332836659453207311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7962033767182068335089301 373220332836659453207311)
                      ·
                        rfl

theorem cell23_726844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_726844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726844 prefixEnd_726844 := by exact prefixLift 726844
  have htrace : WordTrace (prefixWord ++ tailWord_726844) baseStart_726844 baseEnd_726844 := by
    simpa [prefixWord, tailWord_726844, baseEnd_726844] using wordTrace_append hprefix tailTrace_726844
  have hstable : (prefixWord ++ tailWord_726844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726844).length < 2 ^ (prefixWord ++ tailWord_726844).sum := by decide
  have hdescent : baseEnd_726844 < baseStart_726844 := by decide
  rcases family_descends (prefixWord ++ tailWord_726844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726851 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 3]
def baseStart_726851 : Nat := 118140960795 + 726851 * 2 ^ 59
def prefixEnd_726851 : Nat := 4983230072969 + 3 ^ 40 * 726851 * 2
def baseEnd_726851 : Nat := 373223927201240925819779

theorem tailTrace_726851 : CollatzResearch.WordTrace tailWord_726851 prefixEnd_726851 373223927201240925819779 := by
  unfold tailWord_726851
  simp only [CollatzResearch.WordTrace]
  refine ⟨26510433889750438112916407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17673622593166958741944271 26510433889750438112916407)
  ·
    refine ⟨39765650834625657169374611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26510433889750438112916407 39765650834625657169374611)
    ·
      refine ⟨59648476251938485754061917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39765650834625657169374611 59648476251938485754061917)
      ·
        refine ⟨22368178594476932157773219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59648476251938485754061917 22368178594476932157773219)
        ·
          refine ⟨33552267891715398236659829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22368178594476932157773219 33552267891715398236659829)
          ·
            refine ⟨3145525114848318584686859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33552267891715398236659829 3145525114848318584686859)
            ·
              refine ⟨4718287672272477877030289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145525114848318584686859 4718287672272477877030289)
              ·
                refine ⟨3538715754204358407772717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4718287672272477877030289 3538715754204358407772717)
                ·
                  refine ⟨1327018407826634402914769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3538715754204358407772717 1327018407826634402914769)
                  ·
                    refine ⟨995263805869975802186077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1327018407826634402914769 995263805869975802186077)
                    ·
                      refine ⟨373223927201240925819779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995263805869975802186077 373223927201240925819779)
                      ·
                        rfl

theorem cell23_726851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_726851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726851 prefixEnd_726851 := by exact prefixLift 726851
  have htrace : WordTrace (prefixWord ++ tailWord_726851) baseStart_726851 baseEnd_726851 := by
    simpa [prefixWord, tailWord_726851, baseEnd_726851] using wordTrace_append hprefix tailTrace_726851
  have hstable : (prefixWord ++ tailWord_726851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726851).length < 2 ^ (prefixWord ++ tailWord_726851).sum := by decide
  have hdescent : baseEnd_726851 < baseStart_726851 := by decide
  rcases family_descends (prefixWord ++ tailWord_726851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726865 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 3, 2, 2]
def baseStart_726865 : Nat := 118140960795 + 726865 * 2 ^ 59
def prefixEnd_726865 : Nat := 4983230072969 + 3 ^ 40 * 726865 * 2
def baseEnd_726865 : Nat := 373231115930403871044715

theorem tailTrace_726865 : CollatzResearch.WordTrace tailWord_726865 prefixEnd_726865 373231115930403871044715 := by
  unfold tailWord_726865
  simp only [CollatzResearch.WordTrace]
  refine ⟨26510944511699718503926049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17673963007799812335950699 26510944511699718503926049)
  ·
    refine ⟨19883208383774788877944537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26510944511699718503926049 19883208383774788877944537)
    ·
      refine ⟨14912406287831091658458403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19883208383774788877944537 14912406287831091658458403)
      ·
        refine ⟨22368609431746637487687605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14912406287831091658458403 22368609431746637487687605)
        ·
          refine ⟨2097057134226247264470713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22368609431746637487687605 2097057134226247264470713)
          ·
            refine ⟨1572792850669685448353035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2097057134226247264470713 1572792850669685448353035)
            ·
              refine ⟨2359189276004528172529553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572792850669685448353035 2359189276004528172529553)
              ·
                refine ⟨1769391957003396129397165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2359189276004528172529553 1769391957003396129397165)
                ·
                  refine ⟨663521983876273548523937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1769391957003396129397165 663521983876273548523937)
                  ·
                    refine ⟨497641487907205161392953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 663521983876273548523937 497641487907205161392953)
                    ·
                      refine ⟨373231115930403871044715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497641487907205161392953 373231115930403871044715)
                      ·
                        rfl

theorem cell23_726865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_726865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726865 prefixEnd_726865 := by exact prefixLift 726865
  have htrace : WordTrace (prefixWord ++ tailWord_726865) baseStart_726865 baseEnd_726865 := by
    simpa [prefixWord, tailWord_726865, baseEnd_726865] using wordTrace_append hprefix tailTrace_726865
  have hstable : (prefixWord ++ tailWord_726865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726865).length < 2 ^ (prefixWord ++ tailWord_726865).sum := by decide
  have hdescent : baseEnd_726865 < baseStart_726865 := by decide
  rcases family_descends (prefixWord ++ tailWord_726865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726868 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_726868 : Nat := 118140960795 + 726868 * 2 ^ 59
def prefixEnd_726868 : Nat := 4983230072969 + 3 ^ 40 * 726868 * 2
def baseEnd_726868 : Nat := 373232656372367359307201

theorem tailTrace_726868 : CollatzResearch.WordTrace tailWord_726868 prefixEnd_726868 373232656372367359307201 := by
  unfold tailWord_726868
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255526965344425008142629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17674035953792566677523505 13255526965344425008142629)
  ·
    refine ⟨2485411306002079689026743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13255526965344425008142629 2485411306002079689026743)
    ·
      refine ⟨3728116959003119533540115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485411306002079689026743 3728116959003119533540115)
      ·
        refine ⟨5592175438504679300310173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728116959003119533540115 5592175438504679300310173)
        ·
          refine ⟨2097065789439254737616315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5592175438504679300310173 2097065789439254737616315)
          ·
            refine ⟨3145598684158882106424473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097065789439254737616315 3145598684158882106424473)
            ·
              refine ⟨2359199013119161579818355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3145598684158882106424473 2359199013119161579818355)
              ·
                refine ⟨3538798519678742369727533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359199013119161579818355 3538798519678742369727533)
                ·
                  refine ⟨1327049444879528388647825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3538798519678742369727533 1327049444879528388647825)
                  ·
                    refine ⟨995287083659646291485869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1327049444879528388647825 995287083659646291485869)
                    ·
                      refine ⟨373232656372367359307201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995287083659646291485869 373232656372367359307201)
                      ·
                        rfl

theorem cell23_726868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_726868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726868 prefixEnd_726868 := by exact prefixLift 726868
  have htrace : WordTrace (prefixWord ++ tailWord_726868) baseStart_726868 baseEnd_726868 := by
    simpa [prefixWord, tailWord_726868, baseEnd_726868] using wordTrace_append hprefix tailTrace_726868
  have hstable : (prefixWord ++ tailWord_726868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726868).length < 2 ^ (prefixWord ++ tailWord_726868).sum := by decide
  have hdescent : baseEnd_726868 < baseStart_726868 := by decide
  rcases family_descends (prefixWord ++ tailWord_726868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726881 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_726881 : Nat := 118140960795 + 726881 * 2 ^ 59
def prefixEnd_726881 : Nat := 4983230072969 + 3 ^ 40 * 726881 * 2
def baseEnd_726881 : Nat := 373239331620875808444641

theorem tailTrace_726881 : CollatzResearch.WordTrace tailWord_726881 prefixEnd_726881 373239331620875808444641 := by
  unfold tailWord_726881
  simp only [CollatzResearch.WordTrace]
  refine ⟨26511528079641753236508497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17674352053094502157672331 26511528079641753236508497)
  ·
    refine ⟨19883646059731314927381373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26511528079641753236508497 19883646059731314927381373)
    ·
      refine ⟨7456367272399243097768015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19883646059731314927381373 7456367272399243097768015)
      ·
        refine ⟨11184550908598864646652023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7456367272399243097768015 11184550908598864646652023)
        ·
          refine ⟨16776826362898296969978035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11184550908598864646652023 16776826362898296969978035)
          ·
            refine ⟨25165239544347445454967053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16776826362898296969978035 25165239544347445454967053)
            ·
              refine ⟨9436964829130292045612645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25165239544347445454967053 9436964829130292045612645)
              ·
                refine ⟨1769430905461929758552371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9436964829130292045612645 1769430905461929758552371)
                ·
                  refine ⟨2654146358192894637828557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769430905461929758552371 2654146358192894637828557)
                  ·
                    refine ⟨995304884322335489185709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2654146358192894637828557 995304884322335489185709)
                    ·
                      refine ⟨373239331620875808444641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995304884322335489185709 373239331620875808444641)
                      ·
                        rfl

theorem cell23_726881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_726881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726881 prefixEnd_726881 := by exact prefixLift 726881
  have htrace : WordTrace (prefixWord ++ tailWord_726881) baseStart_726881 baseEnd_726881 := by
    simpa [prefixWord, tailWord_726881, baseEnd_726881] using wordTrace_append hprefix tailTrace_726881
  have hstable : (prefixWord ++ tailWord_726881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726881).length < 2 ^ (prefixWord ++ tailWord_726881).sum := by decide
  have hdescent : baseEnd_726881 < baseStart_726881 := by decide
  rcases family_descends (prefixWord ++ tailWord_726881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726882 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_726882 : Nat := 118140960795 + 726882 * 2 ^ 59
def prefixEnd_726882 : Nat := 4983230072969 + 3 ^ 40 * 726882 * 2
def baseEnd_726882 : Nat := 373239845101530304532137

theorem tailTrace_726882 : CollatzResearch.WordTrace tailWord_726882 prefixEnd_726882 373239845101530304532137 := by
  unfold tailWord_726882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6627891138159532601823725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17674376368425420271529933 6627891138159532601823725)
  ·
    refine ⟨2485459176809824725683897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6627891138159532601823725 2485459176809824725683897)
    ·
      refine ⟨1864094382607368544262923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2485459176809824725683897 1864094382607368544262923)
      ·
        refine ⟨2796141573911052816394385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864094382607368544262923 2796141573911052816394385)
        ·
          refine ⟨2097106180433289612295789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2796141573911052816394385 2097106180433289612295789)
          ·
            refine ⟨786414817662483604610921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2097106180433289612295789 786414817662483604610921)
            ·
              refine ⟨589811113246862703458191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786414817662483604610921 589811113246862703458191)
              ·
                refine ⟨884716669870294055187287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589811113246862703458191 884716669870294055187287)
                ·
                  refine ⟨1327075004805441082780931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884716669870294055187287 1327075004805441082780931)
                  ·
                    refine ⟨1990612507208161624171397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1327075004805441082780931 1990612507208161624171397)
                    ·
                      refine ⟨373239845101530304532137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1990612507208161624171397 373239845101530304532137)
                      ·
                        rfl

theorem cell23_726882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_726882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726882 prefixEnd_726882 := by exact prefixLift 726882
  have htrace : WordTrace (prefixWord ++ tailWord_726882) baseStart_726882 baseEnd_726882 := by
    simpa [prefixWord, tailWord_726882, baseEnd_726882] using wordTrace_append hprefix tailTrace_726882
  have hstable : (prefixWord ++ tailWord_726882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726882).length < 2 ^ (prefixWord ++ tailWord_726882).sum := by decide
  have hdescent : baseEnd_726882 < baseStart_726882 := by decide
  rcases family_descends (prefixWord ++ tailWord_726882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726941 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_726941 : Nat := 118140960795 + 726941 * 2 ^ 59
def prefixEnd_726941 : Nat := 4983230072969 + 3 ^ 40 * 726941 * 2
def baseEnd_726941 : Nat := 373270140460145573694365

theorem tailTrace_726941 : CollatzResearch.WordTrace tailWord_726941 prefixEnd_726941 373270140460145573694365 := by
  unfold tailWord_726941
  simp only [CollatzResearch.WordTrace]
  refine ⟨26513716459424383483692677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17675810972949588989128451 26513716459424383483692677)
  ·
    refine ⟨4971321836142071903192377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26513716459424383483692677 4971321836142071903192377)
    ·
      refine ⟨3728491377106553927394283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4971321836142071903192377 3728491377106553927394283)
      ·
        refine ⟨5592737065659830891091425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728491377106553927394283 5592737065659830891091425)
        ·
          refine ⟨4194552799244873168318569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5592737065659830891091425 4194552799244873168318569)
          ·
            refine ⟨3145914599433654876238927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4194552799244873168318569 3145914599433654876238927)
            ·
              refine ⟨4718871899150482314358391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145914599433654876238927 4718871899150482314358391)
              ·
                refine ⟨7078307848725723471537587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718871899150482314358391 7078307848725723471537587)
                ·
                  refine ⟨10617461773088585207306381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078307848725723471537587 10617461773088585207306381)
                  ·
                    refine ⟨3981548164908219452739893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10617461773088585207306381 3981548164908219452739893)
                    ·
                      refine ⟨373270140460145573694365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3981548164908219452739893 373270140460145573694365)
                      ·
                        rfl

theorem cell23_726941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_726941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_726941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_726941 prefixEnd_726941 := by exact prefixLift 726941
  have htrace : WordTrace (prefixWord ++ tailWord_726941) baseStart_726941 baseEnd_726941 := by
    simpa [prefixWord, tailWord_726941, baseEnd_726941] using wordTrace_append hprefix tailTrace_726941
  have hstable : (prefixWord ++ tailWord_726941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726941).length < 2 ^ (prefixWord ++ tailWord_726941).sum := by decide
  have hdescent : baseEnd_726941 < baseStart_726941 := by decide
  rcases family_descends (prefixWord ++ tailWord_726941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727045 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 4]
def baseStart_727045 : Nat := 118140960795 + 727045 * 2 ^ 59
def prefixEnd_727045 : Nat := 4983230072969 + 3 ^ 40 * 727045 * 2
def baseEnd_727045 : Nat := 373323542448213166793887

theorem tailTrace_727045 : CollatzResearch.WordTrace tailWord_727045 prefixEnd_727045 373323542448213166793887 := by
  unfold tailWord_727045
  simp only [CollatzResearch.WordTrace]
  refine ⟨26517509651047609245478589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17678339767365072830319059 26517509651047609245478589)
  ·
    refine ⟨9944066119142853467054471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26517509651047609245478589 9944066119142853467054471)
    ·
      refine ⟨14916099178714280200581707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9944066119142853467054471 14916099178714280200581707)
      ·
        refine ⟨22374148768071420300872561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14916099178714280200581707 22374148768071420300872561)
        ·
          refine ⟨16780611576053565225654421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22374148768071420300872561 16780611576053565225654421)
          ·
            refine ⟨786591167627510869952551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16780611576053565225654421 786591167627510869952551)
            ·
              refine ⟨1179886751441266304928827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786591167627510869952551 1179886751441266304928827)
              ·
                refine ⟨1769830127161899457393241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179886751441266304928827 1769830127161899457393241)
                ·
                  refine ⟨1327372595371424593044931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1769830127161899457393241 1327372595371424593044931)
                  ·
                    refine ⟨1991058893057136889567397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1327372595371424593044931 1991058893057136889567397)
                    ·
                      refine ⟨373323542448213166793887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1991058893057136889567397 373323542448213166793887)
                      ·
                        rfl

theorem cell23_727045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_727045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727045 prefixEnd_727045 := by exact prefixLift 727045
  have htrace : WordTrace (prefixWord ++ tailWord_727045) baseStart_727045 baseEnd_727045 := by
    simpa [prefixWord, tailWord_727045, baseEnd_727045] using wordTrace_append hprefix tailTrace_727045
  have hstable : (prefixWord ++ tailWord_727045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727045).length < 2 ^ (prefixWord ++ tailWord_727045).sum := by decide
  have hdescent : baseEnd_727045 < baseStart_727045 := by decide
  rcases family_descends (prefixWord ++ tailWord_727045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727048 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_727048 : Nat := 118140960795 + 727048 * 2 ^ 59
def prefixEnd_727048 : Nat := 4983230072969 + 3 ^ 40 * 727048 * 2
def baseEnd_727048 : Nat := 373325082890176655056373

theorem tailTrace_727048 : CollatzResearch.WordTrace tailWord_727048 prefixEnd_727048 373325082890176655056373 := by
  unfold tailWord_727048
  simp only [CollatzResearch.WordTrace]
  refine ⟨13258809535018370378918899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17678412713357827171891865 13258809535018370378918899)
  ·
    refine ⟨19888214302527555568378349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13258809535018370378918899 19888214302527555568378349)
    ·
      refine ⟨7458080363447833338141881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19888214302527555568378349 7458080363447833338141881)
      ·
        refine ⟨5593560272585875003606411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7458080363447833338141881 5593560272585875003606411)
        ·
          refine ⟨8390340408878812505409617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5593560272585875003606411 8390340408878812505409617)
          ·
            refine ⟨6292755306659109379057213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8390340408878812505409617 6292755306659109379057213)
            ·
              refine ⟨2359783239997166017146455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6292755306659109379057213 2359783239997166017146455)
              ·
                refine ⟨3539674859995749025719683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359783239997166017146455 3539674859995749025719683)
                ·
                  refine ⟨5309512289993623538579525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539674859995749025719683 5309512289993623538579525)
                  ·
                    refine ⟨995533554373804413483661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309512289993623538579525 995533554373804413483661)
                    ·
                      refine ⟨373325082890176655056373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995533554373804413483661 373325082890176655056373)
                      ·
                        rfl

theorem cell23_727048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_727048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727048 prefixEnd_727048 := by exact prefixLift 727048
  have htrace : WordTrace (prefixWord ++ tailWord_727048) baseStart_727048 baseEnd_727048 := by
    simpa [prefixWord, tailWord_727048, baseEnd_727048] using wordTrace_append hprefix tailTrace_727048
  have hstable : (prefixWord ++ tailWord_727048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727048).length < 2 ^ (prefixWord ++ tailWord_727048).sum := by decide
  have hdescent : baseEnd_727048 < baseStart_727048 := by decide
  rcases family_descends (prefixWord ++ tailWord_727048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727051 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 8]
def baseStart_727051 : Nat := 118140960795 + 727051 * 2 ^ 59
def prefixEnd_727051 : Nat := 4983230072969 + 3 ^ 40 * 727051 * 2
def baseEnd_727051 : Nat := 41480735925793349257651

theorem tailTrace_727051 : CollatzResearch.WordTrace tailWord_727051 prefixEnd_727051 41480735925793349257651 := by
  unfold tailWord_727051
  simp only [CollatzResearch.WordTrace]
  refine ⟨26517728489025872270197007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17678485659350581513464671 26517728489025872270197007)
  ·
    refine ⟨39776592733538808405295511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26517728489025872270197007 39776592733538808405295511)
    ·
      refine ⟨59664889100308212607943267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39776592733538808405295511 59664889100308212607943267)
      ·
        refine ⟨89497333650462318911914901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59664889100308212607943267 89497333650462318911914901)
        ·
          refine ⟨4195187514865421198996011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89497333650462318911914901 4195187514865421198996011)
          ·
            refine ⟨6292781272298131798494017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4195187514865421198996011 6292781272298131798494017)
            ·
              refine ⟨4719585954223598848870513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6292781272298131798494017 4719585954223598848870513)
              ·
                refine ⟨3539689465667699136652885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719585954223598848870513 3539689465667699136652885)
                ·
                  refine ⟨41480735925793349257651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3539689465667699136652885 41480735925793349257651)
                  ·
                    rfl

theorem cell23_727051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 8].length) (baseStart_727051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727051 prefixEnd_727051 := by exact prefixLift 727051
  have htrace : WordTrace (prefixWord ++ tailWord_727051) baseStart_727051 baseEnd_727051 := by
    simpa [prefixWord, tailWord_727051, baseEnd_727051] using wordTrace_append hprefix tailTrace_727051
  have hstable : (prefixWord ++ tailWord_727051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727051).length < 2 ^ (prefixWord ++ tailWord_727051).sum := by decide
  have hdescent : baseEnd_727051 < baseStart_727051 := by decide
  rcases family_descends (prefixWord ++ tailWord_727051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727068 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 8]
def baseStart_727068 : Nat := 118140960795 + 727068 * 2 ^ 59
def prefixEnd_727068 : Nat := 4983230072969 + 3 ^ 40 * 727068 * 2
def baseEnd_727068 : Nat := 41481705833696286311809

theorem tailTrace_727068 : CollatzResearch.WordTrace tailWord_727068 prefixEnd_727068 41481705833696286311809 := by
  unfold tailWord_727068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13259174264982142086782929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17678899019976189449043905 13259174264982142086782929)
  ·
    refine ⟨9944380698736606565087197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13259174264982142086782929 9944380698736606565087197)
    ·
      refine ⟨3729142762026227461907699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9944380698736606565087197 3729142762026227461907699)
      ·
        refine ⟨5593714143039341192861549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3729142762026227461907699 5593714143039341192861549)
        ·
          refine ⟨2097642803639752947323081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5593714143039341192861549 2097642803639752947323081)
          ·
            refine ⟨1573232102729814710492311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2097642803639752947323081 1573232102729814710492311)
            ·
              refine ⟨2359848154094722065738467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573232102729814710492311 2359848154094722065738467)
              ·
                refine ⟨3539772231142083098607701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359848154094722065738467 3539772231142083098607701)
                ·
                  refine ⟨41481705833696286311809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3539772231142083098607701 41481705833696286311809)
                  ·
                    rfl

theorem cell23_727068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_727068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727068 prefixEnd_727068 := by exact prefixLift 727068
  have htrace : WordTrace (prefixWord ++ tailWord_727068) baseStart_727068 baseEnd_727068 := by
    simpa [prefixWord, tailWord_727068, baseEnd_727068] using wordTrace_append hprefix tailTrace_727068
  have hstable : (prefixWord ++ tailWord_727068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727068).length < 2 ^ (prefixWord ++ tailWord_727068).sum := by decide
  have hdescent : baseEnd_727068 < baseStart_727068 := by decide
  rcases family_descends (prefixWord ++ tailWord_727068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727071 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_727071 : Nat := 118140960795 + 727071 * 2 ^ 59
def prefixEnd_727071 : Nat := 4983230072969 + 3 ^ 40 * 727071 * 2
def baseEnd_727071 : Nat := 373336892945230065068767

theorem tailTrace_727071 : CollatzResearch.WordTrace tailWord_727071 prefixEnd_727071 373336892945230065068767 := by
  unfold tailWord_727071
  simp only [CollatzResearch.WordTrace]
  refine ⟨26518457948953415685925067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17678971965968943790616711 26518457948953415685925067)
  ·
    refine ⟨39777686923430123528887601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26518457948953415685925067 39777686923430123528887601)
    ·
      refine ⟨29833265192572592646665701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39777686923430123528887601 29833265192572592646665701)
      ·
        refine ⟨5593737223607361121249819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29833265192572592646665701 5593737223607361121249819)
        ·
          refine ⟨8390605835411041681874729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5593737223607361121249819 8390605835411041681874729)
          ·
            refine ⟨6292954376558281261406047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8390605835411041681874729 6292954376558281261406047)
            ·
              refine ⟨9439431564837421892109071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6292954376558281261406047 9439431564837421892109071)
              ·
                refine ⟨14159147347256132838163607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9439431564837421892109071 14159147347256132838163607)
                ·
                  refine ⟨21238721020884199257245411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14159147347256132838163607 21238721020884199257245411)
                  ·
                    refine ⟨31858081531326298885868117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21238721020884199257245411 31858081531326298885868117)
                    ·
                      refine ⟨373336892945230065068767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 31858081531326298885868117 373336892945230065068767)
                      ·
                        rfl

theorem cell23_727071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_727071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727071 prefixEnd_727071 := by exact prefixLift 727071
  have htrace : WordTrace (prefixWord ++ tailWord_727071) baseStart_727071 baseEnd_727071 := by
    simpa [prefixWord, tailWord_727071, baseEnd_727071] using wordTrace_append hprefix tailTrace_727071
  have hstable : (prefixWord ++ tailWord_727071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727071).length < 2 ^ (prefixWord ++ tailWord_727071).sum := by decide
  have hdescent : baseEnd_727071 < baseStart_727071 := by decide
  rcases family_descends (prefixWord ++ tailWord_727071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727091 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 7]
def baseStart_727091 : Nat := 118140960795 + 727091 * 2 ^ 59
def prefixEnd_727091 : Nat := 4983230072969 + 3 ^ 40 * 727091 * 2
def baseEnd_727091 : Nat := 373347162558319986818675

theorem tailTrace_727091 : CollatzResearch.WordTrace tailWord_727091 prefixEnd_727091 373347162558319986818675 := by
  unfold tailWord_727091
  simp only [CollatzResearch.WordTrace]
  refine ⟨26519187408880959101653127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17679458272587306067768751 26519187408880959101653127)
  ·
    refine ⟨39778781113321438652479691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26519187408880959101653127 39778781113321438652479691)
    ·
      refine ⟨59668171669982157978719537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39778781113321438652479691 59668171669982157978719537)
      ·
        refine ⟨44751128752486618484039653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59668171669982157978719537 44751128752486618484039653)
        ·
          refine ⟨8390836641091240965757435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44751128752486618484039653 8390836641091240965757435)
          ·
            refine ⟨12586254961636861448636153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8390836641091240965757435 12586254961636861448636153)
            ·
              refine ⟨9439691221227646086477115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12586254961636861448636153 9439691221227646086477115)
              ·
                refine ⟨14159536831841469129715673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9439691221227646086477115 14159536831841469129715673)
                ·
                  refine ⟨10619652623881101847286755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14159536831841469129715673 10619652623881101847286755)
                  ·
                    refine ⟨15929478935821652770930133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10619652623881101847286755 15929478935821652770930133)
                    ·
                      refine ⟨373347162558319986818675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15929478935821652770930133 373347162558319986818675)
                      ·
                        rfl

theorem cell23_727091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_727091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727091 prefixEnd_727091 := by exact prefixLift 727091
  have htrace : WordTrace (prefixWord ++ tailWord_727091) baseStart_727091 baseEnd_727091 := by
    simpa [prefixWord, tailWord_727091, baseEnd_727091] using wordTrace_append hprefix tailTrace_727091
  have hstable : (prefixWord ++ tailWord_727091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727091).length < 2 ^ (prefixWord ++ tailWord_727091).sum := by decide
  have hdescent : baseEnd_727091 < baseStart_727091 := by decide
  rcases family_descends (prefixWord ++ tailWord_727091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727095 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 3, 1, 3]
def baseStart_727095 : Nat := 118140960795 + 727095 * 2 ^ 59
def prefixEnd_727095 : Nat := 4983230072969 + 3 ^ 40 * 727095 * 2
def baseEnd_727095 : Nat := 373349216480937971168657

theorem tailTrace_727095 : CollatzResearch.WordTrace tailWord_727095 prefixEnd_727095 373349216480937971168657 := by
  unfold tailWord_727095
  simp only [CollatzResearch.WordTrace]
  refine ⟨26519333300866467784798739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17679555533910978523199159 26519333300866467784798739)
  ·
    refine ⟨39778999951299701677198109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26519333300866467784798739 39778999951299701677198109)
    ·
      refine ⟨14917124981737388128949291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39778999951299701677198109 14917124981737388128949291)
      ·
        refine ⟨22375687472606082193423937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14917124981737388128949291 22375687472606082193423937)
        ·
          refine ⟨16781765604454561645067953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22375687472606082193423937 16781765604454561645067953)
          ·
            refine ⟨12586324203340921233800965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16781765604454561645067953 12586324203340921233800965)
            ·
              refine ⟨2359935788126422731337681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12586324203340921233800965 2359935788126422731337681)
              ·
                refine ⟨1769951841094817048503261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2359935788126422731337681 1769951841094817048503261)
                ·
                  refine ⟨663731940410556393188723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1769951841094817048503261 663731940410556393188723)
                  ·
                    refine ⟨995597910615834589783085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 663731940410556393188723 995597910615834589783085)
                    ·
                      refine ⟨373349216480937971168657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995597910615834589783085 373349216480937971168657)
                      ·
                        rfl

theorem cell23_727095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_727095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727095 prefixEnd_727095 := by exact prefixLift 727095
  have htrace : WordTrace (prefixWord ++ tailWord_727095) baseStart_727095 baseEnd_727095 := by
    simpa [prefixWord, tailWord_727095, baseEnd_727095] using wordTrace_append hprefix tailTrace_727095
  have hstable : (prefixWord ++ tailWord_727095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727095).length < 2 ^ (prefixWord ++ tailWord_727095).sum := by decide
  have hdescent : baseEnd_727095 < baseStart_727095 := by decide
  rcases family_descends (prefixWord ++ tailWord_727095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727112 : List Nat := [2, 1, 3, 1, 1, 1, 2, 7, 1, 1, 3]
def baseStart_727112 : Nat := 118140960795 + 727112 * 2 ^ 59
def prefixEnd_727112 : Nat := 4983230072969 + 3 ^ 40 * 727112 * 2
def baseEnd_727112 : Nat := 373357945652064404656079

theorem tailTrace_727112 : CollatzResearch.WordTrace tailWord_727112 prefixEnd_727112 373357945652064404656079 := by
  unfold tailWord_727112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13259976670902439844083795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17679968894536586458778393 13259976670902439844083795)
  ·
    refine ⟨19889965006353659766125693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13259976670902439844083795 19889965006353659766125693)
    ·
      refine ⟨7458736877382622412297135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19889965006353659766125693 7458736877382622412297135)
      ·
        refine ⟨11188105316073933618445703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7458736877382622412297135 11188105316073933618445703)
        ·
          refine ⟨16782157974110900427668555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11188105316073933618445703 16782157974110900427668555)
          ·
            refine ⟨25173236961166350641502833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16782157974110900427668555 25173236961166350641502833)
            ·
              refine ⟨18879927720874762981127125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25173236961166350641502833 18879927720874762981127125)
              ·
                refine ⟨442498305958002257370167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18879927720874762981127125 442498305958002257370167)
                ·
                  refine ⟨663747458937003386055251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442498305958002257370167 663747458937003386055251)
                  ·
                    refine ⟨995621188405505079082877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 663747458937003386055251 995621188405505079082877)
                    ·
                      refine ⟨373357945652064404656079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995621188405505079082877 373357945652064404656079)
                      ·
                        rfl

theorem cell23_727112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_727112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727112 prefixEnd_727112 := by exact prefixLift 727112
  have htrace : WordTrace (prefixWord ++ tailWord_727112) baseStart_727112 baseEnd_727112 := by
    simpa [prefixWord, tailWord_727112, baseEnd_727112] using wordTrace_append hprefix tailTrace_727112
  have hstable : (prefixWord ++ tailWord_727112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727112).length < 2 ^ (prefixWord ++ tailWord_727112).sum := by decide
  have hdescent : baseEnd_727112 < baseStart_727112 := by decide
  rcases family_descends (prefixWord ++ tailWord_727112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727129 : List Nat := [1, 2, 1, 2, 2, 1, 7, 2, 1, 1, 3]
def baseStart_727129 : Nat := 118140960795 + 727129 * 2 ^ 59
def prefixEnd_727129 : Nat := 4983230072969 + 3 ^ 40 * 727129 * 2
def baseEnd_727129 : Nat := 373366674823190838143501

theorem tailTrace_727129 : CollatzResearch.WordTrace tailWord_727129 prefixEnd_727129 373366674823190838143501 := by
  unfold tailWord_727129
  simp only [CollatzResearch.WordTrace]
  refine ⟨26520573382743291591536441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17680382255162194394357627 26520573382743291591536441)
  ·
    refine ⟨19890430037057468693652331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26520573382743291591536441 19890430037057468693652331)
    ·
      refine ⟨29835645055586203040478497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19890430037057468693652331 29835645055586203040478497)
      ·
        refine ⟨22376733791689652280358873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29835645055586203040478497 22376733791689652280358873)
        ·
          refine ⟨16782550343767239210269155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22376733791689652280358873 16782550343767239210269155)
          ·
            refine ⟨25173825515650858815403733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16782550343767239210269155 25173825515650858815403733)
            ·
              refine ⟨590011535523067003486025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25173825515650858815403733 590011535523067003486025)
              ·
                refine ⟨442508651642300252614519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590011535523067003486025 442508651642300252614519)
                ·
                  refine ⟨663762977463450378921779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442508651642300252614519 663762977463450378921779)
                  ·
                    refine ⟨995644466195175568382669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 663762977463450378921779 995644466195175568382669)
                    ·
                      refine ⟨373366674823190838143501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995644466195175568382669 373366674823190838143501)
                      ·
                        rfl

theorem cell23_727129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 1, 1, 3].length) (baseStart_727129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727129 prefixEnd_727129 := by exact prefixLift 727129
  have htrace : WordTrace (prefixWord ++ tailWord_727129) baseStart_727129 baseEnd_727129 := by
    simpa [prefixWord, tailWord_727129, baseEnd_727129] using wordTrace_append hprefix tailTrace_727129
  have hstable : (prefixWord ++ tailWord_727129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727129).length < 2 ^ (prefixWord ++ tailWord_727129).sum := by decide
  have hdescent : baseEnd_727129 < baseStart_727129 := by decide
  rcases family_descends (prefixWord ++ tailWord_727129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727145 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 2, 4]
def baseStart_727145 : Nat := 118140960795 + 727145 * 2 ^ 59
def prefixEnd_727145 : Nat := 4983230072969 + 3 ^ 40 * 727145 * 2
def baseEnd_727145 : Nat := 124458296837887591847809

theorem tailTrace_727145 : CollatzResearch.WordTrace tailWord_727145 prefixEnd_727145 124458296837887591847809 := by
  unfold tailWord_727145
  simp only [CollatzResearch.WordTrace]
  refine ⟨26521156950685326324118889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17680771300456884216079259 26521156950685326324118889)
  ·
    refine ⟨19890867713013994743089167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26521156950685326324118889 19890867713013994743089167)
    ·
      refine ⟨29836301569520992114633751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19890867713013994743089167 29836301569520992114633751)
      ·
        refine ⟨44754452354281488171950627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29836301569520992114633751 44754452354281488171950627)
        ·
          refine ⟨67131678531422232257925941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44754452354281488171950627 67131678531422232257925941)
          ·
            refine ⟨6293594862320834274180557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67131678531422232257925941 6293594862320834274180557)
            ·
              refine ⟨2360098073370312852817709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6293594862320834274180557 2360098073370312852817709)
              ·
                refine ⟨885036777513867319806641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2360098073370312852817709 885036777513867319806641)
                ·
                  refine ⟨663777583135400489854981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 885036777513867319806641 663777583135400489854981)
                  ·
                    refine ⟨124458296837887591847809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 663777583135400489854981 124458296837887591847809)
                    ·
                      rfl

theorem cell23_727145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 4].length) (baseStart_727145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727145 prefixEnd_727145 := by exact prefixLift 727145
  have htrace : WordTrace (prefixWord ++ tailWord_727145) baseStart_727145 baseEnd_727145 := by
    simpa [prefixWord, tailWord_727145, baseEnd_727145] using wordTrace_append hprefix tailTrace_727145
  have hstable : (prefixWord ++ tailWord_727145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727145).length < 2 ^ (prefixWord ++ tailWord_727145).sum := by decide
  have hdescent : baseEnd_727145 < baseStart_727145 := by decide
  rcases family_descends (prefixWord ++ tailWord_727145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727148 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_727148 : Nat := 118140960795 + 727148 * 2 ^ 59
def prefixEnd_727148 : Nat := 4983230072969 + 3 ^ 40 * 727148 * 2
def baseEnd_727148 : Nat := 373376430955626263805913

theorem tailTrace_727148 : CollatzResearch.WordTrace tailWord_727148 prefixEnd_727148 373376430955626263805913 := by
  unfold tailWord_727148
  simp only [CollatzResearch.WordTrace]
  refine ⟨13260633184837228918239049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17680844246449638557652065 13260633184837228918239049)
  ·
    refine ⟨9945474888627921688679287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13260633184837228918239049 9945474888627921688679287)
    ·
      refine ⟨14918212332941882533018931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9945474888627921688679287 14918212332941882533018931)
      ·
        refine ⟨22377318499412823799528397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14918212332941882533018931 22377318499412823799528397)
        ·
          refine ⟨8391494437279808924823149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22377318499412823799528397 8391494437279808924823149)
          ·
            refine ⟨3146810413979928346808681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8391494437279808924823149 3146810413979928346808681)
            ·
              refine ⟨2360107810484946260106511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3146810413979928346808681 2360107810484946260106511)
              ·
                refine ⟨3540161715727419390159767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360107810484946260106511 3540161715727419390159767)
                ·
                  refine ⟨5310242573591129085239651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540161715727419390159767 5310242573591129085239651)
                  ·
                    refine ⟨7965363860386693627859477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5310242573591129085239651 7965363860386693627859477)
                    ·
                      refine ⟨373376430955626263805913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7965363860386693627859477 373376430955626263805913)
                      ·
                        rfl

theorem cell23_727148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_727148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727148 prefixEnd_727148 := by exact prefixLift 727148
  have htrace : WordTrace (prefixWord ++ tailWord_727148) baseStart_727148 baseEnd_727148 := by
    simpa [prefixWord, tailWord_727148, baseEnd_727148] using wordTrace_append hprefix tailTrace_727148
  have hstable : (prefixWord ++ tailWord_727148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727148).length < 2 ^ (prefixWord ++ tailWord_727148).sum := by decide
  have hdescent : baseEnd_727148 < baseStart_727148 := by decide
  rcases family_descends (prefixWord ++ tailWord_727148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727152 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 4]
def baseStart_727152 : Nat := 118140960795 + 727152 * 2 ^ 59
def prefixEnd_727152 : Nat := 4983230072969 + 3 ^ 40 * 727152 * 2
def baseEnd_727152 : Nat := 373378484878244248155895

theorem tailTrace_727152 : CollatzResearch.WordTrace tailWord_727152 prefixEnd_727152 373378484878244248155895 := by
  unfold tailWord_727152
  simp only [CollatzResearch.WordTrace]
  refine ⟨13260706130829983259811855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17680941507773311013082473 13260706130829983259811855)
  ·
    refine ⟨19891059196244974889717783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13260706130829983259811855 19891059196244974889717783)
    ·
      refine ⟨29836588794367462334576675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19891059196244974889717783 29836588794367462334576675)
      ·
        refine ⟨44754883191551193501865013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29836588794367462334576675 44754883191551193501865013)
        ·
          refine ⟨4195770299207924390799845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44754883191551193501865013 4195770299207924390799845)
          ·
            refine ⟨786706931101485823274971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4195770299207924390799845 786706931101485823274971)
            ·
              refine ⟨1180060396652228734912457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786706931101485823274971 1180060396652228734912457)
              ·
                refine ⟨885045297489171551184343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180060396652228734912457 885045297489171551184343)
                ·
                  refine ⟨1327567946233757326776515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885045297489171551184343 1327567946233757326776515)
                  ·
                    refine ⟨1991351919350635990164773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1327567946233757326776515 1991351919350635990164773)
                    ·
                      refine ⟨373378484878244248155895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1991351919350635990164773 373378484878244248155895)
                      ·
                        rfl

theorem cell23_727152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 4].length) (baseStart_727152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727152 prefixEnd_727152 := by exact prefixLift 727152
  have htrace : WordTrace (prefixWord ++ tailWord_727152) baseStart_727152 baseEnd_727152 := by
    simpa [prefixWord, tailWord_727152, baseEnd_727152] using wordTrace_append hprefix tailTrace_727152
  have hstable : (prefixWord ++ tailWord_727152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727152).length < 2 ^ (prefixWord ++ tailWord_727152).sum := by decide
  have hdescent : baseEnd_727152 < baseStart_727152 := by decide
  rcases family_descends (prefixWord ++ tailWord_727152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727165 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_727165 : Nat := 118140960795 + 727165 * 2 ^ 59
def prefixEnd_727165 : Nat := 4983230072969 + 3 ^ 40 * 727165 * 2
def baseEnd_727165 : Nat := 373385160126752697293335

theorem tailTrace_727165 : CollatzResearch.WordTrace tailWord_727165 prefixEnd_727165 373385160126752697293335 := by
  unfold tailWord_727165
  simp only [CollatzResearch.WordTrace]
  refine ⟨26521886410612869739846949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17681257607075246493231299 26521886410612869739846949)
  ·
    refine ⟨4972853701989913076221303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26521886410612869739846949 4972853701989913076221303)
    ·
      refine ⟨7459280552984869614331955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4972853701989913076221303 7459280552984869614331955)
      ·
        refine ⟨11188920829477304421497933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7459280552984869614331955 11188920829477304421497933)
        ·
          refine ⟨4195845311053989158061725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11188920829477304421497933 4195845311053989158061725)
          ·
            refine ⟨1573441991645245934273147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4195845311053989158061725 1573441991645245934273147)
            ·
              refine ⟨2360162987467868901409721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573441991645245934273147 2360162987467868901409721)
              ·
                refine ⟨1770122240600901676057291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2360162987467868901409721 1770122240600901676057291)
                ·
                  refine ⟨2655183360901352514085937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770122240600901676057291 2655183360901352514085937)
                  ·
                    refine ⟨1991387520676014385564453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2655183360901352514085937 1991387520676014385564453)
                    ·
                      refine ⟨373385160126752697293335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1991387520676014385564453 373385160126752697293335)
                      ·
                        rfl

theorem cell23_727165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_727165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727165 prefixEnd_727165 := by exact prefixLift 727165
  have htrace : WordTrace (prefixWord ++ tailWord_727165) baseStart_727165 baseEnd_727165 := by
    simpa [prefixWord, tailWord_727165, baseEnd_727165] using wordTrace_append hprefix tailTrace_727165
  have hstable : (prefixWord ++ tailWord_727165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727165).length < 2 ^ (prefixWord ++ tailWord_727165).sum := by decide
  have hdescent : baseEnd_727165 < baseStart_727165 := by decide
  rcases family_descends (prefixWord ++ tailWord_727165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727169 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_727169 : Nat := 118140960795 + 727169 * 2 ^ 59
def prefixEnd_727169 : Nat := 4983230072969 + 3 ^ 40 * 727169 * 2
def baseEnd_727169 : Nat := 373387214049370681643317

theorem tailTrace_727169 : CollatzResearch.WordTrace tailWord_727169 prefixEnd_727169 373387214049370681643317 := by
  unfold tailWord_727169
  simp only [CollatzResearch.WordTrace]
  refine ⟨26522032302598378422992561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17681354868398918948661707 26522032302598378422992561)
  ·
    refine ⟨19891524226948783817244421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26522032302598378422992561 19891524226948783817244421)
    ·
      refine ⟨3729660792552896965733329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19891524226948783817244421 3729660792552896965733329)
      ·
        refine ⟨2797245594414672724299997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3729660792552896965733329 2797245594414672724299997)
        ·
          refine ⟨1048967097905502271612499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2797245594414672724299997 1048967097905502271612499)
          ·
            refine ⟨1573450646858253407418749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048967097905502271612499 1573450646858253407418749)
            ·
              refine ⟨590043992571845027782031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1573450646858253407418749 590043992571845027782031)
              ·
                refine ⟨885065988857767541673047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590043992571845027782031 885065988857767541673047)
                ·
                  refine ⟨1327598983286651312509571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885065988857767541673047 1327598983286651312509571)
                  ·
                    refine ⟨1991398474929976968764357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1327598983286651312509571 1991398474929976968764357)
                    ·
                      refine ⟨373387214049370681643317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1991398474929976968764357 373387214049370681643317)
                      ·
                        rfl

theorem cell23_727169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_727169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727169 prefixEnd_727169 := by exact prefixLift 727169
  have htrace : WordTrace (prefixWord ++ tailWord_727169) baseStart_727169 baseEnd_727169 := by
    simpa [prefixWord, tailWord_727169, baseEnd_727169] using wordTrace_append hprefix tailTrace_727169
  have hstable : (prefixWord ++ tailWord_727169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727169).length < 2 ^ (prefixWord ++ tailWord_727169).sum := by decide
  have hdescent : baseEnd_727169 < baseStart_727169 := by decide
  rcases family_descends (prefixWord ++ tailWord_727169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727186 : List Nat := [3, 2, 3, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_727186 : Nat := 118140960795 + 727186 * 2 ^ 59
def prefixEnd_727186 : Nat := 4983230072969 + 3 ^ 40 * 727186 * 2
def baseEnd_727186 : Nat := 373395943220497115130739

theorem tailTrace_727186 : CollatzResearch.WordTrace tailWord_727186 prefixEnd_727186 373395943220497115130739 := by
  unfold tailWord_727186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6630663085884197581590353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17681768229024526884240941 6630663085884197581590353)
  ·
    refine ⟨4972997314413148186192765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6630663085884197581590353 4972997314413148186192765)
    ·
      refine ⟨1864873992904930569822287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4972997314413148186192765 1864873992904930569822287)
      ·
        refine ⟨2797310989357395854733431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864873992904930569822287 2797310989357395854733431)
        ·
          refine ⟨4195966484036093782100147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797310989357395854733431 4195966484036093782100147)
          ·
            refine ⟨6293949726054140673150221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4195966484036093782100147 6293949726054140673150221)
            ·
              refine ⟨2360231147270302752431333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6293949726054140673150221 2360231147270302752431333)
              ·
                refine ⟨442543340113181766080875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2360231147270302752431333 442543340113181766080875)
                ·
                  refine ⟨663815010169772649121313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442543340113181766080875 663815010169772649121313)
                  ·
                    refine ⟨497861257627329486840985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 663815010169772649121313 497861257627329486840985)
                    ·
                      refine ⟨373395943220497115130739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497861257627329486840985 373395943220497115130739)
                      ·
                        rfl

theorem cell23_727186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_727186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727186 prefixEnd_727186 := by exact prefixLift 727186
  have htrace : WordTrace (prefixWord ++ tailWord_727186) baseStart_727186 baseEnd_727186 := by
    simpa [prefixWord, tailWord_727186, baseEnd_727186] using wordTrace_append hprefix tailTrace_727186
  have hstable : (prefixWord ++ tailWord_727186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727186).length < 2 ^ (prefixWord ++ tailWord_727186).sum := by decide
  have hdescent : baseEnd_727186 < baseStart_727186 := by decide
  rcases family_descends (prefixWord ++ tailWord_727186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727192 : List Nat := [2, 1, 2, 4, 4, 1, 1, 8]
def baseStart_727192 : Nat := 118140960795 + 727192 * 2 ^ 59
def prefixEnd_727192 : Nat := 4983230072969 + 3 ^ 40 * 727192 * 2
def baseEnd_727192 : Nat := 13829593485349040431693

theorem tailTrace_727192 : CollatzResearch.WordTrace tailWord_727192 prefixEnd_727192 13829593485349040431693 := by
  unfold tailWord_727192
  simp only [CollatzResearch.WordTrace]
  refine ⟨13261435590757526675539915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17681914121010035567386553 13261435590757526675539915)
  ·
    refine ⟨19892153386136290013309873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13261435590757526675539915 19892153386136290013309873)
    ·
      refine ⟨14919115039602217509982405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19892153386136290013309873 14919115039602217509982405)
      ·
        refine ⟨2797334069925415783121701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14919115039602217509982405 2797334069925415783121701)
        ·
          refine ⟨524500138111015459335319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2797334069925415783121701 524500138111015459335319)
          ·
            refine ⟨786750207166523189002979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524500138111015459335319 786750207166523189002979)
            ·
              refine ⟨1180125310749784783504469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786750207166523189002979 1180125310749784783504469)
              ·
                refine ⟨13829593485349040431693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1180125310749784783504469 13829593485349040431693)
                ·
                  rfl

theorem cell23_727192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 8].length) (baseStart_727192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727192 prefixEnd_727192 := by exact prefixLift 727192
  have htrace : WordTrace (prefixWord ++ tailWord_727192) baseStart_727192 baseEnd_727192 := by
    simpa [prefixWord, tailWord_727192, baseEnd_727192] using wordTrace_append hprefix tailTrace_727192
  have hstable : (prefixWord ++ tailWord_727192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727192).length < 2 ^ (prefixWord ++ tailWord_727192).sum := by decide
  have hdescent : baseEnd_727192 < baseStart_727192 := by decide
  rcases family_descends (prefixWord ++ tailWord_727192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727195 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 5, 3, 2]
def baseStart_727195 : Nat := 118140960795 + 727195 * 2 ^ 59
def prefixEnd_727195 : Nat := 4983230072969 + 3 ^ 40 * 727195 * 2
def baseEnd_727195 : Nat := 373400564546387579918197

theorem tailTrace_727195 : CollatzResearch.WordTrace tailWord_727195 prefixEnd_727195 373400564546387579918197 := by
  unfold tailWord_727195
  simp only [CollatzResearch.WordTrace]
  refine ⟨26522980600504184863439039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17681987067002789908959359 26522980600504184863439039)
  ·
    refine ⟨39784470900756277295158559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26522980600504184863439039 39784470900756277295158559)
    ·
      refine ⟨59676706351134415942737839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39784470900756277295158559 59676706351134415942737839)
      ·
        refine ⟨89515059526701623914106759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59676706351134415942737839 89515059526701623914106759)
        ·
          refine ⟨134272589290052435871160139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89515059526701623914106759 134272589290052435871160139)
          ·
            refine ⟨201408883935078653806740209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134272589290052435871160139 201408883935078653806740209)
            ·
              refine ⟨151056662951308990355055157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201408883935078653806740209 151056662951308990355055157)
              ·
                refine ⟨14161562151685217845786421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151056662951308990355055157 14161562151685217845786421)
                ·
                  refine ⟨1327646451720489173042477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14161562151685217845786421 1327646451720489173042477)
                  ·
                    refine ⟨497867419395183439890929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1327646451720489173042477 497867419395183439890929)
                    ·
                      refine ⟨373400564546387579918197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 497867419395183439890929 373400564546387579918197)
                      ·
                        rfl

theorem cell23_727195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 3, 2].length) (baseStart_727195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727195 prefixEnd_727195 := by exact prefixLift 727195
  have htrace : WordTrace (prefixWord ++ tailWord_727195) baseStart_727195 baseEnd_727195 := by
    simpa [prefixWord, tailWord_727195, baseEnd_727195] using wordTrace_append hprefix tailTrace_727195
  have hstable : (prefixWord ++ tailWord_727195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727195).length < 2 ^ (prefixWord ++ tailWord_727195).sum := by decide
  have hdescent : baseEnd_727195 < baseStart_727195 := by decide
  rcases family_descends (prefixWord ++ tailWord_727195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727202 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_727202 : Nat := 118140960795 + 727202 * 2 ^ 59
def prefixEnd_727202 : Nat := 4983230072969 + 3 ^ 40 * 727202 * 2
def baseEnd_727202 : Nat := 373404158910969052530665

theorem tailTrace_727202 : CollatzResearch.WordTrace tailWord_727202 prefixEnd_727202 373404158910969052530665 := by
  unfold tailWord_727202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6630808977869706264735965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17682157274319216705962573 6630808977869706264735965)
  ·
    refine ⟨2486553366701139849275987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6630808977869706264735965 2486553366701139849275987)
    ·
      refine ⟨3729830050051709773913981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2486553366701139849275987 3729830050051709773913981)
      ·
        refine ⟨1398686268769391165217743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3729830050051709773913981 1398686268769391165217743)
        ·
          refine ⟨2098029403154086747826615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398686268769391165217743 2098029403154086747826615)
          ·
            refine ⟨3147044104731130121739923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098029403154086747826615 3147044104731130121739923)
            ·
              refine ⟨4720566157096695182609885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147044104731130121739923 4720566157096695182609885)
              ·
                refine ⟨1770212308911260693478707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4720566157096695182609885 1770212308911260693478707)
                ·
                  refine ⟨2655318463366891040218061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770212308911260693478707 2655318463366891040218061)
                  ·
                    refine ⟨995744423762584140081773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2655318463366891040218061 995744423762584140081773)
                    ·
                      refine ⟨373404158910969052530665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995744423762584140081773 373404158910969052530665)
                      ·
                        rfl

theorem cell23_727202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_727202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727202 prefixEnd_727202 := by exact prefixLift 727202
  have htrace : WordTrace (prefixWord ++ tailWord_727202) baseStart_727202 baseEnd_727202 := by
    simpa [prefixWord, tailWord_727202, baseEnd_727202] using wordTrace_append hprefix tailTrace_727202
  have hstable : (prefixWord ++ tailWord_727202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727202).length < 2 ^ (prefixWord ++ tailWord_727202).sum := by decide
  have hdescent : baseEnd_727202 < baseStart_727202 := by decide
  rcases family_descends (prefixWord ++ tailWord_727202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727218 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_727218 : Nat := 118140960795 + 727218 * 2 ^ 59
def prefixEnd_727218 : Nat := 4983230072969 + 3 ^ 40 * 727218 * 2
def baseEnd_727218 : Nat := 124470791533813663310197

theorem tailTrace_727218 : CollatzResearch.WordTrace tailWord_727218 prefixEnd_727218 124470791533813663310197 := by
  unfold tailWord_727218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6630954869855214947881577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17682546319613906527684205 6630954869855214947881577)
  ·
    refine ⟨4973216152391411210911183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6630954869855214947881577 4973216152391411210911183)
    ·
      refine ⟨7459824228587116816366775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4973216152391411210911183 7459824228587116816366775)
      ·
        refine ⟨11189736342880675224550163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7459824228587116816366775 11189736342880675224550163)
        ·
          refine ⟨16784604514321012836825245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11189736342880675224550163 16784604514321012836825245)
          ·
            refine ⟨6294226692870379813809467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16784604514321012836825245 6294226692870379813809467)
            ·
              refine ⟨9441340039305569720714201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6294226692870379813809467 9441340039305569720714201)
              ·
                refine ⟨7081005029479177290535651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9441340039305569720714201 7081005029479177290535651)
                ·
                  refine ⟨10621507544218765935803477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7081005029479177290535651 10621507544218765935803477)
                  ·
                    refine ⟨124470791533813663310197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10621507544218765935803477 124470791533813663310197)
                    ·
                      rfl

theorem cell23_727218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_727218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727218 prefixEnd_727218 := by exact prefixLift 727218
  have htrace : WordTrace (prefixWord ++ tailWord_727218) baseStart_727218 baseEnd_727218 := by
    simpa [prefixWord, tailWord_727218, baseEnd_727218] using wordTrace_append hprefix tailTrace_727218
  have hstable : (prefixWord ++ tailWord_727218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727218).length < 2 ^ (prefixWord ++ tailWord_727218).sum := by decide
  have hdescent : baseEnd_727218 < baseStart_727218 := by decide
  rcases family_descends (prefixWord ++ tailWord_727218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727220 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_727220 : Nat := 118140960795 + 727220 * 2 ^ 59
def prefixEnd_727220 : Nat := 4983230072969 + 3 ^ 40 * 727220 * 2
def baseEnd_727220 : Nat := 373413401562749982105583

theorem tailTrace_727220 : CollatzResearch.WordTrace tailWord_727220 prefixEnd_727220 373413401562749982105583 := by
  unfold tailWord_727220
  simp only [CollatzResearch.WordTrace]
  refine ⟨13261946212706807066549557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17682594950275742755399409 13261946212706807066549557)
  ·
    refine ⟨1243307457441263162489021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13261946212706807066549557 1243307457441263162489021)
    ·
      refine ⟨466240296540473685933383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1243307457441263162489021 466240296540473685933383)
      ·
        refine ⟨699360444810710528900075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466240296540473685933383 699360444810710528900075)
        ·
          refine ⟨1049040667216065793350113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699360444810710528900075 1049040667216065793350113)
          ·
            refine ⟨786780500412049345012585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1049040667216065793350113 786780500412049345012585)
            ·
              refine ⟨590085375309037008759439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786780500412049345012585 590085375309037008759439)
              ·
                refine ⟨885128062963555513139159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590085375309037008759439 885128062963555513139159)
                ·
                  refine ⟨1327692094445333269708739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885128062963555513139159 1327692094445333269708739)
                  ·
                    refine ⟨1991538141667999904563109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1327692094445333269708739 1991538141667999904563109)
                    ·
                      refine ⟨373413401562749982105583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1991538141667999904563109 373413401562749982105583)
                      ·
                        rfl

theorem cell23_727220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_727220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727220 prefixEnd_727220 := by exact prefixLift 727220
  have htrace : WordTrace (prefixWord ++ tailWord_727220) baseStart_727220 baseEnd_727220 := by
    simpa [prefixWord, tailWord_727220, baseEnd_727220] using wordTrace_append hprefix tailTrace_727220
  have hstable : (prefixWord ++ tailWord_727220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727220).length < 2 ^ (prefixWord ++ tailWord_727220).sum := by decide
  have hdescent : baseEnd_727220 < baseStart_727220 := by decide
  rcases family_descends (prefixWord ++ tailWord_727220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727236 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_727236 : Nat := 118140960795 + 727236 * 2 ^ 59
def prefixEnd_727236 : Nat := 4983230072969 + 3 ^ 40 * 727236 * 2
def baseEnd_727236 : Nat := 373421617253221919505509

theorem tailTrace_727236 : CollatzResearch.WordTrace tailWord_727236 prefixEnd_727236 373421617253221919505509 := by
  unfold tailWord_727236
  simp only [CollatzResearch.WordTrace]
  refine ⟨13262237996677824432840781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17682983995570432577121041 13262237996677824432840781)
  ·
    refine ⟨4973339248754184162315293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13262237996677824432840781 4973339248754184162315293)
    ·
      refine ⟨1865002218282819060868235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4973339248754184162315293 1865002218282819060868235)
      ·
        refine ⟨2797503327424228591302353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865002218282819060868235 2797503327424228591302353)
        ·
          refine ⟨2098127495568171443476765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2797503327424228591302353 2098127495568171443476765)
          ·
            refine ⟨786797810838064291303787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2098127495568171443476765 786797810838064291303787)
            ·
              refine ⟨1180196716257096436955681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786797810838064291303787 1180196716257096436955681)
              ·
                refine ⟨885147537192822327716761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180196716257096436955681 885147537192822327716761)
                ·
                  refine ⟨663860652894616745787571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 885147537192822327716761 663860652894616745787571)
                  ·
                    refine ⟨995790979341925118681357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 663860652894616745787571 995790979341925118681357)
                    ·
                      refine ⟨373421617253221919505509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995790979341925118681357 373421617253221919505509)
                      ·
                        rfl

theorem cell23_727236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_727236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727236 prefixEnd_727236 := by exact prefixLift 727236
  have htrace : WordTrace (prefixWord ++ tailWord_727236) baseStart_727236 baseEnd_727236 := by
    simpa [prefixWord, tailWord_727236, baseEnd_727236] using wordTrace_append hprefix tailTrace_727236
  have hstable : (prefixWord ++ tailWord_727236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727236).length < 2 ^ (prefixWord ++ tailWord_727236).sum := by decide
  have hdescent : baseEnd_727236 < baseStart_727236 := by decide
  rcases family_descends (prefixWord ++ tailWord_727236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727288 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_727288 : Nat := 118140960795 + 727288 * 2 ^ 59
def prefixEnd_727288 : Nat := 4983230072969 + 3 ^ 40 * 727288 * 2
def baseEnd_727288 : Nat := 373448318247255716055269

theorem tailTrace_727288 : CollatzResearch.WordTrace tailWord_727288 prefixEnd_727288 373448318247255716055269 := by
  unfold tailWord_727288
  simp only [CollatzResearch.WordTrace]
  refine ⟨13263186294583630873287259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17684248392778174497716345 13263186294583630873287259)
  ·
    refine ⟨19894779441875446309930889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13263186294583630873287259 19894779441875446309930889)
    ·
      refine ⟨14921084581406584732448167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19894779441875446309930889 14921084581406584732448167)
      ·
        refine ⟨22381626872109877098672251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14921084581406584732448167 22381626872109877098672251)
        ·
          refine ⟨33572440308164815648008377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22381626872109877098672251 33572440308164815648008377)
          ·
            refine ⟨25179330231123611736006283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33572440308164815648008377 25179330231123611736006283)
            ·
              refine ⟨37768995346685417604009425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25179330231123611736006283 37768995346685417604009425)
              ·
                refine ⟨28326746510014063203007069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37768995346685417604009425 28326746510014063203007069)
                ·
                  refine ⟨10622529941255273701127651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28326746510014063203007069 10622529941255273701127651)
                  ·
                    refine ⟨15933794911882910551691477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10622529941255273701127651 15933794911882910551691477)
                    ·
                      refine ⟨373448318247255716055269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15933794911882910551691477 373448318247255716055269)
                      ·
                        rfl

theorem cell23_727288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_727288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727288 prefixEnd_727288 := by exact prefixLift 727288
  have htrace : WordTrace (prefixWord ++ tailWord_727288) baseStart_727288 baseEnd_727288 := by
    simpa [prefixWord, tailWord_727288, baseEnd_727288] using wordTrace_append hprefix tailTrace_727288
  have hstable : (prefixWord ++ tailWord_727288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727288).length < 2 ^ (prefixWord ++ tailWord_727288).sum := by decide
  have hdescent : baseEnd_727288 < baseStart_727288 := by decide
  rcases family_descends (prefixWord ++ tailWord_727288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727295 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 2, 5]
def baseStart_727295 : Nat := 118140960795 + 727295 * 2 ^ 59
def prefixEnd_727295 : Nat := 4983230072969 + 3 ^ 40 * 727295 * 2
def baseEnd_727295 : Nat := 124483970870612396222579

theorem tailTrace_727295 : CollatzResearch.WordTrace tailWord_727295 prefixEnd_727295 124483970870612396222579 := by
  unfold tailWord_727295
  simp only [CollatzResearch.WordTrace]
  refine ⟨26526627900141901942079339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17684418600094601294719559 26526627900141901942079339)
  ·
    refine ⟨39789941850212852913119009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26526627900141901942079339 39789941850212852913119009)
    ·
      refine ⟨29842456387659639684839257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39789941850212852913119009 29842456387659639684839257)
      ·
        refine ⟨22381842290744729763629443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29842456387659639684839257 22381842290744729763629443)
        ·
          refine ⟨33572763436117094645444165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22381842290744729763629443 33572763436117094645444165)
          ·
            refine ⟨6294893144271955246020781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33572763436117094645444165 6294893144271955246020781)
            ·
              refine ⟨2360584929101983217257793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6294893144271955246020781 2360584929101983217257793)
              ·
                refine ⟨1770438696826487412943345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2360584929101983217257793 1770438696826487412943345)
                ·
                  refine ⟨1327829022619865559707509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1770438696826487412943345 1327829022619865559707509)
                  ·
                    refine ⟨124483970870612396222579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1327829022619865559707509 124483970870612396222579)
                    ·
                      rfl

theorem cell23_727295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_727295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727295 prefixEnd_727295 := by exact prefixLift 727295
  have htrace : WordTrace (prefixWord ++ tailWord_727295) baseStart_727295 baseEnd_727295 := by
    simpa [prefixWord, tailWord_727295, baseEnd_727295] using wordTrace_append hprefix tailTrace_727295
  have hstable : (prefixWord ++ tailWord_727295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727295).length < 2 ^ (prefixWord ++ tailWord_727295).sum := by decide
  have hdescent : baseEnd_727295 < baseStart_727295 := by decide
  rcases family_descends (prefixWord ++ tailWord_727295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727305 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 5]
def baseStart_727305 : Nat := 118140960795 + 727305 * 2 ^ 59
def prefixEnd_727305 : Nat := 4983230072969 + 3 ^ 40 * 727305 * 2
def baseEnd_727305 : Nat := 373457047418382149542691

theorem tailTrace_727305 : CollatzResearch.WordTrace tailWord_727305 prefixEnd_727305 373457047418382149542691 := by
  unfold tailWord_727305
  simp only [CollatzResearch.WordTrace]
  refine ⟨26526992630105673649943369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17684661753403782433295579 26526992630105673649943369)
  ·
    refine ⟨19895244472579255237457527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26526992630105673649943369 19895244472579255237457527)
    ·
      refine ⟨29842866708868882856186291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19895244472579255237457527 29842866708868882856186291)
      ·
        refine ⟨44764300063303324284279437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29842866708868882856186291 44764300063303324284279437)
        ·
          refine ⟨16786612523738746606604789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44764300063303324284279437 16786612523738746606604789)
          ·
            refine ⟨1573744924100507494369199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16786612523738746606604789 1573744924100507494369199)
            ·
              refine ⟨2360617386150761241553799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573744924100507494369199 2360617386150761241553799)
              ·
                refine ⟨3540926079226141862330699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360617386150761241553799 3540926079226141862330699)
                ·
                  refine ⟨5311389118839212793496049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540926079226141862330699 5311389118839212793496049)
                  ·
                    refine ⟨3983541839129409595122037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5311389118839212793496049 3983541839129409595122037)
                    ·
                      refine ⟨373457047418382149542691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3983541839129409595122037 373457047418382149542691)
                      ·
                        rfl

theorem cell23_727305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_727305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727305 prefixEnd_727305 := by exact prefixLift 727305
  have htrace : WordTrace (prefixWord ++ tailWord_727305) baseStart_727305 baseEnd_727305 := by
    simpa [prefixWord, tailWord_727305, baseEnd_727305] using wordTrace_append hprefix tailTrace_727305
  have hstable : (prefixWord ++ tailWord_727305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727305).length < 2 ^ (prefixWord ++ tailWord_727305).sum := by decide
  have hdescent : baseEnd_727305 < baseStart_727305 := by decide
  rcases family_descends (prefixWord ++ tailWord_727305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727332 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_727332 : Nat := 118140960795 + 727332 * 2 ^ 59
def prefixEnd_727332 : Nat := 4983230072969 + 3 ^ 40 * 727332 * 2
def baseEnd_727332 : Nat := 373470911396053543905067

theorem tailTrace_727332 : CollatzResearch.WordTrace tailWord_727332 prefixEnd_727332 373470911396053543905067 := by
  unfold tailWord_727332
  simp only [CollatzResearch.WordTrace]
  refine ⟨13263988700503928630588125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17685318267338571507450833 13263988700503928630588125)
  ·
    refine ⟨4973995762688973236470547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13263988700503928630588125 4973995762688973236470547)
    ·
      refine ⟨7460993644033459854705821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4973995762688973236470547 7460993644033459854705821)
      ·
        refine ⟨2797872616512547445514683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7460993644033459854705821 2797872616512547445514683)
        ·
          refine ⟨4196808924768821168272025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797872616512547445514683 4196808924768821168272025)
          ·
            refine ⟨3147606693576615876204019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4196808924768821168272025 3147606693576615876204019)
            ·
              refine ⟨4721410040364923814306029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147606693576615876204019 4721410040364923814306029)
              ·
                refine ⟨1770528765136846430364761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4721410040364923814306029 1770528765136846430364761)
                ·
                  refine ⟨1327896573852634822773571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1770528765136846430364761 1327896573852634822773571)
                  ·
                    refine ⟨1991844860778952234160357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1327896573852634822773571 1991844860778952234160357)
                    ·
                      refine ⟨373470911396053543905067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1991844860778952234160357 373470911396053543905067)
                      ·
                        rfl

theorem cell23_727332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_727332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727332 prefixEnd_727332 := by exact prefixLift 727332
  have htrace : WordTrace (prefixWord ++ tailWord_727332) baseStart_727332 baseEnd_727332 := by
    simpa [prefixWord, tailWord_727332, baseEnd_727332] using wordTrace_append hprefix tailTrace_727332
  have hstable : (prefixWord ++ tailWord_727332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727332).length < 2 ^ (prefixWord ++ tailWord_727332).sum := by decide
  have hdescent : baseEnd_727332 < baseStart_727332 := by decide
  rcases family_descends (prefixWord ++ tailWord_727332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727352 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 2, 2, 3]
def baseStart_727352 : Nat := 118140960795 + 727352 * 2 ^ 59
def prefixEnd_727352 : Nat := 4983230072969 + 3 ^ 40 * 727352 * 2
def baseEnd_727352 : Nat := 373481181009143465654975

theorem tailTrace_727352 : CollatzResearch.WordTrace tailWord_727352 prefixEnd_727352 373481181009143465654975 := by
  unfold tailWord_727352
  simp only [CollatzResearch.WordTrace]
  refine ⟨13264353430467700338452155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17685804573956933784602873 13264353430467700338452155)
  ·
    refine ⟨19896530145701550507678233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13264353430467700338452155 19896530145701550507678233)
    ·
      refine ⟨14922397609276162880758675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19896530145701550507678233 14922397609276162880758675)
      ·
        refine ⟨22383596413914244321138013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14922397609276162880758675 22383596413914244321138013)
        ·
          refine ⟨8393848655217841620426755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22383596413914244321138013 8393848655217841620426755)
          ·
            refine ⟨12590772982826762430640133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393848655217841620426755 12590772982826762430640133)
            ·
              refine ⟨2360769934280017955745025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12590772982826762430640133 2360769934280017955745025)
              ·
                refine ⟨1770577450710013466808769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2360769934280017955745025 1770577450710013466808769)
                ·
                  refine ⟨1327933088032510100106577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1770577450710013466808769 1327933088032510100106577)
                  ·
                    refine ⟨995949816024382575079933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1327933088032510100106577 995949816024382575079933)
                    ·
                      refine ⟨373481181009143465654975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995949816024382575079933 373481181009143465654975)
                      ·
                        rfl

theorem cell23_727352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_727352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727352 prefixEnd_727352 := by exact prefixLift 727352
  have htrace : WordTrace (prefixWord ++ tailWord_727352) baseStart_727352 baseEnd_727352 := by
    simpa [prefixWord, tailWord_727352, baseEnd_727352] using wordTrace_append hprefix tailTrace_727352
  have hstable : (prefixWord ++ tailWord_727352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727352).length < 2 ^ (prefixWord ++ tailWord_727352).sum := by decide
  have hdescent : baseEnd_727352 < baseStart_727352 := by decide
  rcases family_descends (prefixWord ++ tailWord_727352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727359 : List Nat := [1, 1, 2, 2, 4, 1, 3, 4, 1, 4]
def baseStart_727359 : Nat := 118140960795 + 727359 * 2 ^ 59
def prefixEnd_727359 : Nat := 4983230072969 + 3 ^ 40 * 727359 * 2
def baseEnd_727359 : Nat := 124494925124574979422481

theorem tailTrace_727359 : CollatzResearch.WordTrace tailWord_727359 prefixEnd_727359 124494925124574979422481 := by
  unfold tailWord_727359
  simp only [CollatzResearch.WordTrace]
  refine ⟨26528962171910040872409131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17685974781273360581606087 26528962171910040872409131)
  ·
    refine ⟨39793443257865061308613697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26528962171910040872409131 39793443257865061308613697)
    ·
      refine ⟨29845082443398795981460273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39793443257865061308613697 29845082443398795981460273)
      ·
        refine ⟨22383811832549096986095205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29845082443398795981460273 22383811832549096986095205)
        ·
          refine ⟨4196964718602955684892851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22383811832549096986095205 4196964718602955684892851)
          ·
            refine ⟨6295447077904433527339277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4196964718602955684892851 6295447077904433527339277)
            ·
              refine ⟨2360792654214162572752229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6295447077904433527339277 2360792654214162572752229)
              ·
                refine ⟨442648622665155482391043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2360792654214162572752229 442648622665155482391043)
                ·
                  refine ⟨663972933997733223586565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442648622665155482391043 663972933997733223586565)
                  ·
                    refine ⟨124494925124574979422481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 663972933997733223586565 124494925124574979422481)
                    ·
                      rfl

theorem cell23_727359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 1, 4].length) (baseStart_727359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727359 prefixEnd_727359 := by exact prefixLift 727359
  have htrace : WordTrace (prefixWord ++ tailWord_727359) baseStart_727359 baseEnd_727359 := by
    simpa [prefixWord, tailWord_727359, baseEnd_727359] using wordTrace_append hprefix tailTrace_727359
  have hstable : (prefixWord ++ tailWord_727359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727359).length < 2 ^ (prefixWord ++ tailWord_727359).sum := by decide
  have hdescent : baseEnd_727359 < baseStart_727359 := by decide
  rcases family_descends (prefixWord ++ tailWord_727359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727365 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 4, 5, 3]
def baseStart_727365 : Nat := 118140960795 + 727365 * 2 ^ 59
def prefixEnd_727365 : Nat := 4983230072969 + 3 ^ 40 * 727365 * 2
def baseEnd_727365 : Nat := 373487856257651914792415

theorem tailTrace_727365 : CollatzResearch.WordTrace tailWord_727365 prefixEnd_727365 373487856257651914792415 := by
  unfold tailWord_727365
  simp only [CollatzResearch.WordTrace]
  refine ⟨26529181009888303897127549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17686120673258869264751699 26529181009888303897127549)
  ·
    refine ⟨9948442878708113961422831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26529181009888303897127549 9948442878708113961422831)
    ·
      refine ⟨14922664318062170942134247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9948442878708113961422831 14922664318062170942134247)
      ·
        refine ⟨22383996477093256413201371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14922664318062170942134247 22383996477093256413201371)
        ·
          refine ⟨33575994715639884619802057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22383996477093256413201371 33575994715639884619802057)
          ·
            refine ⟨25181996036729913464851543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33575994715639884619802057 25181996036729913464851543)
            ·
              refine ⟨37772994055094870197277315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25181996036729913464851543 37772994055094870197277315)
              ·
                refine ⟨56659491082642305295915973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37772994055094870197277315 56659491082642305295915973)
                ·
                  refine ⟨10623654577995432242984245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56659491082642305295915973 10623654577995432242984245)
                  ·
                    refine ⟨995967616687071772779773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10623654577995432242984245 995967616687071772779773)
                    ·
                      refine ⟨373487856257651914792415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 995967616687071772779773 373487856257651914792415)
                      ·
                        rfl

theorem cell23_727365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_727365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727365 prefixEnd_727365 := by exact prefixLift 727365
  have htrace : WordTrace (prefixWord ++ tailWord_727365) baseStart_727365 baseEnd_727365 := by
    simpa [prefixWord, tailWord_727365, baseEnd_727365] using wordTrace_append hprefix tailTrace_727365
  have hstable : (prefixWord ++ tailWord_727365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727365).length < 2 ^ (prefixWord ++ tailWord_727365).sum := by decide
  have hdescent : baseEnd_727365 < baseStart_727365 := by decide
  rcases family_descends (prefixWord ++ tailWord_727365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727459 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 1, 2, 3]
def baseStart_727459 : Nat := 118140960795 + 727459 * 2 ^ 59
def prefixEnd_727459 : Nat := 4983230072969 + 3 ^ 40 * 727459 * 2
def baseEnd_727459 : Nat := 373536123439174547016983

theorem tailTrace_727459 : CollatzResearch.WordTrace tailWord_727459 prefixEnd_727459 373536123439174547016983 := by
  unfold tailWord_727459
  simp only [CollatzResearch.WordTrace]
  refine ⟨26532609471547757951049431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17688406314365171967366287 26532609471547757951049431)
  ·
    refine ⟨39798914207321636926574147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26532609471547757951049431 39798914207321636926574147)
    ·
      refine ⟨59698371310982455389861221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39798914207321636926574147 59698371310982455389861221)
      ·
        refine ⟨11193444620809210385598979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59698371310982455389861221 11193444620809210385598979)
        ·
          refine ⟨16790166931213815578398469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11193444620809210385598979 16790166931213815578398469)
          ·
            refine ⟨3148156299602590420949713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16790166931213815578398469 3148156299602590420949713)
            ·
              refine ⟨2361117224701942815712285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3148156299602590420949713 2361117224701942815712285)
              ·
                refine ⟨885418959263228555892107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2361117224701942815712285 885418959263228555892107)
                ·
                  refine ⟨1328128438894842833838161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885418959263228555892107 1328128438894842833838161)
                  ·
                    refine ⟨996096329171132125378621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1328128438894842833838161 996096329171132125378621)
                    ·
                      refine ⟨373536123439174547016983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 996096329171132125378621 373536123439174547016983)
                      ·
                        rfl

theorem cell23_727459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_727459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727459 prefixEnd_727459 := by exact prefixLift 727459
  have htrace : WordTrace (prefixWord ++ tailWord_727459) baseStart_727459 baseEnd_727459 := by
    simpa [prefixWord, tailWord_727459, baseEnd_727459] using wordTrace_append hprefix tailTrace_727459
  have hstable : (prefixWord ++ tailWord_727459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727459).length < 2 ^ (prefixWord ++ tailWord_727459).sum := by decide
  have hdescent : baseEnd_727459 < baseStart_727459 := by decide
  rcases family_descends (prefixWord ++ tailWord_727459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727473 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 3, 2, 2]
def baseStart_727473 : Nat := 118140960795 + 727473 * 2 ^ 59
def prefixEnd_727473 : Nat := 4983230072969 + 3 ^ 40 * 727473 * 2
def baseEnd_727473 : Nat := 373543312168337492241919

theorem tailTrace_727473 : CollatzResearch.WordTrace tailWord_727473 prefixEnd_727473 373543312168337492241919 := by
  unfold tailWord_727473
  simp only [CollatzResearch.WordTrace]
  refine ⟨26533120093497038342059073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17688746728998025561372715 26533120093497038342059073)
  ·
    refine ⟨19899840070122778756544305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26533120093497038342059073 19899840070122778756544305)
    ·
      refine ⟨14924880052592084067408229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19899840070122778756544305 14924880052592084067408229)
      ·
        refine ⟨2798415009861015762639043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14924880052592084067408229 2798415009861015762639043)
        ·
          refine ⟨4197622514791523643958565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2798415009861015762639043 4197622514791523643958565)
          ·
            refine ⟨787054221523410683242231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4197622514791523643958565 787054221523410683242231)
            ·
              refine ⟨1180581332285116024863347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787054221523410683242231 1180581332285116024863347)
              ·
                refine ⟨1770871998427674037295021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180581332285116024863347 1770871998427674037295021)
                ·
                  refine ⟨664076999410377763985633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1770871998427674037295021 664076999410377763985633)
                  ·
                    refine ⟨498057749557783322989225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 664076999410377763985633 498057749557783322989225)
                    ·
                      refine ⟨373543312168337492241919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498057749557783322989225 373543312168337492241919)
                      ·
                        rfl

theorem cell23_727473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_727473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727473 prefixEnd_727473 := by exact prefixLift 727473
  have htrace : WordTrace (prefixWord ++ tailWord_727473) baseStart_727473 baseEnd_727473 := by
    simpa [prefixWord, tailWord_727473, baseEnd_727473] using wordTrace_append hprefix tailTrace_727473
  have hstable : (prefixWord ++ tailWord_727473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727473).length < 2 ^ (prefixWord ++ tailWord_727473).sum := by decide
  have hdescent : baseEnd_727473 < baseStart_727473 := by decide
  rcases family_descends (prefixWord ++ tailWord_727473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727523 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 2, 1, 3]
def baseStart_727523 : Nat := 118140960795 + 727523 * 2 ^ 59
def prefixEnd_727523 : Nat := 4983230072969 + 3 ^ 40 * 727523 * 2
def baseEnd_727523 : Nat := 373568986201062296616689

theorem tailTrace_727523 : CollatzResearch.WordTrace tailWord_727523 prefixEnd_727523 373568986201062296616689 := by
  unfold tailWord_727523
  simp only [CollatzResearch.WordTrace]
  refine ⟨26534943743315896881379223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17689962495543931254252815 26534943743315896881379223)
  ·
    refine ⟨39802415614973845322068835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26534943743315896881379223 39802415614973845322068835)
    ·
      refine ⟨59703623422460767983103253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39802415614973845322068835 59703623422460767983103253)
      ·
        refine ⟨2798607347927848499207965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59703623422460767983103253 2798607347927848499207965)
        ·
          refine ⟨1049477755472943187202987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2798607347927848499207965 1049477755472943187202987)
          ·
            refine ⟨1574216633209414780804481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049477755472943187202987 1574216633209414780804481)
            ·
              refine ⟨1180662474907061085603361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1574216633209414780804481 1180662474907061085603361)
              ·
                refine ⟨885496856180295814202521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180662474907061085603361 885496856180295814202521)
                ·
                  refine ⟨664122642135221860651891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 885496856180295814202521 664122642135221860651891)
                  ·
                    refine ⟨996183963202832790977837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 664122642135221860651891 996183963202832790977837)
                    ·
                      refine ⟨373568986201062296616689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 996183963202832790977837 373568986201062296616689)
                      ·
                        rfl

theorem cell23_727523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_727523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727523 prefixEnd_727523 := by exact prefixLift 727523
  have htrace : WordTrace (prefixWord ++ tailWord_727523) baseStart_727523 baseEnd_727523 := by
    simpa [prefixWord, tailWord_727523, baseEnd_727523] using wordTrace_append hprefix tailTrace_727523
  have hstable : (prefixWord ++ tailWord_727523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727523).length < 2 ^ (prefixWord ++ tailWord_727523).sum := by decide
  have hdescent : baseEnd_727523 < baseStart_727523 := by decide
  rcases family_descends (prefixWord ++ tailWord_727523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727532 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 3]
def baseStart_727532 : Nat := 118140960795 + 727532 * 2 ^ 59
def prefixEnd_727532 : Nat := 4983230072969 + 3 ^ 40 * 727532 * 2
def baseEnd_727532 : Nat := 373573607526952761404147

theorem tailTrace_727532 : CollatzResearch.WordTrace tailWord_727532 prefixEnd_727532 373573607526952761404147 := by
  unfold tailWord_727532
  simp only [CollatzResearch.WordTrace]
  refine ⟨13267636000141645709228425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17690181333522194278971233 13267636000141645709228425)
  ·
    refine ⟨9950727000106234281921319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13267636000141645709228425 9950727000106234281921319)
    ·
      refine ⟨14926090500159351422881979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9950727000106234281921319 14926090500159351422881979)
      ·
        refine ⟨22389135750239027134322969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14926090500159351422881979 22389135750239027134322969)
        ·
          refine ⟨16791851812679270350742227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22389135750239027134322969 16791851812679270350742227)
          ·
            refine ⟨25187777719018905526113341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16791851812679270350742227 25187777719018905526113341)
            ·
              refine ⟨9445416644632089572292503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25187777719018905526113341 9445416644632089572292503)
              ·
                refine ⟨14168124966948134358438755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9445416644632089572292503 14168124966948134358438755)
                ·
                  refine ⟨21252187450422201537658133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14168124966948134358438755 21252187450422201537658133)
                  ·
                    refine ⟨996196286738540697077725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21252187450422201537658133 996196286738540697077725)
                    ·
                      refine ⟨373573607526952761404147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 996196286738540697077725 373573607526952761404147)
                      ·
                        rfl

theorem cell23_727532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_727532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727532 prefixEnd_727532 := by exact prefixLift 727532
  have htrace : WordTrace (prefixWord ++ tailWord_727532) baseStart_727532 baseEnd_727532 := by
    simpa [prefixWord, tailWord_727532, baseEnd_727532] using wordTrace_append hprefix tailTrace_727532
  have hstable : (prefixWord ++ tailWord_727532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727532).length < 2 ^ (prefixWord ++ tailWord_727532).sum := by decide
  have hdescent : baseEnd_727532 < baseStart_727532 := by decide
  rcases family_descends (prefixWord ++ tailWord_727532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727580 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_727580 : Nat := 118140960795 + 727580 * 2 ^ 59
def prefixEnd_727580 : Nat := 4983230072969 + 3 ^ 40 * 727580 * 2
def baseEnd_727580 : Nat := 373598254598368573603927

theorem tailTrace_727580 : CollatzResearch.WordTrace tailWord_727580 prefixEnd_727580 373598254598368573603927 := by
  unfold tailWord_727580
  simp only [CollatzResearch.WordTrace]
  refine ⟨13268511352054697808102097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17691348469406263744136129 13268511352054697808102097)
  ·
    refine ⟨9951383514041023356076573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13268511352054697808102097 9951383514041023356076573)
    ·
      refine ⟨3731768817765383758528715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9951383514041023356076573 3731768817765383758528715)
      ·
        refine ⟨5597653226648075637793073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3731768817765383758528715 5597653226648075637793073)
        ·
          refine ⟨4198239919986056728344805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5597653226648075637793073 4198239919986056728344805)
          ·
            refine ⟨787169984997385636564651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4198239919986056728344805 787169984997385636564651)
            ·
              refine ⟨1180754977496078454846977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787169984997385636564651 1180754977496078454846977)
              ·
                refine ⟨885566233122058841135233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180754977496078454846977 885566233122058841135233)
                ·
                  refine ⟨664174674841544130851425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 885566233122058841135233 664174674841544130851425)
                  ·
                    refine ⟨498131006131158098138569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 664174674841544130851425 498131006131158098138569)
                    ·
                      refine ⟨373598254598368573603927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498131006131158098138569 373598254598368573603927)
                      ·
                        rfl

theorem cell23_727580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_727580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727580 prefixEnd_727580 := by exact prefixLift 727580
  have htrace : WordTrace (prefixWord ++ tailWord_727580) baseStart_727580 baseEnd_727580 := by
    simpa [prefixWord, tailWord_727580, baseEnd_727580] using wordTrace_append hprefix tailTrace_727580
  have hstable : (prefixWord ++ tailWord_727580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727580).length < 2 ^ (prefixWord ++ tailWord_727580).sum := by decide
  have hdescent : baseEnd_727580 < baseStart_727580 := by decide
  rcases family_descends (prefixWord ++ tailWord_727580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727589 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 1, 7, 2]
def baseStart_727589 : Nat := 118140960795 + 727589 * 2 ^ 59
def prefixEnd_727589 : Nat := 4983230072969 + 3 ^ 40 * 727589 * 2
def baseEnd_727589 : Nat := 373602875924259038391385

theorem tailTrace_727589 : CollatzResearch.WordTrace tailWord_727589 prefixEnd_727589 373602875924259038391385 := by
  unfold tailWord_727589
  simp only [CollatzResearch.WordTrace]
  refine ⟨26537350961076790153281821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17691567307384526768854547 26537350961076790153281821)
  ·
    refine ⟨9951506610403796307480683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26537350961076790153281821 9951506610403796307480683)
    ·
      refine ⟨14927259915605694461221025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9951506610403796307480683 14927259915605694461221025)
      ·
        refine ⟨11195444936704270845915769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14927259915605694461221025 11195444936704270845915769)
        ·
          refine ⟨8396583702528203134436827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11195444936704270845915769 8396583702528203134436827)
          ·
            refine ⟨12594875553792304701655241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8396583702528203134436827 12594875553792304701655241)
            ·
              refine ⟨9446156665344228526241431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12594875553792304701655241 9446156665344228526241431)
              ·
                refine ⟨14169234998016342789362147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9446156665344228526241431 14169234998016342789362147)
                ·
                  refine ⟨21253852497024514184043221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14169234998016342789362147 21253852497024514184043221)
                  ·
                    refine ⟨498137167899012051188513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21253852497024514184043221 498137167899012051188513)
                    ·
                      refine ⟨373602875924259038391385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498137167899012051188513 373602875924259038391385)
                      ·
                        rfl

theorem cell23_727589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_727589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727589 prefixEnd_727589 := by exact prefixLift 727589
  have htrace : WordTrace (prefixWord ++ tailWord_727589) baseStart_727589 baseEnd_727589 := by
    simpa [prefixWord, tailWord_727589, baseEnd_727589] using wordTrace_append hprefix tailTrace_727589
  have hstable : (prefixWord ++ tailWord_727589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727589).length < 2 ^ (prefixWord ++ tailWord_727589).sum := by decide
  have hdescent : baseEnd_727589 < baseStart_727589 := by decide
  rcases family_descends (prefixWord ++ tailWord_727589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727619 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 1, 6, 2]
def baseStart_727619 : Nat := 118140960795 + 727619 * 2 ^ 59
def prefixEnd_727619 : Nat := 4983230072969 + 3 ^ 40 * 727619 * 2
def baseEnd_727619 : Nat := 373618280343893921016247

theorem tailTrace_727619 : CollatzResearch.WordTrace tailWord_727619 prefixEnd_727619 373618280343893921016247 := by
  unfold tailWord_727619
  simp only [CollatzResearch.WordTrace]
  refine ⟨26538445150968105276873911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17692296767312070184582607 26538445150968105276873911)
  ·
    refine ⟨39807667726452157915310867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26538445150968105276873911 39807667726452157915310867)
    ·
      refine ⟨59711501589678236872966301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39807667726452157915310867 59711501589678236872966301)
      ·
        refine ⟨22391813096129338827362363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59711501589678236872966301 22391813096129338827362363)
        ·
          refine ⟨33587719644194008241043545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22391813096129338827362363 33587719644194008241043545)
          ·
            refine ⟨25190789733145506180782659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33587719644194008241043545 25190789733145506180782659)
            ·
              refine ⟨37786184599718259271173989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25190789733145506180782659 37786184599718259271173989)
              ·
                refine ⟨7084909612447173613345123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37786184599718259271173989 7084909612447173613345123)
                ·
                  refine ⟨10627364418670760420017685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7084909612447173613345123 10627364418670760420017685)
                  ·
                    refine ⟨498157707125191894688329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10627364418670760420017685 498157707125191894688329)
                    ·
                      refine ⟨373618280343893921016247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498157707125191894688329 373618280343893921016247)
                      ·
                        rfl

theorem cell23_727619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_727619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727619 prefixEnd_727619 := by exact prefixLift 727619
  have htrace : WordTrace (prefixWord ++ tailWord_727619) baseStart_727619 baseEnd_727619 := by
    simpa [prefixWord, tailWord_727619, baseEnd_727619] using wordTrace_append hprefix tailTrace_727619
  have hstable : (prefixWord ++ tailWord_727619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727619).length < 2 ^ (prefixWord ++ tailWord_727619).sum := by decide
  have hdescent : baseEnd_727619 < baseStart_727619 := by decide
  rcases family_descends (prefixWord ++ tailWord_727619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727632 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_727632 : Nat := 118140960795 + 727632 * 2 ^ 59
def prefixEnd_727632 : Nat := 4983230072969 + 3 ^ 40 * 727632 * 2
def baseEnd_727632 : Nat := 373624955592402370153687

theorem tailTrace_727632 : CollatzResearch.WordTrace tailWord_727632 prefixEnd_727632 373624955592402370153687 := by
  unfold tailWord_727632
  simp only [CollatzResearch.WordTrace]
  refine ⟨13269459649960504248548575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17692612866614005664731433 13269459649960504248548575)
  ·
    refine ⟨19904189474940756372822863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13269459649960504248548575 19904189474940756372822863)
    ·
      refine ⟨29856284212411134559234295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19904189474940756372822863 29856284212411134559234295)
      ·
        refine ⟨44784426318616701838851443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29856284212411134559234295 44784426318616701838851443)
        ·
          refine ⟨67176639477925052758277165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44784426318616701838851443 67176639477925052758277165)
          ·
            refine ⟨25191239804221894784353937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67176639477925052758277165 25191239804221894784353937)
            ·
              refine ⟨18893429853166421088265453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25191239804221894784353937 18893429853166421088265453)
              ·
                refine ⟨7085036194937407908099545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18893429853166421088265453 7085036194937407908099545)
                ·
                  refine ⟨5313777146203055931074659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7085036194937407908099545 5313777146203055931074659)
                  ·
                    refine ⟨7970665719304583896611989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5313777146203055931074659 7970665719304583896611989)
                    ·
                      refine ⟨373624955592402370153687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7970665719304583896611989 373624955592402370153687)
                      ·
                        rfl

theorem cell23_727632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_727632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727632 prefixEnd_727632 := by exact prefixLift 727632
  have htrace : WordTrace (prefixWord ++ tailWord_727632) baseStart_727632 baseEnd_727632 := by
    simpa [prefixWord, tailWord_727632, baseEnd_727632] using wordTrace_append hprefix tailTrace_727632
  have hstable : (prefixWord ++ tailWord_727632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727632).length < 2 ^ (prefixWord ++ tailWord_727632).sum := by decide
  have hdescent : baseEnd_727632 < baseStart_727632 := by decide
  rcases family_descends (prefixWord ++ tailWord_727632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727636 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_727636 : Nat := 118140960795 + 727636 * 2 ^ 59
def prefixEnd_727636 : Nat := 4983230072969 + 3 ^ 40 * 727636 * 2
def baseEnd_727636 : Nat := 373627009515020354503669

theorem tailTrace_727636 : CollatzResearch.WordTrace tailWord_727636 prefixEnd_727636 373627009515020354503669 := by
  unfold tailWord_727636
  simp only [CollatzResearch.WordTrace]
  refine ⟨13269532595953258590121381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17692710127937678120161841 13269532595953258590121381)
  ·
    refine ⟨2488037361741235985647759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13269532595953258590121381 2488037361741235985647759)
    ·
      refine ⟨3732056042611853978471639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2488037361741235985647759 3732056042611853978471639)
      ·
        refine ⟨5598084063917780967707459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3732056042611853978471639 5598084063917780967707459)
        ·
          refine ⟨8397126095876671451561189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598084063917780967707459 8397126095876671451561189)
          ·
            refine ⟨1574461142976875897167723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8397126095876671451561189 1574461142976875897167723)
            ·
              refine ⟨2361691714465313845751585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574461142976875897167723 2361691714465313845751585)
              ·
                refine ⟨1771268785848985384313689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2361691714465313845751585 1771268785848985384313689)
                ·
                  refine ⟨1328451589386739038235267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1771268785848985384313689 1328451589386739038235267)
                  ·
                    refine ⟨1992677384080108557352901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1328451589386739038235267 1992677384080108557352901)
                    ·
                      refine ⟨373627009515020354503669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1992677384080108557352901 373627009515020354503669)
                      ·
                        rfl

theorem cell23_727636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_727636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727636 prefixEnd_727636 := by exact prefixLift 727636
  have htrace : WordTrace (prefixWord ++ tailWord_727636) baseStart_727636 baseEnd_727636 := by
    simpa [prefixWord, tailWord_727636, baseEnd_727636] using wordTrace_append hprefix tailTrace_727636
  have hstable : (prefixWord ++ tailWord_727636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727636).length < 2 ^ (prefixWord ++ tailWord_727636).sum := by decide
  have hdescent : baseEnd_727636 < baseStart_727636 := by decide
  rcases family_descends (prefixWord ++ tailWord_727636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727672 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 2, 9]
def baseStart_727672 : Nat := 118140960795 + 727672 * 2 ^ 59
def prefixEnd_727672 : Nat := 4983230072969 + 3 ^ 40 * 727672 * 2
def baseEnd_727672 : Nat := 124548498272860737884501

theorem tailTrace_727672 : CollatzResearch.WordTrace tailWord_727672 prefixEnd_727672 124548498272860737884501 := by
  unfold tailWord_727672
  simp only [CollatzResearch.WordTrace]
  refine ⟨13270189109888047664276635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17693585479850730219035513 13270189109888047664276635)
  ·
    refine ⟨19905283664832071496414953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13270189109888047664276635 19905283664832071496414953)
    ·
      refine ⟨14928962748624053622311215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19905283664832071496414953 14928962748624053622311215)
      ·
        refine ⟨22393444122936080433466823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14928962748624053622311215 22393444122936080433466823)
        ·
          refine ⟨33590166184404120650200235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22393444122936080433466823 33590166184404120650200235)
          ·
            refine ⟨50385249276606180975300353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33590166184404120650200235 50385249276606180975300353)
            ·
              refine ⟨37788936957454635731475265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50385249276606180975300353 37788936957454635731475265)
              ·
                refine ⟨28341702718090976798606449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37788936957454635731475265 28341702718090976798606449)
                ·
                  refine ⟨21256277038568232598954837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28341702718090976798606449 21256277038568232598954837)
                  ·
                    refine ⟨124548498272860737884501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 21256277038568232598954837 124548498272860737884501)
                    ·
                      rfl

theorem cell23_727672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_727672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727672 prefixEnd_727672 := by exact prefixLift 727672
  have htrace : WordTrace (prefixWord ++ tailWord_727672) baseStart_727672 baseEnd_727672 := by
    simpa [prefixWord, tailWord_727672, baseEnd_727672] using wordTrace_append hprefix tailTrace_727672
  have hstable : (prefixWord ++ tailWord_727672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727672).length < 2 ^ (prefixWord ++ tailWord_727672).sum := by decide
  have hdescent : baseEnd_727672 < baseStart_727672 := by decide
  rcases family_descends (prefixWord ++ tailWord_727672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727743 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 1, 1, 4]
def baseStart_727743 : Nat := 118140960795 + 727743 * 2 ^ 59
def prefixEnd_727743 : Nat := 4983230072969 + 3 ^ 40 * 727743 * 2
def baseEnd_727743 : Nat := 373681951945051435865677

theorem tailTrace_727743 : CollatzResearch.WordTrace tailWord_727743 prefixEnd_727743 373681951945051435865677 := by
  unfold tailWord_727743
  simp only [CollatzResearch.WordTrace]
  refine ⟨26542967802518874454387883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17695311868345916302925255 26542967802518874454387883)
  ·
    refine ⟨39814451703778311681581825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26542967802518874454387883 39814451703778311681581825)
    ·
      refine ⟨29860838777833733761186369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39814451703778311681581825 29860838777833733761186369)
      ·
        refine ⟨22395629083375300320889777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29860838777833733761186369 22395629083375300320889777)
        ·
          refine ⟨16796721812531475240667333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22395629083375300320889777 16796721812531475240667333)
          ·
            refine ⟨3149385339849651607625125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16796721812531475240667333 3149385339849651607625125)
            ·
              refine ⟨590509751221809676429711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3149385339849651607625125 590509751221809676429711)
              ·
                refine ⟨885764626832714514644567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590509751221809676429711 885764626832714514644567)
                ·
                  refine ⟨1328646940249071771966851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885764626832714514644567 1328646940249071771966851)
                  ·
                    refine ⟨1992970410373607657950277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1328646940249071771966851 1992970410373607657950277)
                    ·
                      refine ⟨373681951945051435865677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1992970410373607657950277 373681951945051435865677)
                      ·
                        rfl

theorem cell23_727743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_727743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727743 prefixEnd_727743 := by exact prefixLift 727743
  have htrace : WordTrace (prefixWord ++ tailWord_727743) baseStart_727743 baseEnd_727743 := by
    simpa [prefixWord, tailWord_727743, baseEnd_727743] using wordTrace_append hprefix tailTrace_727743
  have hstable : (prefixWord ++ tailWord_727743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727743).length < 2 ^ (prefixWord ++ tailWord_727743).sum := by decide
  have hdescent : baseEnd_727743 < baseStart_727743 := by decide
  rcases family_descends (prefixWord ++ tailWord_727743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727759 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 3]
def baseStart_727759 : Nat := 118140960795 + 727759 * 2 ^ 59
def prefixEnd_727759 : Nat := 4983230072969 + 3 ^ 40 * 727759 * 2
def baseEnd_727759 : Nat := 373690167635523373265603

theorem tailTrace_727759 : CollatzResearch.WordTrace tailWord_727759 prefixEnd_727759 373690167635523373265603 := by
  unfold tailWord_727759
  simp only [CollatzResearch.WordTrace]
  refine ⟨26543551370460909186970331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17695700913640606124646887 26543551370460909186970331)
  ·
    refine ⟨39815327055691363780455497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26543551370460909186970331 39815327055691363780455497)
    ·
      refine ⟨29861495291768522835341623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39815327055691363780455497 29861495291768522835341623)
      ·
        refine ⟨44792242937652784253012435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29861495291768522835341623 44792242937652784253012435)
        ·
          refine ⟨67188364406479176379518653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44792242937652784253012435 67188364406479176379518653)
          ·
            refine ⟨25195636652429691142319495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67188364406479176379518653 25195636652429691142319495)
            ·
              refine ⟨37793454978644536713479243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25195636652429691142319495 37793454978644536713479243)
              ·
                refine ⟨56690182467966805070218865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37793454978644536713479243 56690182467966805070218865)
                ·
                  refine ⟨42517636850975103802664149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56690182467966805070218865 42517636850975103802664149)
                  ·
                    refine ⟨996507113694728995374941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42517636850975103802664149 996507113694728995374941)
                    ·
                      refine ⟨373690167635523373265603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 996507113694728995374941 373690167635523373265603)
                      ·
                        rfl

theorem cell23_727759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 3].length) (baseStart_727759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727759 prefixEnd_727759 := by exact prefixLift 727759
  have htrace : WordTrace (prefixWord ++ tailWord_727759) baseStart_727759 baseEnd_727759 := by
    simpa [prefixWord, tailWord_727759, baseEnd_727759] using wordTrace_append hprefix tailTrace_727759
  have hstable : (prefixWord ++ tailWord_727759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727759).length < 2 ^ (prefixWord ++ tailWord_727759).sum := by decide
  have hdescent : baseEnd_727759 < baseStart_727759 := by decide
  rcases family_descends (prefixWord ++ tailWord_727759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727794 : List Nat := [3, 2, 1, 3, 1, 4, 1, 3, 1, 2, 2]
def baseStart_727794 : Nat := 118140960795 + 727794 * 2 ^ 59
def prefixEnd_727794 : Nat := 4983230072969 + 3 ^ 40 * 727794 * 2
def baseEnd_727794 : Nat := 373708139458430736327943

theorem tailTrace_727794 : CollatzResearch.WordTrace tailWord_727794 prefixEnd_727794 373708139458430736327943 := by
  unfold tailWord_727794
  simp only [CollatzResearch.WordTrace]
  refine ⟨6636206981333527541123609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17696551950222740109662957 6636206981333527541123609)
  ·
    refine ⟨4977155236000145655842707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6636206981333527541123609 4977155236000145655842707)
    ·
      refine ⟨7465732854000218483764061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4977155236000145655842707 7465732854000218483764061)
      ·
        refine ⟨2799649820250081931411523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7465732854000218483764061 2799649820250081931411523)
        ·
          refine ⟨4199474730375122897117285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799649820250081931411523 4199474730375122897117285)
          ·
            refine ⟨787401511945335543209491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4199474730375122897117285 787401511945335543209491)
            ·
              refine ⟨1181102267918003314814237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787401511945335543209491 1181102267918003314814237)
              ·
                refine ⟨442913350469251243055339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1181102267918003314814237 442913350469251243055339)
                ·
                  refine ⟨664370025703876864583009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442913350469251243055339 664370025703876864583009)
                  ·
                    refine ⟨498277519277907648437257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 664370025703876864583009 498277519277907648437257)
                    ·
                      refine ⟨373708139458430736327943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498277519277907648437257 373708139458430736327943)
                      ·
                        rfl

theorem cell23_727794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_727794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727794 prefixEnd_727794 := by exact prefixLift 727794
  have htrace : WordTrace (prefixWord ++ tailWord_727794) baseStart_727794 baseEnd_727794 := by
    simpa [prefixWord, tailWord_727794, baseEnd_727794] using wordTrace_append hprefix tailTrace_727794
  have hstable : (prefixWord ++ tailWord_727794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727794).length < 2 ^ (prefixWord ++ tailWord_727794).sum := by decide
  have hdescent : baseEnd_727794 < baseStart_727794 := by decide
  rcases family_descends (prefixWord ++ tailWord_727794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727797 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_727797 : Nat := 118140960795 + 727797 * 2 ^ 59
def prefixEnd_727797 : Nat := 4983230072969 + 3 ^ 40 * 727797 * 2
def baseEnd_727797 : Nat := 373709679900394224590429

theorem tailTrace_727797 : CollatzResearch.WordTrace tailWord_727797 prefixEnd_727797 373709679900394224590429 := by
  unfold tailWord_727797
  simp only [CollatzResearch.WordTrace]
  refine ⟨26544937344323241676853645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17696624896215494451235763 26544937344323241676853645)
  ·
    refine ⟨9954351504121215628820117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26544937344323241676853645 9954351504121215628820117)
    ·
      refine ⟨466610226755681982600943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9954351504121215628820117 466610226755681982600943)
      ·
        refine ⟨699915340133522973901415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466610226755681982600943 699915340133522973901415)
        ·
          refine ⟨1049873010200284460852123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699915340133522973901415 1049873010200284460852123)
          ·
            refine ⟨1574809515300426691278185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049873010200284460852123 1574809515300426691278185)
            ·
              refine ⟨1181107136475320018458639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1574809515300426691278185 1181107136475320018458639)
              ·
                refine ⟨1771660704712980027687959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181107136475320018458639 1771660704712980027687959)
                ·
                  refine ⟨2657491057069470041531939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771660704712980027687959 2657491057069470041531939)
                  ·
                    refine ⟨3986236585604205062297909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2657491057069470041531939 3986236585604205062297909)
                    ·
                      refine ⟨373709679900394224590429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3986236585604205062297909 373709679900394224590429)
                      ·
                        rfl

theorem cell23_727797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_727797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727797 prefixEnd_727797 := by exact prefixLift 727797
  have htrace : WordTrace (prefixWord ++ tailWord_727797) baseStart_727797 baseEnd_727797 := by
    simpa [prefixWord, tailWord_727797, baseEnd_727797] using wordTrace_append hprefix tailTrace_727797
  have hstable : (prefixWord ++ tailWord_727797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727797).length < 2 ^ (prefixWord ++ tailWord_727797).sum := by decide
  have hdescent : baseEnd_727797 < baseStart_727797 := by decide
  rcases family_descends (prefixWord ++ tailWord_727797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727799 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_727799 : Nat := 118140960795 + 727799 * 2 ^ 59
def prefixEnd_727799 : Nat := 4983230072969 + 3 ^ 40 * 727799 * 2
def baseEnd_727799 : Nat := 373710706861703216765419

theorem tailTrace_727799 : CollatzResearch.WordTrace tailWord_727799 prefixEnd_727799 373710706861703216765419 := by
  unfold tailWord_727799
  simp only [CollatzResearch.WordTrace]
  refine ⟨26545010290315996018426451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17696673526877330678950967 26545010290315996018426451)
  ·
    refine ⟨39817515435473994027639677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26545010290315996018426451 39817515435473994027639677)
    ·
      refine ⟨14931568288302747760364879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39817515435473994027639677 14931568288302747760364879)
      ·
        refine ⟨22397352432454121640547319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14931568288302747760364879 22397352432454121640547319)
        ·
          refine ⟨33596028648681182460820979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22397352432454121640547319 33596028648681182460820979)
          ·
            refine ⟨50394042973021773691231469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33596028648681182460820979 50394042973021773691231469)
            ·
              refine ⟨18897766114883165134211801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50394042973021773691231469 18897766114883165134211801)
              ·
                refine ⟨14173324586162373850658851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18897766114883165134211801 14173324586162373850658851)
                ·
                  refine ⟨21259986879243560775988277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14173324586162373850658851 21259986879243560775988277)
                  ·
                    refine ⟨1993123769929083822748901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21259986879243560775988277 1993123769929083822748901)
                    ·
                      refine ⟨373710706861703216765419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1993123769929083822748901 373710706861703216765419)
                      ·
                        rfl

theorem cell23_727799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_727799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727799 prefixEnd_727799 := by exact prefixLift 727799
  have htrace : WordTrace (prefixWord ++ tailWord_727799) baseStart_727799 baseEnd_727799 := by
    simpa [prefixWord, tailWord_727799, baseEnd_727799] using wordTrace_append hprefix tailTrace_727799
  have hstable : (prefixWord ++ tailWord_727799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727799).length < 2 ^ (prefixWord ++ tailWord_727799).sum := by decide
  have hdescent : baseEnd_727799 < baseStart_727799 := by decide
  rcases family_descends (prefixWord ++ tailWord_727799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727810 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_727810 : Nat := 118140960795 + 727810 * 2 ^ 59
def prefixEnd_727810 : Nat := 4983230072969 + 3 ^ 40 * 727810 * 2
def baseEnd_727810 : Nat := 373716355148902673727869

theorem tailTrace_727810 : CollatzResearch.WordTrace tailWord_727810 prefixEnd_727810 373716355148902673727869 := by
  unfold tailWord_727810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6636352873319036224269221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17696940995517429931384589 6636352873319036224269221)
  ·
    refine ⟨1244316163747319292050479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6636352873319036224269221 1244316163747319292050479)
    ·
      refine ⟨1866474245620978938075719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1244316163747319292050479 1866474245620978938075719)
      ·
        refine ⟨2799711368431468407113579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866474245620978938075719 2799711368431468407113579)
        ·
          refine ⟨4199567052647202610670369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799711368431468407113579 4199567052647202610670369)
          ·
            refine ⟨3149675289485401958002777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4199567052647202610670369 3149675289485401958002777)
            ·
              refine ⟨2362256467114051468502083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3149675289485401958002777 2362256467114051468502083)
              ·
                refine ⟨3543384700671077202753125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362256467114051468502083 3543384700671077202753125)
                ·
                  refine ⟨664384631375826975516211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3543384700671077202753125 664384631375826975516211)
                  ·
                    refine ⟨996576947063740463274317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 664384631375826975516211 996576947063740463274317)
                    ·
                      refine ⟨373716355148902673727869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 996576947063740463274317 373716355148902673727869)
                      ·
                        rfl

theorem cell23_727810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_727810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727810 prefixEnd_727810 := by exact prefixLift 727810
  have htrace : WordTrace (prefixWord ++ tailWord_727810) baseStart_727810 baseEnd_727810 := by
    simpa [prefixWord, tailWord_727810, baseEnd_727810] using wordTrace_append hprefix tailTrace_727810
  have hstable : (prefixWord ++ tailWord_727810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727810).length < 2 ^ (prefixWord ++ tailWord_727810).sum := by decide
  have hdescent : baseEnd_727810 < baseStart_727810 := by decide
  rcases family_descends (prefixWord ++ tailWord_727810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727819 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 5]
def baseStart_727819 : Nat := 118140960795 + 727819 * 2 ^ 59
def prefixEnd_727819 : Nat := 4983230072969 + 3 ^ 40 * 727819 * 2
def baseEnd_727819 : Nat := 373720976474793138515327

theorem tailTrace_727819 : CollatzResearch.WordTrace tailWord_727819 prefixEnd_727819 373720976474793138515327 := by
  unfold tailWord_727819
  simp only [CollatzResearch.WordTrace]
  refine ⟨26545739750243539434154511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17697159833495692956103007 26545739750243539434154511)
  ·
    refine ⟨39818609625365309151231767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26545739750243539434154511 39818609625365309151231767)
    ·
      refine ⟨59727914438047963726847651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39818609625365309151231767 59727914438047963726847651)
      ·
        refine ⟨89591871657071945590271477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59727914438047963726847651 89591871657071945590271477)
        ·
          refine ⟨8399237967850494899087951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89591871657071945590271477 8399237967850494899087951)
          ·
            refine ⟨12598856951775742348631927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8399237967850494899087951 12598856951775742348631927)
            ·
              refine ⟨18898285427663613522947891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12598856951775742348631927 18898285427663613522947891)
              ·
                refine ⟨28347428141495420284421837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18898285427663613522947891 28347428141495420284421837)
                ·
                  refine ⟨10630285553060782606658189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28347428141495420284421837 10630285553060782606658189)
                  ·
                    refine ⟨3986357082397793477496821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10630285553060782606658189 3986357082397793477496821)
                    ·
                      refine ⟨373720976474793138515327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3986357082397793477496821 373720976474793138515327)
                      ·
                        rfl

theorem cell23_727819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_727819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727819 prefixEnd_727819 := by exact prefixLift 727819
  have htrace : WordTrace (prefixWord ++ tailWord_727819) baseStart_727819 baseEnd_727819 := by
    simpa [prefixWord, tailWord_727819, baseEnd_727819] using wordTrace_append hprefix tailTrace_727819
  have hstable : (prefixWord ++ tailWord_727819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727819).length < 2 ^ (prefixWord ++ tailWord_727819).sum := by decide
  have hdescent : baseEnd_727819 < baseStart_727819 := by decide
  rcases family_descends (prefixWord ++ tailWord_727819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727833 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 6, 2, 2]
def baseStart_727833 : Nat := 118140960795 + 727833 * 2 ^ 59
def prefixEnd_727833 : Nat := 4983230072969 + 3 ^ 40 * 727833 * 2
def baseEnd_727833 : Nat := 373728165203956083740263

theorem tailTrace_727833 : CollatzResearch.WordTrace tailWord_727833 prefixEnd_727833 373728165203956083740263 := by
  unfold tailWord_727833
  simp only [CollatzResearch.WordTrace]
  refine ⟨26546250372192819825164153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17697500248128546550109435 26546250372192819825164153)
  ·
    refine ⟨19909687779144614868873115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26546250372192819825164153 19909687779144614868873115)
    ·
      refine ⟨29864531668716922303309673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19909687779144614868873115 29864531668716922303309673)
      ·
        refine ⟨22398398751537691727482255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29864531668716922303309673 22398398751537691727482255)
        ·
          refine ⟨33597598127306537591223383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22398398751537691727482255 33597598127306537591223383)
          ·
            refine ⟨50396397190959806386835075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33597598127306537591223383 50396397190959806386835075)
            ·
              refine ⟨75594595786439709580252613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50396397190959806386835075 75594595786439709580252613)
              ·
                refine ⟨14173986709957445546297365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75594595786439709580252613 14173986709957445546297365)
                ·
                  refine ⟨664405627029255259982689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14173986709957445546297365 664405627029255259982689)
                  ·
                    refine ⟨498304220271941444987017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 664405627029255259982689 498304220271941444987017)
                    ·
                      refine ⟨373728165203956083740263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498304220271941444987017 373728165203956083740263)
                      ·
                        rfl

theorem cell23_727833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_727833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727833 prefixEnd_727833 := by exact prefixLift 727833
  have htrace : WordTrace (prefixWord ++ tailWord_727833) baseStart_727833 baseEnd_727833 := by
    simpa [prefixWord, tailWord_727833, baseEnd_727833] using wordTrace_append hprefix tailTrace_727833
  have hstable : (prefixWord ++ tailWord_727833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727833).length < 2 ^ (prefixWord ++ tailWord_727833).sum := by decide
  have hdescent : baseEnd_727833 < baseStart_727833 := by decide
  rcases family_descends (prefixWord ++ tailWord_727833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727836 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_727836 : Nat := 118140960795 + 727836 * 2 ^ 59
def prefixEnd_727836 : Nat := 4983230072969 + 3 ^ 40 * 727836 * 2
def baseEnd_727836 : Nat := 373729705645919572002749

theorem tailTrace_727836 : CollatzResearch.WordTrace tailWord_727836 prefixEnd_727836 373729705645919572002749 := by
  unfold tailWord_727836
  simp only [CollatzResearch.WordTrace]
  refine ⟨13273179895590975668761681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17697573194121300891682241 13273179895590975668761681)
  ·
    refine ⟨9954884921693231751571261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13273179895590975668761681 9954884921693231751571261)
    ·
      refine ⟨3733081845634961906839223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9954884921693231751571261 3733081845634961906839223)
      ·
        refine ⟨5599622768452442860258835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3733081845634961906839223 5599622768452442860258835)
        ·
          refine ⟨8399434152678664290388253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5599622768452442860258835 8399434152678664290388253)
          ·
            refine ⟨3149787807254499108895595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8399434152678664290388253 3149787807254499108895595)
            ·
              refine ⟨4724681710881748663343393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3149787807254499108895595 4724681710881748663343393)
              ·
                refine ⟨3543511283161311497507545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4724681710881748663343393 3543511283161311497507545)
                ·
                  refine ⟨2657633462370983623130659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3543511283161311497507545 2657633462370983623130659)
                  ·
                    refine ⟨3986450193556475434695989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2657633462370983623130659 3986450193556475434695989)
                    ·
                      refine ⟨373729705645919572002749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3986450193556475434695989 373729705645919572002749)
                      ·
                        rfl

theorem cell23_727836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_727836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727836 prefixEnd_727836 := by exact prefixLift 727836
  have htrace : WordTrace (prefixWord ++ tailWord_727836) baseStart_727836 baseEnd_727836 := by
    simpa [prefixWord, tailWord_727836, baseEnd_727836] using wordTrace_append hprefix tailTrace_727836
  have hstable : (prefixWord ++ tailWord_727836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727836).length < 2 ^ (prefixWord ++ tailWord_727836).sum := by decide
  have hdescent : baseEnd_727836 < baseStart_727836 := by decide
  rcases family_descends (prefixWord ++ tailWord_727836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727837 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_727837 : Nat := 118140960795 + 727837 * 2 ^ 59
def prefixEnd_727837 : Nat := 4983230072969 + 3 ^ 40 * 727837 * 2
def baseEnd_727837 : Nat := 373730219126574068090245

theorem tailTrace_727837 : CollatzResearch.WordTrace tailWord_727837 prefixEnd_727837 373730219126574068090245 := by
  unfold tailWord_727837
  simp only [CollatzResearch.WordTrace]
  refine ⟨26546396264178328508309765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17697597509452219005539843 26546396264178328508309765)
  ·
    refine ⟨4977449299533436595308081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26546396264178328508309765 4977449299533436595308081)
    ·
      refine ⟨3733086974650077446481061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4977449299533436595308081 3733086974650077446481061)
      ·
        refine ⟨699953807746889521215199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3733086974650077446481061 699953807746889521215199)
        ·
          refine ⟨1049930711620334281822799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699953807746889521215199 1049930711620334281822799)
          ·
            refine ⟨1574896067430501422734199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049930711620334281822799 1574896067430501422734199)
            ·
              refine ⟨2362344101145752134101299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574896067430501422734199 2362344101145752134101299)
              ·
                refine ⟨3543516151718628201151949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362344101145752134101299 3543516151718628201151949)
                ·
                  refine ⟨1328818556894485575431981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3543516151718628201151949 1328818556894485575431981)
                  ·
                    refine ⟨498306958835432090786993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1328818556894485575431981 498306958835432090786993)
                    ·
                      refine ⟨373730219126574068090245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498306958835432090786993 373730219126574068090245)
                      ·
                        rfl

theorem cell23_727837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_727837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727837 prefixEnd_727837 := by exact prefixLift 727837
  have htrace : WordTrace (prefixWord ++ tailWord_727837) baseStart_727837 baseEnd_727837 := by
    simpa [prefixWord, tailWord_727837, baseEnd_727837] using wordTrace_append hprefix tailTrace_727837
  have hstable : (prefixWord ++ tailWord_727837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727837).length < 2 ^ (prefixWord ++ tailWord_727837).sum := by decide
  have hdescent : baseEnd_727837 < baseStart_727837 := by decide
  rcases family_descends (prefixWord ++ tailWord_727837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727854 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_727854 : Nat := 118140960795 + 727854 * 2 ^ 59
def prefixEnd_727854 : Nat := 4983230072969 + 3 ^ 40 * 727854 * 2
def baseEnd_727854 : Nat := 373738948297700501577667

theorem tailTrace_727854 : CollatzResearch.WordTrace tailWord_727854 prefixEnd_727854 373738948297700501577667 := by
  unfold tailWord_727854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3318377038139592551459827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17698010870077826941119077 3318377038139592551459827)
  ·
    refine ⟨4977565557209388827189741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3318377038139592551459827 4977565557209388827189741)
    ·
      refine ⟨1866587083953520810196153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4977565557209388827189741 1866587083953520810196153)
      ·
        refine ⟨1399940312965140607647115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1866587083953520810196153 1399940312965140607647115)
        ·
          refine ⟨2099910469447710911470673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399940312965140607647115 2099910469447710911470673)
          ·
            refine ⟨1574932852085783183603005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2099910469447710911470673 1574932852085783183603005)
            ·
              refine ⟨590599819532168693851127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1574932852085783183603005 590599819532168693851127)
              ·
                refine ⟨885899729298253040776691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590599819532168693851127 885899729298253040776691)
                ·
                  refine ⟨1328849593947379561165037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885899729298253040776691 1328849593947379561165037)
                  ·
                    refine ⟨498318597730267335436889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1328849593947379561165037 498318597730267335436889)
                    ·
                      refine ⟨373738948297700501577667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498318597730267335436889 373738948297700501577667)
                      ·
                        rfl

theorem cell23_727854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_727854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727854 prefixEnd_727854 := by exact prefixLift 727854
  have htrace : WordTrace (prefixWord ++ tailWord_727854) baseStart_727854 baseEnd_727854 := by
    simpa [prefixWord, tailWord_727854, baseEnd_727854] using wordTrace_append hprefix tailTrace_727854
  have hstable : (prefixWord ++ tailWord_727854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727854).length < 2 ^ (prefixWord ++ tailWord_727854).sum := by decide
  have hdescent : baseEnd_727854 < baseStart_727854 := by decide
  rcases family_descends (prefixWord ++ tailWord_727854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727886 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_727886 : Nat := 118140960795 + 727886 * 2 ^ 59
def prefixEnd_727886 : Nat := 4983230072969 + 3 ^ 40 * 727886 * 2
def baseEnd_727886 : Nat := 124585126559548125459173

theorem tailTrace_727886 : CollatzResearch.WordTrace tailWord_727886 prefixEnd_727886 124585126559548125459173 := by
  unfold tailWord_727886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3318522930125101234605439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17698788960667206584562341 3318522930125101234605439)
  ·
    refine ⟨4977784395187651851908159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3318522930125101234605439 4977784395187651851908159)
    ·
      refine ⟨7466676592781477777862239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4977784395187651851908159 7466676592781477777862239)
      ·
        refine ⟨11200014889172216666793359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7466676592781477777862239 11200014889172216666793359)
        ·
          refine ⟨16800022333758325000190039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11200014889172216666793359 16800022333758325000190039)
          ·
            refine ⟨25200033500637487500285059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16800022333758325000190039 25200033500637487500285059)
            ·
              refine ⟨37800050250956231250427589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25200033500637487500285059 37800050250956231250427589)
              ·
                refine ⟨7087509422054293359455173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37800050250956231250427589 7087509422054293359455173)
                ·
                  refine ⟨1328908016635180004897845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7087509422054293359455173 1328908016635180004897845)
                  ·
                    refine ⟨124585126559548125459173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1328908016635180004897845 124585126559548125459173)
                    ·
                      rfl

theorem cell23_727886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_727886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727886 prefixEnd_727886 := by exact prefixLift 727886
  have htrace : WordTrace (prefixWord ++ tailWord_727886) baseStart_727886 baseEnd_727886 := by
    simpa [prefixWord, tailWord_727886, baseEnd_727886] using wordTrace_append hprefix tailTrace_727886
  have hstable : (prefixWord ++ tailWord_727886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727886).length < 2 ^ (prefixWord ++ tailWord_727886).sum := by decide
  have hdescent : baseEnd_727886 < baseStart_727886 := by decide
  rcases family_descends (prefixWord ++ tailWord_727886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727893 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 2, 5, 2]
def baseStart_727893 : Nat := 118140960795 + 727893 * 2 ^ 59
def prefixEnd_727893 : Nat := 4983230072969 + 3 ^ 40 * 727893 * 2
def baseEnd_727893 : Nat := 373758974043225848989987

theorem tailTrace_727893 : CollatzResearch.WordTrace tailWord_727893 prefixEnd_727893 373758974043225848989987 := by
  unfold tailWord_727893
  simp only [CollatzResearch.WordTrace]
  refine ⟨26548438751975450072348333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17698959167983633381565555 26548438751975450072348333)
  ·
    refine ⟨9955664531990793777130625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26548438751975450072348333 9955664531990793777130625)
    ·
      refine ⟨7466748398993095332847969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9955664531990793777130625 7466748398993095332847969)
      ·
        refine ⟨5600061299244821499635977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7466748398993095332847969 5600061299244821499635977)
        ·
          refine ⟨4200045974433616124726983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5600061299244821499635977 4200045974433616124726983)
          ·
            refine ⟨6300068961650424187090475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200045974433616124726983 6300068961650424187090475)
            ·
              refine ⟨9450103442475636280635713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6300068961650424187090475 9450103442475636280635713)
              ·
                refine ⟨7087577581856727210476785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9450103442475636280635713 7087577581856727210476785)
                ·
                  refine ⟨5315683186392545407857589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7087577581856727210476785 5315683186392545407857589)
                  ·
                    refine ⟨498345298724301131986649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5315683186392545407857589 498345298724301131986649)
                    ·
                      refine ⟨373758974043225848989987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498345298724301131986649 373758974043225848989987)
                      ·
                        rfl

theorem cell23_727893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_727893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727893 prefixEnd_727893 := by exact prefixLift 727893
  have htrace : WordTrace (prefixWord ++ tailWord_727893) baseStart_727893 baseEnd_727893 := by
    simpa [prefixWord, tailWord_727893, baseEnd_727893] using wordTrace_append hprefix tailTrace_727893
  have hstable : (prefixWord ++ tailWord_727893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727893).length < 2 ^ (prefixWord ++ tailWord_727893).sum := by decide
  have hdescent : baseEnd_727893 < baseStart_727893 := by decide
  rcases family_descends (prefixWord ++ tailWord_727893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727923 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 2, 4, 2]
def baseStart_727923 : Nat := 118140960795 + 727923 * 2 ^ 59
def prefixEnd_727923 : Nat := 4983230072969 + 3 ^ 40 * 727923 * 2
def baseEnd_727923 : Nat := 373774378462860731614849

theorem tailTrace_727923 : CollatzResearch.WordTrace tailWord_727923 prefixEnd_727923 373774378462860731614849 := by
  unfold tailWord_727923
  simp only [CollatzResearch.WordTrace]
  refine ⟨26549532941866765195940423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17699688627911176797293615 26549532941866765195940423)
  ·
    refine ⟨39824299412800147793910635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26549532941866765195940423 39824299412800147793910635)
    ·
      refine ⟨59736449119200221690865953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39824299412800147793910635 59736449119200221690865953)
      ·
        refine ⟨44802336839400166268149465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59736449119200221690865953 44802336839400166268149465)
        ·
          refine ⟨33601752629550124701112099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44802336839400166268149465 33601752629550124701112099)
          ·
            refine ⟨50402628944325187051668149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33601752629550124701112099 50402628944325187051668149)
            ·
              refine ⟨4725246463530486286093889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50402628944325187051668149 4725246463530486286093889)
              ·
                refine ⟨3543934847647864714570417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4725246463530486286093889 3543934847647864714570417)
                ·
                  refine ⟨2657951135735898535927813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3543934847647864714570417 2657951135735898535927813)
                  ·
                    refine ⟨498365837950480975486465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2657951135735898535927813 498365837950480975486465)
                    ·
                      refine ⟨373774378462860731614849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498365837950480975486465 373774378462860731614849)
                      ·
                        rfl

theorem cell23_727923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 4, 2].length) (baseStart_727923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727923 prefixEnd_727923 := by exact prefixLift 727923
  have htrace : WordTrace (prefixWord ++ tailWord_727923) baseStart_727923 baseEnd_727923 := by
    simpa [prefixWord, tailWord_727923, baseEnd_727923] using wordTrace_append hprefix tailTrace_727923
  have hstable : (prefixWord ++ tailWord_727923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727923).length < 2 ^ (prefixWord ++ tailWord_727923).sum := by decide
  have hdescent : baseEnd_727923 < baseStart_727923 := by decide
  rcases family_descends (prefixWord ++ tailWord_727923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727933 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_727933 : Nat := 118140960795 + 727933 * 2 ^ 59
def prefixEnd_727933 : Nat := 4983230072969 + 3 ^ 40 * 727933 * 2
def baseEnd_727933 : Nat := 124593171089801897496601

theorem tailTrace_727933 : CollatzResearch.WordTrace tailWord_727933 prefixEnd_727933 124593171089801897496601 := by
  unfold tailWord_727933
  simp only [CollatzResearch.WordTrace]
  refine ⟨26549897671830536903804453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17699931781220357935869635 26549897671830536903804453)
  ·
    refine ⟨4978105813468225669463335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26549897671830536903804453 4978105813468225669463335)
    ·
      refine ⟨7467158720202338504195003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4978105813468225669463335 7467158720202338504195003)
      ·
        refine ⟨11200738080303507756292505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7467158720202338504195003 11200738080303507756292505)
        ·
          refine ⟨8400553560227630817219379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11200738080303507756292505 8400553560227630817219379)
          ·
            refine ⟨12600830340341446225829069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8400553560227630817219379 12600830340341446225829069)
            ·
              refine ⟨4725311377628042334685901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12600830340341446225829069 4725311377628042334685901)
              ·
                refine ⟨1771991766610515875507213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4725311377628042334685901 1771991766610515875507213)
                ·
                  refine ⟨664496912478943453315205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1771991766610515875507213 664496912478943453315205)
                  ·
                    refine ⟨124593171089801897496601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 664496912478943453315205 124593171089801897496601)
                    ·
                      rfl

theorem cell23_727933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_727933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727933 prefixEnd_727933 := by exact prefixLift 727933
  have htrace : WordTrace (prefixWord ++ tailWord_727933) baseStart_727933 baseEnd_727933 := by
    simpa [prefixWord, tailWord_727933, baseEnd_727933] using wordTrace_append hprefix tailTrace_727933
  have hstable : (prefixWord ++ tailWord_727933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727933).length < 2 ^ (prefixWord ++ tailWord_727933).sum := by decide
  have hdescent : baseEnd_727933 < baseStart_727933 := by decide
  rcases family_descends (prefixWord ++ tailWord_727933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727943 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_727943 : Nat := 118140960795 + 727943 * 2 ^ 59
def prefixEnd_727943 : Nat := 4983230072969 + 3 ^ 40 * 727943 * 2
def baseEnd_727943 : Nat := 373784648075950653364757

theorem tailTrace_727943 : CollatzResearch.WordTrace tailWord_727943 prefixEnd_727943 373784648075950653364757 := by
  unfold tailWord_727943
  simp only [CollatzResearch.WordTrace]
  refine ⟨26550262401794308611668483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17700174934529539074445655 26550262401794308611668483)
  ·
    refine ⟨39825393602691462917502725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26550262401794308611668483 39825393602691462917502725)
    ·
      refine ⟨7467261300504649297031761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39825393602691462917502725 7467261300504649297031761)
      ·
        refine ⟨5600445975378486972773821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7467261300504649297031761 5600445975378486972773821)
        ·
          refine ⟨2100167240766932614790183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5600445975378486972773821 2100167240766932614790183)
          ·
            refine ⟨3150250861150398922185275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100167240766932614790183 3150250861150398922185275)
            ·
              refine ⟨4725376291725598383277913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150250861150398922185275 4725376291725598383277913)
              ·
                refine ⟨3544032218794198787458435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4725376291725598383277913 3544032218794198787458435)
                ·
                  refine ⟨5316048328191298181187653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544032218794198787458435 5316048328191298181187653)
                  ·
                    refine ⟨996759061535868408972685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5316048328191298181187653 996759061535868408972685)
                    ·
                      refine ⟨373784648075950653364757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 996759061535868408972685 373784648075950653364757)
                      ·
                        rfl

theorem cell23_727943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_727943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727943 prefixEnd_727943 := by exact prefixLift 727943
  have htrace : WordTrace (prefixWord ++ tailWord_727943) baseStart_727943 baseEnd_727943 := by
    simpa [prefixWord, tailWord_727943, baseEnd_727943] using wordTrace_append hprefix tailTrace_727943
  have hstable : (prefixWord ++ tailWord_727943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727943).length < 2 ^ (prefixWord ++ tailWord_727943).sum := by decide
  have hdescent : baseEnd_727943 < baseStart_727943 := by decide
  rcases family_descends (prefixWord ++ tailWord_727943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727967 : List Nat := [1, 1, 2, 5, 2, 1, 3, 3, 1, 4]
def baseStart_727967 : Nat := 118140960795 + 727967 * 2 ^ 59
def prefixEnd_727967 : Nat := 4983230072969 + 3 ^ 40 * 727967 * 2
def baseEnd_727967 : Nat := 124598990537219519821549

theorem tailTrace_727967 : CollatzResearch.WordTrace tailWord_727967 prefixEnd_727967 124598990537219519821549 := by
  unfold tailWord_727967
  simp only [CollatzResearch.WordTrace]
  refine ⟨26551137753707360710542155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17700758502471573807028103 26551137753707360710542155)
  ·
    refine ⟨39826706630561041065813233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26551137753707360710542155 39826706630561041065813233)
    ·
      refine ⟨29870029972920780799359925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39826706630561041065813233 29870029972920780799359925)
      ·
        refine ⟨2800315309961323199939993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29870029972920780799359925 2800315309961323199939993)
        ·
          refine ⟨2100236482470992399954995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2800315309961323199939993 2100236482470992399954995)
          ·
            refine ⟨3150354723706488599932493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100236482470992399954995 3150354723706488599932493)
            ·
              refine ⟨1181383021389933224974685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3150354723706488599932493 1181383021389933224974685)
              ·
                refine ⟨443018633021224959365507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1181383021389933224974685 443018633021224959365507)
                ·
                  refine ⟨664527949531837439048261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443018633021224959365507 664527949531837439048261)
                  ·
                    refine ⟨124598990537219519821549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 664527949531837439048261 124598990537219519821549)
                    ·
                      rfl

theorem cell23_727967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 1, 4].length) (baseStart_727967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727967 prefixEnd_727967 := by exact prefixLift 727967
  have htrace : WordTrace (prefixWord ++ tailWord_727967) baseStart_727967 baseEnd_727967 := by
    simpa [prefixWord, tailWord_727967, baseEnd_727967] using wordTrace_append hprefix tailTrace_727967
  have hstable : (prefixWord ++ tailWord_727967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727967).length < 2 ^ (prefixWord ++ tailWord_727967).sum := by decide
  have hdescent : baseEnd_727967 < baseStart_727967 := by decide
  rcases family_descends (prefixWord ++ tailWord_727967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727983 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 3, 5, 2]
def baseStart_727983 : Nat := 118140960795 + 727983 * 2 ^ 59
def prefixEnd_727983 : Nat := 4983230072969 + 3 ^ 40 * 727983 * 2
def baseEnd_727983 : Nat := 373805187302130496864573

theorem tailTrace_727983 : CollatzResearch.WordTrace tailWord_727983 prefixEnd_727983 373805187302130496864573 := by
  unfold tailWord_727983
  simp only [CollatzResearch.WordTrace]
  refine ⟨26551721321649395443124603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17701147547766263628749735 26551721321649395443124603)
  ·
    refine ⟨39827581982474093164686905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26551721321649395443124603 39827581982474093164686905)
    ·
      refine ⟨29870686486855569873515179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39827581982474093164686905 29870686486855569873515179)
      ·
        refine ⟨44806029730283354810272769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29870686486855569873515179 44806029730283354810272769)
        ·
          refine ⟨33604522297712516107704577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44806029730283354810272769 33604522297712516107704577)
          ·
            refine ⟨25203391723284387080778433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33604522297712516107704577 25203391723284387080778433)
            ·
              refine ⟨18902543792463290310583825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25203391723284387080778433 18902543792463290310583825)
              ·
                refine ⟨14176907844347467732937869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18902543792463290310583825 14176907844347467732937869)
                ·
                  refine ⟨5316340441630300399851701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14176907844347467732937869 5316340441630300399851701)
                  ·
                    refine ⟨498406916402840662486097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5316340441630300399851701 498406916402840662486097)
                    ·
                      refine ⟨373805187302130496864573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498406916402840662486097 373805187302130496864573)
                      ·
                        rfl

theorem cell23_727983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 5, 2].length) (baseStart_727983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727983 prefixEnd_727983 := by exact prefixLift 727983
  have htrace : WordTrace (prefixWord ++ tailWord_727983) baseStart_727983 baseEnd_727983 := by
    simpa [prefixWord, tailWord_727983, baseEnd_727983] using wordTrace_append hprefix tailTrace_727983
  have hstable : (prefixWord ++ tailWord_727983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727983).length < 2 ^ (prefixWord ++ tailWord_727983).sum := by decide
  have hdescent : baseEnd_727983 < baseStart_727983 := by decide
  rcases family_descends (prefixWord ++ tailWord_727983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727986 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_727986 : Nat := 118140960795 + 727986 * 2 ^ 59
def prefixEnd_727986 : Nat := 4983230072969 + 3 ^ 40 * 727986 * 2
def baseEnd_727986 : Nat := 373806727744093985127059

theorem tailTrace_727986 : CollatzResearch.WordTrace tailWord_727986 prefixEnd_727986 373806727744093985127059 := by
  unfold tailWord_727986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6637957685159631738870953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17701220493759017970322541 6637957685159631738870953)
  ·
    refine ⟨4978468263869723804153215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6637957685159631738870953 4978468263869723804153215)
    ·
      refine ⟨7467702395804585706229823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4978468263869723804153215 7467702395804585706229823)
      ·
        refine ⟨11201553593706878559344735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7467702395804585706229823 11201553593706878559344735)
        ·
          refine ⟨16802330390560317839017103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11201553593706878559344735 16802330390560317839017103)
          ·
            refine ⟨25203495585840476758525655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16802330390560317839017103 25203495585840476758525655)
            ·
              refine ⟨37805243378760715137788483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25203495585840476758525655 37805243378760715137788483)
              ·
                refine ⟨56707865068141072706682725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37805243378760715137788483 56707865068141072706682725)
                ·
                  refine ⟨10632724700276451132503011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56707865068141072706682725 10632724700276451132503011)
                  ·
                    refine ⟨15949087050414676698754517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10632724700276451132503011 15949087050414676698754517)
                    ·
                      refine ⟨373806727744093985127059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15949087050414676698754517 373806727744093985127059)
                      ·
                        rfl

theorem cell23_727986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_727986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727986 prefixEnd_727986 := by exact prefixLift 727986
  have htrace : WordTrace (prefixWord ++ tailWord_727986) baseStart_727986 baseEnd_727986 := by
    simpa [prefixWord, tailWord_727986, baseEnd_727986] using wordTrace_append hprefix tailTrace_727986
  have hstable : (prefixWord ++ tailWord_727986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727986).length < 2 ^ (prefixWord ++ tailWord_727986).sum := by decide
  have hdescent : baseEnd_727986 < baseStart_727986 := by decide
  rcases family_descends (prefixWord ++ tailWord_727986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727997 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 6]
def baseStart_727997 : Nat := 118140960795 + 727997 * 2 ^ 59
def prefixEnd_727997 : Nat := 4983230072969 + 3 ^ 40 * 727997 * 2
def baseEnd_727997 : Nat := 41534708447921493565501

theorem tailTrace_727997 : CollatzResearch.WordTrace tailWord_727997 prefixEnd_727997 41534708447921493565501 := by
  unfold tailWord_727997
  simp only [CollatzResearch.WordTrace]
  refine ⟨26552231943598675834134245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17701487962399117222756163 26552231943598675834134245)
  ·
    refine ⟨4978543489424751718900171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26552231943598675834134245 4978543489424751718900171)
    ·
      refine ⟨7467815234137127578350257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4978543489424751718900171 7467815234137127578350257)
      ·
        refine ⟨5600861425602845683762693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7467815234137127578350257 5600861425602845683762693)
        ·
          refine ⟨1050161517300533565705505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5600861425602845683762693 1050161517300533565705505)
          ·
            refine ⟨787621137975400174279129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050161517300533565705505 787621137975400174279129)
            ·
              refine ⟨590715853481550130709347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787621137975400174279129 590715853481550130709347)
              ·
                refine ⟨886073780222325196064021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590715853481550130709347 886073780222325196064021)
                ·
                  refine ⟨41534708447921493565501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 886073780222325196064021 41534708447921493565501)
                  ·
                    rfl

theorem cell23_727997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_727997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_727997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_727997 prefixEnd_727997 := by exact prefixLift 727997
  have htrace : WordTrace (prefixWord ++ tailWord_727997) baseStart_727997 baseEnd_727997 := by
    simpa [prefixWord, tailWord_727997, baseEnd_727997] using wordTrace_append hprefix tailTrace_727997
  have hstable : (prefixWord ++ tailWord_727997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727997).length < 2 ^ (prefixWord ++ tailWord_727997).sum := by decide
  have hdescent : baseEnd_727997 < baseStart_727997 := by decide
  rcases family_descends (prefixWord ++ tailWord_727997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728023 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 4, 4]
def baseStart_728023 : Nat := 118140960795 + 728023 * 2 ^ 59
def prefixEnd_728023 : Nat := 4983230072969 + 3 ^ 40 * 728023 * 2
def baseEnd_728023 : Nat := 124608575509436780121463

theorem tailTrace_728023 : CollatzResearch.WordTrace tailWord_728023 prefixEnd_728023 124608575509436780121463 := by
  unfold tailWord_728023
  simp only [CollatzResearch.WordTrace]
  refine ⟨26553180241504482274580723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17702120161002988183053815 26553180241504482274580723)
  ·
    refine ⟨39829770362256723411871085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26553180241504482274580723 39829770362256723411871085)
    ·
      refine ⟨14936163885846271279451657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39829770362256723411871085 14936163885846271279451657)
      ·
        refine ⟨11202122914384703459588743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14936163885846271279451657 11202122914384703459588743)
        ·
          refine ⟨16803184371577055189383115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11202122914384703459588743 16803184371577055189383115)
          ·
            refine ⟨25204776557365582784074673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16803184371577055189383115 25204776557365582784074673)
            ·
              refine ⟨18903582418024187088056005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25204776557365582784074673 18903582418024187088056005)
              ·
                refine ⟨3544421703379535079010501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18903582418024187088056005 3544421703379535079010501)
                ·
                  refine ⟨664579069383662827314469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3544421703379535079010501 664579069383662827314469)
                  ·
                    refine ⟨124608575509436780121463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 664579069383662827314469 124608575509436780121463)
                    ·
                      rfl

theorem cell23_728023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_728023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728023 prefixEnd_728023 := by exact prefixLift 728023
  have htrace : WordTrace (prefixWord ++ tailWord_728023) baseStart_728023 baseEnd_728023 := by
    simpa [prefixWord, tailWord_728023, baseEnd_728023] using wordTrace_append hprefix tailTrace_728023
  have hstable : (prefixWord ++ tailWord_728023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728023).length < 2 ^ (prefixWord ++ tailWord_728023).sum := by decide
  have hdescent : baseEnd_728023 < baseStart_728023 := by decide
  rcases family_descends (prefixWord ++ tailWord_728023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728034 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_728034 : Nat := 118140960795 + 728034 * 2 ^ 59
def prefixEnd_728034 : Nat := 4983230072969 + 3 ^ 40 * 728034 * 2
def baseEnd_728034 : Nat := 373831374815509797326839

theorem tailTrace_728034 : CollatzResearch.WordTrace tailWord_728034 prefixEnd_728034 373831374815509797326839 := by
  unfold tailWord_728034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6638395361116157788307789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17702387629643087435487437 6638395361116157788307789)
  ·
    refine ⟨2489398260418559170615421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6638395361116157788307789 2489398260418559170615421)
    ·
      refine ⟨933524347656959688980783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2489398260418559170615421 933524347656959688980783)
      ·
        refine ⟨1400286521485439533471175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933524347656959688980783 1400286521485439533471175)
        ·
          refine ⟨2100429782228159300206763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400286521485439533471175 2100429782228159300206763)
          ·
            refine ⟨3150644673342238950310145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100429782228159300206763 3150644673342238950310145)
            ·
              refine ⟨2362983505006679212732609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3150644673342238950310145 2362983505006679212732609)
              ·
                refine ⟨1772237628755009409549457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2362983505006679212732609 1772237628755009409549457)
                ·
                  refine ⟨1329178221566257057162093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1772237628755009409549457 1329178221566257057162093)
                  ·
                    refine ⟨498441833087346396435785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329178221566257057162093 498441833087346396435785)
                    ·
                      refine ⟨373831374815509797326839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498441833087346396435785 373831374815509797326839)
                      ·
                        rfl

theorem cell23_728034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_728034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728034 prefixEnd_728034 := by exact prefixLift 728034
  have htrace : WordTrace (prefixWord ++ tailWord_728034) baseStart_728034 baseEnd_728034 := by
    simpa [prefixWord, tailWord_728034, baseEnd_728034] using wordTrace_append hprefix tailTrace_728034
  have hstable : (prefixWord ++ tailWord_728034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728034).length < 2 ^ (prefixWord ++ tailWord_728034).sum := by decide
  have hdescent : baseEnd_728034 < baseStart_728034 := by decide
  rcases family_descends (prefixWord ++ tailWord_728034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728040 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 2, 4]
def baseStart_728040 : Nat := 118140960795 + 728040 * 2 ^ 59
def prefixEnd_728040 : Nat := 4983230072969 + 3 ^ 40 * 728040 * 2
def baseEnd_728040 : Nat := 124611485233145591283937

theorem tailTrace_728040 : CollatzResearch.WordTrace tailWord_728040 prefixEnd_728040 124611485233145591283937 := by
  unfold tailWord_728040
  simp only [CollatzResearch.WordTrace]
  refine ⟨13276900141221447088974787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17702533521628596118633049 13276900141221447088974787)
  ·
    refine ⟨19915350211832170633462181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13276900141221447088974787 19915350211832170633462181)
    ·
      refine ⟨3734128164718531993774159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19915350211832170633462181 3734128164718531993774159)
      ·
        refine ⟨5601192247077797990661239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3734128164718531993774159 5601192247077797990661239)
        ·
          refine ⟨8401788370616696985991859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5601192247077797990661239 8401788370616696985991859)
          ·
            refine ⟨12602682555925045478987789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8401788370616696985991859 12602682555925045478987789)
            ·
              refine ⟨4726005958471892054620421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12602682555925045478987789 4726005958471892054620421)
              ·
                refine ⟨886126117213479760241329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4726005958471892054620421 886126117213479760241329)
                ·
                  refine ⟨664594587910109820180997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 886126117213479760241329 664594587910109820180997)
                  ·
                    refine ⟨124611485233145591283937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 664594587910109820180997 124611485233145591283937)
                    ·
                      rfl

theorem cell23_728040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_728040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728040 prefixEnd_728040 := by exact prefixLift 728040
  have htrace : WordTrace (prefixWord ++ tailWord_728040) baseStart_728040 baseEnd_728040 := by
    simpa [prefixWord, tailWord_728040, baseEnd_728040] using wordTrace_append hprefix tailTrace_728040
  have hstable : (prefixWord ++ tailWord_728040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728040).length < 2 ^ (prefixWord ++ tailWord_728040).sum := by decide
  have hdescent : baseEnd_728040 < baseStart_728040 := by decide
  rcases family_descends (prefixWord ++ tailWord_728040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728060 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_728060 : Nat := 118140960795 + 728060 * 2 ^ 59
def prefixEnd_728060 : Nat := 4983230072969 + 3 ^ 40 * 728060 * 2
def baseEnd_728060 : Nat := 373844725312526695601719

theorem tailTrace_728060 : CollatzResearch.WordTrace tailWord_728060 prefixEnd_728060 373844725312526695601719 := by
  unfold tailWord_728060
  simp only [CollatzResearch.WordTrace]
  refine ⟨13277264871185218796838817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17703019828246958395785089 13277264871185218796838817)
  ·
    refine ⟨9957948653388914097629113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13277264871185218796838817 9957948653388914097629113)
    ·
      refine ⟨7468461490041685573221835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9957948653388914097629113 7468461490041685573221835)
      ·
        refine ⟨11202692235062528359832753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468461490041685573221835 11202692235062528359832753)
        ·
          refine ⟨8402019176296896269874565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11202692235062528359832753 8402019176296896269874565)
          ·
            refine ⟨1575378595555668050601481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8402019176296896269874565 1575378595555668050601481)
            ·
              refine ⟨1181533946666751037951111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575378595555668050601481 1181533946666751037951111)
              ·
                refine ⟨1772300920000126556926667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181533946666751037951111 1772300920000126556926667)
                ·
                  refine ⟨2658451380000189835390001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772300920000126556926667 2658451380000189835390001)
                  ·
                    refine ⟨1993838535000142376542501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2658451380000189835390001 1993838535000142376542501)
                    ·
                      refine ⟨373844725312526695601719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1993838535000142376542501 373844725312526695601719)
                      ·
                        rfl

theorem cell23_728060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_728060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728060 prefixEnd_728060 := by exact prefixLift 728060
  have htrace : WordTrace (prefixWord ++ tailWord_728060) baseStart_728060 baseEnd_728060 := by
    simpa [prefixWord, tailWord_728060, baseEnd_728060] using wordTrace_append hprefix tailTrace_728060
  have hstable : (prefixWord ++ tailWord_728060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728060).length < 2 ^ (prefixWord ++ tailWord_728060).sum := by decide
  have hdescent : baseEnd_728060 < baseStart_728060 := by decide
  rcases family_descends (prefixWord ++ tailWord_728060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
