import V185TrunkScan22Chunk441

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3940423 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 2, 3]
def baseStart_3940423 : Nat := 118140960795 + 3940423 * 2 ^ 59
def prefixEnd_3940423 : Nat := 4983230072969 + 3 ^ 40 * 3940423 * 2
def baseEnd_3940423 : Nat := 1348887320687694540393887

theorem tailTrace_3940423 : CollatzResearch.WordTrace tailWord_3940423 prefixEnd_3940423 1348887320687694540393887 := by
  unfold tailWord_3940423
  simp only [CollatzResearch.WordTrace]
  refine ⟨143719033803527916515577923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95812689202351944343718615 143719033803527916515577923)
  ·
    refine ⟨215578550705291874773366885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143719033803527916515577923 215578550705291874773366885)
    ·
      refine ⟨40420978257242226520006291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215578550705291874773366885 40420978257242226520006291)
      ·
        refine ⟨60631467385863339780009437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40420978257242226520006291 60631467385863339780009437)
        ·
          refine ⟨22736800269698752417503539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60631467385863339780009437 22736800269698752417503539)
          ·
            refine ⟨34105200404548128626255309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22736800269698752417503539 34105200404548128626255309)
            ·
              refine ⟨12789450151705548234845741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34105200404548128626255309 12789450151705548234845741)
              ·
                refine ⟨4796043806889580588067153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12789450151705548234845741 4796043806889580588067153)
                ·
                  refine ⟨3597032855167185441050365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4796043806889580588067153 3597032855167185441050365)
                  ·
                    refine ⟨1348887320687694540393887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3597032855167185441050365 1348887320687694540393887)
                    ·
                      rfl

theorem cell22_3940423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_3940423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940423 prefixEnd_3940423 := by exact prefixLift 3940423
  have htrace : WordTrace (prefixWord ++ tailWord_3940423) baseStart_3940423 baseEnd_3940423 := by
    simpa [prefixWord, tailWord_3940423, baseEnd_3940423] using wordTrace_append hprefix tailTrace_3940423
  have hstable : (prefixWord ++ tailWord_3940423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940423).length < 2 ^ (prefixWord ++ tailWord_3940423).sum := by decide
  have hdescent : baseEnd_3940423 < baseStart_3940423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940466 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_3940466 : Nat := 118140960795 + 3940466 * 2 ^ 59
def prefixEnd_3940466 : Nat := 4983230072969 + 3 ^ 40 * 3940466 * 2
def baseEnd_3940466 : Nat := 1348902040466456761568755

theorem tailTrace_3940466 : CollatzResearch.WordTrace tailWord_3940466 prefixEnd_3940466 1348902040466456761568755 := by
  unfold tailWord_3940466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35930150535593033714848313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95813734761581423239595501 35930150535593033714848313)
  ·
    refine ⟨26947612901694775286136235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35930150535593033714848313 26947612901694775286136235)
    ·
      refine ⟨40421419352542162929204353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26947612901694775286136235 40421419352542162929204353)
      ·
        refine ⟨30316064514406622196903265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40421419352542162929204353 30316064514406622196903265)
        ·
          refine ⟨22737048385804966647677449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30316064514406622196903265 22737048385804966647677449)
          ·
            refine ⟨17052786289353724985758087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22737048385804966647677449 17052786289353724985758087)
            ·
              refine ⟨25579179434030587478637131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17052786289353724985758087 25579179434030587478637131)
              ·
                refine ⟨38368769151045881217955697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25579179434030587478637131 38368769151045881217955697)
                ·
                  refine ⟨28776576863284410913466773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38368769151045881217955697 28776576863284410913466773)
                  ·
                    refine ⟨1348902040466456761568755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28776576863284410913466773 1348902040466456761568755)
                    ·
                      rfl

theorem cell22_3940466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_3940466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940466 prefixEnd_3940466 := by exact prefixLift 3940466
  have htrace : WordTrace (prefixWord ++ tailWord_3940466) baseStart_3940466 baseEnd_3940466 := by
    simpa [prefixWord, tailWord_3940466, baseEnd_3940466] using wordTrace_append hprefix tailTrace_3940466
  have hstable : (prefixWord ++ tailWord_3940466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940466).length < 2 ^ (prefixWord ++ tailWord_3940466).sum := by decide
  have hdescent : baseEnd_3940466 < baseStart_3940466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940601 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_3940601 : Nat := 118140960795 + 3940601 * 2 ^ 59
def prefixEnd_3940601 : Nat := 4983230072969 + 3 ^ 40 * 3940601 * 2
def baseEnd_3940601 : Nat := 1348948253725361409443341

theorem tailTrace_3940601 : CollatzResearch.WordTrace tailWord_3940601 prefixEnd_3940601 1348948253725361409443341 := by
  unfold tailWord_3940601
  simp only [CollatzResearch.WordTrace]
  refine ⟨143725525996883052915557657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95817017331255368610371771 143725525996883052915557657)
  ·
    refine ⟨107794144497662289686668243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143725525996883052915557657 107794144497662289686668243)
    ·
      refine ⟨161691216746493434530002365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107794144497662289686668243 161691216746493434530002365)
      ·
        refine ⟨60634206279935037948750887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161691216746493434530002365 60634206279935037948750887)
        ·
          refine ⟨90951309419902556923126331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60634206279935037948750887 90951309419902556923126331)
          ·
            refine ⟨136426964129853835384689497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90951309419902556923126331 136426964129853835384689497)
            ·
              refine ⟨102320223097390376538517123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136426964129853835384689497 102320223097390376538517123)
              ·
                refine ⟨153480334646085564807775685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102320223097390376538517123 153480334646085564807775685)
                ·
                  refine ⟨28777562746141043401457941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153480334646085564807775685 28777562746141043401457941)
                  ·
                    refine ⟨1348948253725361409443341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28777562746141043401457941 1348948253725361409443341)
                    ·
                      rfl

theorem cell22_3940601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_3940601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940601 prefixEnd_3940601 := by exact prefixLift 3940601
  have htrace : WordTrace (prefixWord ++ tailWord_3940601) baseStart_3940601 baseEnd_3940601 := by
    simpa [prefixWord, tailWord_3940601, baseEnd_3940601] using wordTrace_append hprefix tailTrace_3940601
  have hstable : (prefixWord ++ tailWord_3940601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940601).length < 2 ^ (prefixWord ++ tailWord_3940601).sum := by decide
  have hdescent : baseEnd_3940601 < baseStart_3940601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940654 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3940654 : Nat := 118140960795 + 3940654 * 2 ^ 59
def prefixEnd_3940654 : Nat := 4983230072969 + 3 ^ 40 * 3940654 * 2
def baseEnd_3940654 : Nat := 1348966396708486937868179

theorem tailTrace_3940654 : CollatzResearch.WordTrace tailWord_3940654 prefixEnd_3940654 1348966396708486937868179 := by
  unfold tailWord_3940654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17965932383211380370904627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95818306043794028644824677 17965932383211380370904627)
  ·
    refine ⟨26948898574817070556356941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17965932383211380370904627 26948898574817070556356941)
    ·
      refine ⟨10105836965556401458633853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26948898574817070556356941 10105836965556401458633853)
      ·
        refine ⟨3789688862083650546987695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10105836965556401458633853 3789688862083650546987695)
        ·
          refine ⟨5684533293125475820481543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3789688862083650546987695 5684533293125475820481543)
          ·
            refine ⟨8526799939688213730722315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5684533293125475820481543 8526799939688213730722315)
            ·
              refine ⟨12790199909532320596083473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8526799939688213730722315 12790199909532320596083473)
              ·
                refine ⟨9592649932149240447062605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12790199909532320596083473 9592649932149240447062605)
                ·
                  refine ⟨3597243724555965167648477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9592649932149240447062605 3597243724555965167648477)
                  ·
                    refine ⟨1348966396708486937868179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3597243724555965167648477 1348966396708486937868179)
                    ·
                      rfl

theorem cell22_3940654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3940654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940654 prefixEnd_3940654 := by exact prefixLift 3940654
  have htrace : WordTrace (prefixWord ++ tailWord_3940654) baseStart_3940654 baseEnd_3940654 := by
    simpa [prefixWord, tailWord_3940654, baseEnd_3940654] using wordTrace_append hprefix tailTrace_3940654
  have hstable : (prefixWord ++ tailWord_3940654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940654).length < 2 ^ (prefixWord ++ tailWord_3940654).sum := by decide
  have hdescent : baseEnd_3940654 < baseStart_3940654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940695 : List Nat := [1, 1, 3, 2, 3, 1, 1, 6, 4]
def baseStart_3940695 : Nat := 118140960795 + 3940695 * 2 ^ 59
def prefixEnd_3940695 : Nat := 4983230072969 + 3 ^ 40 * 3940695 * 2
def baseEnd_3940695 : Nat := 449660143948792165864351

theorem tailTrace_3940695 : CollatzResearch.WordTrace tailWord_3940695 prefixEnd_3940695 449660143948792165864351 := by
  unfold tailWord_3940695
  simp only [CollatzResearch.WordTrace]
  refine ⟨143728954458542506969479539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95819302972361671312986359 143728954458542506969479539)
  ·
    refine ⟨215593431687813760454219309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143728954458542506969479539 215593431687813760454219309)
    ·
      refine ⟨80847536882930160170332241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215593431687813760454219309 80847536882930160170332241)
      ·
        refine ⟨60635652662197620127749181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80847536882930160170332241 60635652662197620127749181)
        ·
          refine ⟨22738369748324107547905943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60635652662197620127749181 22738369748324107547905943)
          ·
            refine ⟨34107554622486161321858915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22738369748324107547905943 34107554622486161321858915)
            ·
              refine ⟨51161331933729241982788373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34107554622486161321858915 51161331933729241982788373)
              ·
                refine ⟨2398187434393558217943205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51161331933729241982788373 2398187434393558217943205)
                ·
                  refine ⟨449660143948792165864351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2398187434393558217943205 449660143948792165864351)
                  ·
                    rfl

theorem cell22_3940695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 4].length) (baseStart_3940695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940695 prefixEnd_3940695 := by exact prefixLift 3940695
  have htrace : WordTrace (prefixWord ++ tailWord_3940695) baseStart_3940695 baseEnd_3940695 := by
    simpa [prefixWord, tailWord_3940695, baseEnd_3940695] using wordTrace_append hprefix tailTrace_3940695
  have hstable : (prefixWord ++ tailWord_3940695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940695).length < 2 ^ (prefixWord ++ tailWord_3940695).sum := by decide
  have hdescent : baseEnd_3940695 < baseStart_3940695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940708 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_3940708 : Nat := 118140960795 + 3940708 * 2 ^ 59
def prefixEnd_3940708 : Nat := 4983230072969 + 3 ^ 40 * 3940708 * 2
def baseEnd_3940708 : Nat := 1348984882012048797018013

theorem tailTrace_3940708 : CollatzResearch.WordTrace tailWord_3940708 prefixEnd_3940708 1348984882012048797018013 := by
  unfold tailWord_3940708
  simp only [CollatzResearch.WordTrace]
  refine ⟨71864714303747705094851389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95819619071663606793135185 71864714303747705094851389)
  ·
    refine ⟨26949267863905389410569271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71864714303747705094851389 26949267863905389410569271)
    ·
      refine ⟨40423901795858084115853907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26949267863905389410569271 40423901795858084115853907)
      ·
        refine ⟨60635852693787126173780861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40423901795858084115853907 60635852693787126173780861)
        ·
          refine ⟨22738444760170172315167823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60635852693787126173780861 22738444760170172315167823)
          ·
            refine ⟨34107667140255258472751735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22738444760170172315167823 34107667140255258472751735)
            ·
              refine ⟨51161500710382887709127603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34107667140255258472751735 51161500710382887709127603)
              ·
                refine ⟨76742251065574331563691405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51161500710382887709127603 76742251065574331563691405)
                ·
                  refine ⟨28778344149590374336384277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76742251065574331563691405 28778344149590374336384277)
                  ·
                    refine ⟨1348984882012048797018013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28778344149590374336384277 1348984882012048797018013)
                    ·
                      rfl

theorem cell22_3940708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_3940708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940708 prefixEnd_3940708 := by exact prefixLift 3940708
  have htrace : WordTrace (prefixWord ++ tailWord_3940708) baseStart_3940708 baseEnd_3940708 := by
    simpa [prefixWord, tailWord_3940708, baseEnd_3940708] using wordTrace_append hprefix tailTrace_3940708
  have hstable : (prefixWord ++ tailWord_3940708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940708).length < 2 ^ (prefixWord ++ tailWord_3940708).sum := by decide
  have hdescent : baseEnd_3940708 < baseStart_3940708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940725 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3940725 : Nat := 118140960795 + 3940725 * 2 ^ 59
def prefixEnd_3940725 : Nat := 4983230072969 + 3 ^ 40 * 3940725 * 2
def baseEnd_3940725 : Nat := 1348990701459466419342961

theorem tailTrace_3940725 : CollatzResearch.WordTrace tailWord_3940725 prefixEnd_3940725 1348990701459466419342961 := by
  unfold tailWord_3940725
  simp only [CollatzResearch.WordTrace]
  refine ⟨143730048648433822093071629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95820032432289214728714419 143730048648433822093071629)
  ·
    refine ⟨53898768243162683284901861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143730048648433822093071629 53898768243162683284901861)
    ·
      refine ⟨10106019045593003115919099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53898768243162683284901861 10106019045593003115919099)
      ·
        refine ⟨15159028568389504673878649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10106019045593003115919099 15159028568389504673878649)
        ·
          refine ⟨11369271426292128505408987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15159028568389504673878649 11369271426292128505408987)
          ·
            refine ⟨17053907139438192758113481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11369271426292128505408987 17053907139438192758113481)
            ·
              refine ⟨12790430354578644568585111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17053907139438192758113481 12790430354578644568585111)
              ·
                refine ⟨19185645531867966852877667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12790430354578644568585111 19185645531867966852877667)
                ·
                  refine ⟨28778468297801950279316501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19185645531867966852877667 28778468297801950279316501)
                  ·
                    refine ⟨1348990701459466419342961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28778468297801950279316501 1348990701459466419342961)
                    ·
                      rfl

theorem cell22_3940725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3940725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940725 prefixEnd_3940725 := by exact prefixLift 3940725
  have htrace : WordTrace (prefixWord ++ tailWord_3940725) baseStart_3940725 baseEnd_3940725 := by
    simpa [prefixWord, tailWord_3940725, baseEnd_3940725] using wordTrace_append hprefix tailTrace_3940725
  have hstable : (prefixWord ++ tailWord_3940725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940725).length < 2 ^ (prefixWord ++ tailWord_3940725).sum := by decide
  have hdescent : baseEnd_3940725 < baseStart_3940725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940746 : List Nat := [3, 1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_3940746 : Nat := 118140960795 + 3940746 * 2 ^ 59
def prefixEnd_3940746 : Nat := 4983230072969 + 3 ^ 40 * 3940746 * 2
def baseEnd_3940746 : Nat := 449665963396209788189299

theorem tailTrace_3940746 : CollatzResearch.WordTrace tailWord_3940746 prefixEnd_3940746 449665963396209788189299 := by
  unfold tailWord_3940746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35932703645339435669896523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95820543054238495119724061 35932703645339435669896523)
  ·
    refine ⟨53899055468009153504844785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35932703645339435669896523 53899055468009153504844785)
    ·
      refine ⟨40424291601006865128633589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53899055468009153504844785 40424291601006865128633589)
      ·
        refine ⟨3789777337594393605809399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40424291601006865128633589 3789777337594393605809399)
        ·
          refine ⟨5684666006391590408714099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3789777337594393605809399 5684666006391590408714099)
          ·
            refine ⟨8526999009587385613071149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5684666006391590408714099 8526999009587385613071149)
            ·
              refine ⟨3197624628595269604901681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8526999009587385613071149 3197624628595269604901681)
              ·
                refine ⟨2398218471446452203676261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3197624628595269604901681 2398218471446452203676261)
                ·
                  refine ⟨449665963396209788189299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2398218471446452203676261 449665963396209788189299)
                  ·
                    rfl

theorem cell22_3940746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_3940746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940746 prefixEnd_3940746 := by exact prefixLift 3940746
  have htrace : WordTrace (prefixWord ++ tailWord_3940746) baseStart_3940746 baseEnd_3940746 := by
    simpa [prefixWord, tailWord_3940746, baseEnd_3940746] using wordTrace_append hprefix tailTrace_3940746
  have hstable : (prefixWord ++ tailWord_3940746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940746).length < 2 ^ (prefixWord ++ tailWord_3940746).sum := by decide
  have hdescent : baseEnd_3940746 < baseStart_3940746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940783 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 6, 5]
def baseStart_3940783 : Nat := 118140960795 + 3940783 * 2 ^ 59
def prefixEnd_3940783 : Nat := 4983230072969 + 3 ^ 40 * 3940783 * 2
def baseEnd_3940783 : Nat := 1349010556044773601392783

theorem tailTrace_3940783 : CollatzResearch.WordTrace tailWord_3940783 prefixEnd_3940783 1349010556044773601392783 := by
  unfold tailWord_3940783
  simp only [CollatzResearch.WordTrace]
  refine ⟨143732164082223697998683003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95821442721482465332455335 143732164082223697998683003)
  ·
    refine ⟨215598246123335546998024505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143732164082223697998683003 215598246123335546998024505)
    ·
      refine ⟨161698684592501660248518379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215598246123335546998024505 161698684592501660248518379)
      ·
        refine ⟨242548026888752490372777569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161698684592501660248518379 242548026888752490372777569)
        ·
          refine ⟨181911020166564367779583177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242548026888752490372777569 181911020166564367779583177)
          ·
            refine ⟨136433265124923275834687383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181911020166564367779583177 136433265124923275834687383)
            ·
              refine ⟨204649897687384913752031075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136433265124923275834687383 204649897687384913752031075)
              ·
                refine ⟨306974846531077370628046613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204649897687384913752031075 306974846531077370628046613)
                ·
                  refine ⟨14389445931144251748189685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 306974846531077370628046613 14389445931144251748189685)
                  ·
                    refine ⟨1349010556044773601392783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14389445931144251748189685 1349010556044773601392783)
                    ·
                      rfl

theorem cell22_3940783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_3940783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940783 prefixEnd_3940783 := by exact prefixLift 3940783
  have htrace : WordTrace (prefixWord ++ tailWord_3940783) baseStart_3940783 baseEnd_3940783 := by
    simpa [prefixWord, tailWord_3940783, baseEnd_3940783] using wordTrace_append hprefix tailTrace_3940783
  have hstable : (prefixWord ++ tailWord_3940783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940783).length < 2 ^ (prefixWord ++ tailWord_3940783).sum := by decide
  have hdescent : baseEnd_3940783 < baseStart_3940783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940860 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_3940860 : Nat := 118140960795 + 3940860 * 2 ^ 59
def prefixEnd_3940860 : Nat := 4983230072969 + 3 ^ 40 * 3940860 * 2
def baseEnd_3940860 : Nat := 1349036914718371067217547

theorem tailTrace_3940860 : CollatzResearch.WordTrace tailWord_3940860 prefixEnd_3940860 1349036914718371067217547 := by
  unfold tailWord_3940860
  simp only [CollatzResearch.WordTrace]
  refine ⟨71867486251472370074618017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95823315001963160099490689 71867486251472370074618017)
  ·
    refine ⟨53900614688604277555963513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71867486251472370074618017 53900614688604277555963513)
    ·
      refine ⟨40425461016453208166972635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53900614688604277555963513 40425461016453208166972635)
      ·
        refine ⟨60638191524679812250458953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40425461016453208166972635 60638191524679812250458953)
        ·
          refine ⟨45478643643509859187844215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60638191524679812250458953 45478643643509859187844215)
          ·
            refine ⟨68217965465264788781766323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45478643643509859187844215 68217965465264788781766323)
            ·
              refine ⟨102326948197897183172649485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68217965465264788781766323 102326948197897183172649485)
              ·
                refine ⟨38372605574211443689743557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102326948197897183172649485 38372605574211443689743557)
                ·
                  refine ⟨7194863545164645691826917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38372605574211443689743557 7194863545164645691826917)
                  ·
                    refine ⟨1349036914718371067217547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7194863545164645691826917 1349036914718371067217547)
                    ·
                      rfl

theorem cell22_3940860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_3940860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940860 prefixEnd_3940860 := by exact prefixLift 3940860
  have htrace : WordTrace (prefixWord ++ tailWord_3940860) baseStart_3940860 baseEnd_3940860 := by
    simpa [prefixWord, tailWord_3940860, baseEnd_3940860] using wordTrace_append hprefix tailTrace_3940860
  have hstable : (prefixWord ++ tailWord_3940860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940860).length < 2 ^ (prefixWord ++ tailWord_3940860).sum := by decide
  have hdescent : baseEnd_3940860 < baseStart_3940860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940892 : List Nat := [2, 2, 3, 1, 2, 2, 4, 6]
def baseStart_3940892 : Nat := 118140960795 + 3940892 * 2 ^ 59
def prefixEnd_3940892 : Nat := 4983230072969 + 3 ^ 40 * 3940892 * 2
def baseEnd_3940892 : Nat := 149894207663592627824161

theorem tailTrace_3940892 : CollatzResearch.WordTrace tailWord_3940892 prefixEnd_3940892 149894207663592627824161 := by
  unfold tailWord_3940892
  simp only [CollatzResearch.WordTrace]
  refine ⟨71868069819414404807200465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95824093092552539742933953 71868069819414404807200465)
  ·
    refine ⟨53901052364560803605400349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71868069819414404807200465 53901052364560803605400349)
    ·
      refine ⟨20212894636710301352025131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53901052364560803605400349 20212894636710301352025131)
      ·
        refine ⟨30319341955065452028037697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20212894636710301352025131 30319341955065452028037697)
        ·
          refine ⟨22739506466299089021028273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30319341955065452028037697 22739506466299089021028273)
          ·
            refine ⟨17054629849724316765771205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22739506466299089021028273 17054629849724316765771205)
            ·
              refine ⟨3197743096823309393582101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17054629849724316765771205 3197743096823309393582101)
              ·
                refine ⟨149894207663592627824161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3197743096823309393582101 149894207663592627824161)
                ·
                  rfl

theorem cell22_3940892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 6].length) (baseStart_3940892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940892 prefixEnd_3940892 := by exact prefixLift 3940892
  have htrace : WordTrace (prefixWord ++ tailWord_3940892) baseStart_3940892 baseEnd_3940892 := by
    simpa [prefixWord, tailWord_3940892, baseEnd_3940892] using wordTrace_append hprefix tailTrace_3940892
  have hstable : (prefixWord ++ tailWord_3940892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940892).length < 2 ^ (prefixWord ++ tailWord_3940892).sum := by decide
  have hdescent : baseEnd_3940892 < baseStart_3940892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940920 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 7]
def baseStart_3940920 : Nat := 118140960795 + 3940920 * 2 ^ 59
def prefixEnd_3940920 : Nat := 4983230072969 + 3 ^ 40 * 3940920 * 2
def baseEnd_3940920 : Nat := 449685817981516970239121

theorem tailTrace_3940920 : CollatzResearch.WordTrace tailWord_3940920 prefixEnd_3940920 449685817981516970239121 := by
  unfold tailWord_3940920
  simp only [CollatzResearch.WordTrace]
  refine ⟨71868580441363685198210107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95824773921818246930946809 71868580441363685198210107)
  ·
    refine ⟨107802870662045527797315161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71868580441363685198210107 107802870662045527797315161)
    ·
      refine ⟨80852152996534145847986371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107802870662045527797315161 80852152996534145847986371)
      ·
        refine ⟨121278229494801218771979557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80852152996534145847986371 121278229494801218771979557)
        ·
          refine ⟨22739668030275228519746167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121278229494801218771979557 22739668030275228519746167)
          ·
            refine ⟨34109502045412842779619251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22739668030275228519746167 34109502045412842779619251)
            ·
              refine ⟨51164253068119264169428877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34109502045412842779619251 51164253068119264169428877)
              ·
                refine ⟨19186594900544724063535829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51164253068119264169428877 19186594900544724063535829)
                ·
                  refine ⟨449685817981516970239121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19186594900544724063535829 449685817981516970239121)
                  ·
                    rfl

theorem cell22_3940920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_3940920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940920 prefixEnd_3940920 := by exact prefixLift 3940920
  have htrace : WordTrace (prefixWord ++ tailWord_3940920) baseStart_3940920 baseEnd_3940920 := by
    simpa [prefixWord, tailWord_3940920, baseEnd_3940920] using wordTrace_append hprefix tailTrace_3940920
  have hstable : (prefixWord ++ tailWord_3940920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940920).length < 2 ^ (prefixWord ++ tailWord_3940920).sum := by decide
  have hdescent : baseEnd_3940920 < baseStart_3940920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940924 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 3, 3]
def baseStart_3940924 : Nat := 118140960795 + 3940924 * 2 ^ 59
def prefixEnd_3940924 : Nat := 4983230072969 + 3 ^ 40 * 3940924 * 2
def baseEnd_3940924 : Nat := 1349058823226296233617351

theorem tailTrace_3940924 : CollatzResearch.WordTrace tailWord_3940924 prefixEnd_3940924 1349058823226296233617351 := by
  unfold tailWord_3940924
  simp only [CollatzResearch.WordTrace]
  refine ⟨71868653387356439539782913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95824871183141919386377217 71868653387356439539782913)
  ·
    refine ⟨53901490040517329654837185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71868653387356439539782913 53901490040517329654837185)
    ·
      refine ⟨40426117530387997241127889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53901490040517329654837185 40426117530387997241127889)
      ·
        refine ⟨30319588147790997930845917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40426117530387997241127889 30319588147790997930845917)
        ·
          refine ⟨11369845555421624224067219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30319588147790997930845917 11369845555421624224067219)
          ·
            refine ⟨17054768333132436336100829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11369845555421624224067219 17054768333132436336100829)
            ·
              refine ⟨6395538124924663626037811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17054768333132436336100829 6395538124924663626037811)
              ·
                refine ⟨9593307187386995439056717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6395538124924663626037811 9593307187386995439056717)
                ·
                  refine ⟨3597490195270123289646269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9593307187386995439056717 3597490195270123289646269)
                  ·
                    refine ⟨1349058823226296233617351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3597490195270123289646269 1349058823226296233617351)
                    ·
                      rfl

theorem cell22_3940924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_3940924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940924 prefixEnd_3940924 := by exact prefixLift 3940924
  have htrace : WordTrace (prefixWord ++ tailWord_3940924) baseStart_3940924 baseEnd_3940924 := by
    simpa [prefixWord, tailWord_3940924, baseEnd_3940924] using wordTrace_append hprefix tailTrace_3940924
  have hstable : (prefixWord ++ tailWord_3940924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940924).length < 2 ^ (prefixWord ++ tailWord_3940924).sum := by decide
  have hdescent : baseEnd_3940924 < baseStart_3940924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940997 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_3940997 : Nat := 118140960795 + 3940997 * 2 ^ 59
def prefixEnd_3940997 : Nat := 4983230072969 + 3 ^ 40 * 3940997 * 2
def baseEnd_3940997 : Nat := 1349083812618148376542127

theorem tailTrace_3940997 : CollatzResearch.WordTrace tailWord_3940997 prefixEnd_3940997 1349083812618148376542127 := by
  unfold tailWord_3940997
  simp only [CollatzResearch.WordTrace]
  refine ⟨143739969303448412546973245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95826646202298941697982163 143739969303448412546973245)
  ·
    refine ⟨53902488488793154705114967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143739969303448412546973245 53902488488793154705114967)
    ·
      refine ⟨80853732733189732057672451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53902488488793154705114967 80853732733189732057672451)
      ·
        refine ⟨121280599099784598086508677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80853732733189732057672451 121280599099784598086508677)
        ·
          refine ⟨22740112331209612141220377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121280599099784598086508677 22740112331209612141220377)
          ·
            refine ⟨17055084248407209105915283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22740112331209612141220377 17055084248407209105915283)
            ·
              refine ⟨25582626372610813658872925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17055084248407209105915283 25582626372610813658872925)
              ·
                refine ⟨9593484889729055122077347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25582626372610813658872925 9593484889729055122077347)
                ·
                  refine ⟨14390227334593582683116021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9593484889729055122077347 14390227334593582683116021)
                  ·
                    refine ⟨1349083812618148376542127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14390227334593582683116021 1349083812618148376542127)
                    ·
                      rfl

theorem cell22_3940997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_3940997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940997 prefixEnd_3940997 := by exact prefixLift 3940997
  have htrace : WordTrace (prefixWord ++ tailWord_3940997) baseStart_3940997 baseEnd_3940997 := by
    simpa [prefixWord, tailWord_3940997, baseEnd_3940997] using wordTrace_append hprefix tailTrace_3940997
  have hstable : (prefixWord ++ tailWord_3940997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940997).length < 2 ^ (prefixWord ++ tailWord_3940997).sum := by decide
  have hdescent : baseEnd_3940997 < baseStart_3940997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941106 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_3941106 : Nat := 118140960795 + 3941106 * 2 ^ 59
def prefixEnd_3941106 : Nat := 4983230072969 + 3 ^ 40 * 3941106 * 2
def baseEnd_3941106 : Nat := 449707041848569475188931

theorem tailTrace_3941106 : CollatzResearch.WordTrace tailWord_3941106 prefixEnd_3941106 449707041848569475188931 := by
  unfold tailWord_3941106
  simp only [CollatzResearch.WordTrace]
  refine ⟨35935986215013381040672793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95829296573369016108460781 35935986215013381040672793)
  ·
    refine ⟨26951989661260035780504595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35935986215013381040672793 26951989661260035780504595)
    ·
      refine ⟨40427984491890053670756893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26951989661260035780504595 40427984491890053670756893)
      ·
        refine ⟨15160494184458770126533835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40427984491890053670756893 15160494184458770126533835)
        ·
          refine ⟨22740741276688155189800753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15160494184458770126533835 22740741276688155189800753)
          ·
            refine ⟨17055555957516116392350565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22740741276688155189800753 17055555957516116392350565)
            ·
              refine ⟨3197916742034271823565731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17055555957516116392350565 3197916742034271823565731)
              ·
                refine ⟨4796875113051407735348597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197916742034271823565731 4796875113051407735348597)
                ·
                  refine ⟨449707041848569475188931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4796875113051407735348597 449707041848569475188931)
                  ·
                    rfl

theorem cell22_3941106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_3941106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941106 prefixEnd_3941106 := by exact prefixLift 3941106
  have htrace : WordTrace (prefixWord ++ tailWord_3941106) baseStart_3941106 baseEnd_3941106 := by
    simpa [prefixWord, tailWord_3941106, baseEnd_3941106] using wordTrace_append hprefix tailTrace_3941106
  have hstable : (prefixWord ++ tailWord_3941106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941106).length < 2 ^ (prefixWord ++ tailWord_3941106).sum := by decide
  have hdescent : baseEnd_3941106 < baseStart_3941106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941117 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 8]
def baseStart_3941117 : Nat := 118140960795 + 3941117 * 2 ^ 59
def prefixEnd_3941117 : Nat := 4983230072969 + 3 ^ 40 * 3941117 * 2
def baseEnd_3941117 : Nat := 449708297023502687847253

theorem tailTrace_3941117 : CollatzResearch.WordTrace tailWord_3941117 prefixEnd_3941117 449708297023502687847253 := by
  unfold tailWord_3941117
  simp only [CollatzResearch.WordTrace]
  refine ⟨143744346063013673041341605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95829564042009115360894403 143744346063013673041341605)
  ·
    refine ⟨26952064886815063695251551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143744346063013673041341605 26952064886815063695251551)
    ·
      refine ⟨40428097330222595542877327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26952064886815063695251551 40428097330222595542877327)
      ·
        refine ⟨60642145995333893314315991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40428097330222595542877327 60642145995333893314315991)
        ·
          refine ⟨90963218993000839971473987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60642145995333893314315991 90963218993000839971473987)
          ·
            refine ⟨136444828489501259957210981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90963218993000839971473987 136444828489501259957210981)
            ·
              refine ⟨25583405341781486241977059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136444828489501259957210981 25583405341781486241977059)
              ·
                refine ⟨38375108012672229362965589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25583405341781486241977059 38375108012672229362965589)
                ·
                  refine ⟨449708297023502687847253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38375108012672229362965589 449708297023502687847253)
                  ·
                    rfl

theorem cell22_3941117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_3941117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941117 prefixEnd_3941117 := by exact prefixLift 3941117
  have htrace : WordTrace (prefixWord ++ tailWord_3941117) baseStart_3941117 baseEnd_3941117 := by
    simpa [prefixWord, tailWord_3941117, baseEnd_3941117] using wordTrace_append hprefix tailTrace_3941117
  have hstable : (prefixWord ++ tailWord_3941117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941117).length < 2 ^ (prefixWord ++ tailWord_3941117).sum := by decide
  have hdescent : baseEnd_3941117 < baseStart_3941117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941151 : List Nat := [1, 1, 2, 4, 2, 3, 1, 4, 4]
def baseStart_3941151 : Nat := 118140960795 + 3941151 * 2 ^ 59
def prefixEnd_3941151 : Nat := 4983230072969 + 3 ^ 40 * 3941151 * 2
def baseEnd_3941151 : Nat := 449712176655114436063885

theorem tailTrace_3941151 : CollatzResearch.WordTrace tailWord_3941151 prefixEnd_3941151 449712176655114436063885 := by
  unfold tailWord_3941151
  simp only [CollatzResearch.WordTrace]
  refine ⟨143745586144890496848079307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95830390763260331232052871 143745586144890496848079307)
  ·
    refine ⟨215618379217335745272118961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143745586144890496848079307 215618379217335745272118961)
    ·
      refine ⟨161713784413001808954089221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215618379217335745272118961 161713784413001808954089221)
      ·
        refine ⟨30321334577437839178891729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161713784413001808954089221 30321334577437839178891729)
        ·
          refine ⟨22741000933078379384168797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30321334577437839178891729 22741000933078379384168797)
          ·
            refine ⟨8527875349904392269063299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22741000933078379384168797 8527875349904392269063299)
            ·
              refine ⟨12791813024856588403594949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8527875349904392269063299 12791813024856588403594949)
              ·
                refine ⟨2398464942160610325674053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12791813024856588403594949 2398464942160610325674053)
                ·
                  refine ⟨449712176655114436063885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2398464942160610325674053 449712176655114436063885)
                  ·
                    rfl

theorem cell22_3941151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 4].length) (baseStart_3941151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941151 prefixEnd_3941151 := by exact prefixLift 3941151
  have htrace : WordTrace (prefixWord ++ tailWord_3941151) baseStart_3941151 baseEnd_3941151 := by
    simpa [prefixWord, tailWord_3941151, baseEnd_3941151] using wordTrace_append hprefix tailTrace_3941151
  have hstable : (prefixWord ++ tailWord_3941151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941151).length < 2 ^ (prefixWord ++ tailWord_3941151).sum := by decide
  have hdescent : baseEnd_3941151 < baseStart_3941151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941166 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3941166 : Nat := 118140960795 + 3941166 * 2 ^ 59
def prefixEnd_3941166 : Nat := 4983230072969 + 3 ^ 40 * 3941166 * 2
def baseEnd_3941166 : Nat := 1349141664771888269066609

theorem tailTrace_3941166 : CollatzResearch.WordTrace tailWord_3941166 prefixEnd_3941166 1349141664771888269066609 := by
  unfold tailWord_3941166
  simp only [CollatzResearch.WordTrace]
  refine ⟨17968266654979519301234419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95830755493224102939916901 17968266654979519301234419)
  ·
    refine ⟨26952399982469278951851629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17968266654979519301234419 26952399982469278951851629)
    ·
      refine ⟨10107149993425979606944361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26952399982469278951851629 10107149993425979606944361)
      ·
        refine ⟨7580362495069484705208271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10107149993425979606944361 7580362495069484705208271)
        ·
          refine ⟨11370543742604227057812407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7580362495069484705208271 11370543742604227057812407)
          ·
            refine ⟨17055815613906340586718611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11370543742604227057812407 17055815613906340586718611)
            ·
              refine ⟨25583723420859510880077917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17055815613906340586718611 25583723420859510880077917)
              ·
                refine ⟨9593896282822316580029219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25583723420859510880077917 9593896282822316580029219)
                ·
                  refine ⟨14390844424233474870043829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9593896282822316580029219 14390844424233474870043829)
                  ·
                    refine ⟨1349141664771888269066609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14390844424233474870043829 1349141664771888269066609)
                    ·
                      rfl

theorem cell22_3941166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3941166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941166 prefixEnd_3941166 := by exact prefixLift 3941166
  have htrace : WordTrace (prefixWord ++ tailWord_3941166) baseStart_3941166 baseEnd_3941166 := by
    simpa [prefixWord, tailWord_3941166, baseEnd_3941166] using wordTrace_append hprefix tailTrace_3941166
  have hstable : (prefixWord ++ tailWord_3941166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941166).length < 2 ^ (prefixWord ++ tailWord_3941166).sum := by decide
  have hdescent : baseEnd_3941166 < baseStart_3941166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941181 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3941181 : Nat := 118140960795 + 3941181 * 2 ^ 59
def prefixEnd_3941181 : Nat := 4983230072969 + 3 ^ 40 * 3941181 * 2
def baseEnd_3941181 : Nat := 1349146799578433229941563

theorem tailTrace_3941181 : CollatzResearch.WordTrace tailWord_3941181 prefixEnd_3941181 1349146799578433229941563 := by
  unfold tailWord_3941181
  simp only [CollatzResearch.WordTrace]
  refine ⟨143746680334781811971671397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95831120223187874647780931 143746680334781811971671397)
  ·
    refine ⟨26952502562771589744688387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143746680334781811971671397 26952502562771589744688387)
    ·
      refine ⟨40428753844157384617032581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26952502562771589744688387 40428753844157384617032581)
      ·
        refine ⟨7580391345779509615693609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40428753844157384617032581 7580391345779509615693609)
        ·
          refine ⟨5685293509334632211770207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7580391345779509615693609 5685293509334632211770207)
          ·
            refine ⟨8527940264001948317655311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685293509334632211770207 8527940264001948317655311)
            ·
              refine ⟨12791910396002922476482967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8527940264001948317655311 12791910396002922476482967)
              ·
                refine ⟨19187865594004383714724451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12791910396002922476482967 19187865594004383714724451)
                ·
                  refine ⟨28781798391006575572086677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19187865594004383714724451 28781798391006575572086677)
                  ·
                    refine ⟨1349146799578433229941563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28781798391006575572086677 1349146799578433229941563)
                    ·
                      rfl

theorem cell22_3941181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3941181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941181 prefixEnd_3941181 := by exact prefixLift 3941181
  have htrace : WordTrace (prefixWord ++ tailWord_3941181) baseStart_3941181 baseEnd_3941181 := by
    simpa [prefixWord, tailWord_3941181, baseEnd_3941181] using wordTrace_append hprefix tailTrace_3941181
  have hstable : (prefixWord ++ tailWord_3941181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941181).length < 2 ^ (prefixWord ++ tailWord_3941181).sum := by decide
  have hdescent : baseEnd_3941181 < baseStart_3941181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941185 : List Nat := [1, 2, 5, 3, 1, 1, 2, 3, 4]
def baseStart_3941185 : Nat := 118140960795 + 3941185 * 2 ^ 59
def prefixEnd_3941185 : Nat := 4983230072969 + 3 ^ 40 * 3941185 * 2
def baseEnd_3941185 : Nat := 449716056286726184280517

theorem tailTrace_3941185 : CollatzResearch.WordTrace tailWord_3941185 prefixEnd_3941185 449716056286726184280517 := by
  unfold tailWord_3941185
  simp only [CollatzResearch.WordTrace]
  refine ⟨143746826226767320654817009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95831217484511547103211339 143746826226767320654817009)
  ·
    refine ⟨107810119670075490491112757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143746826226767320654817009 107810119670075490491112757)
    ·
      refine ⟨10107198719069577233541821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107810119670075490491112757 10107198719069577233541821)
      ·
        refine ⟨3790199519651091462578183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10107198719069577233541821 3790199519651091462578183)
        ·
          refine ⟨5685299279476637193867275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790199519651091462578183 5685299279476637193867275)
          ·
            refine ⟨8527948919214955790800913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685299279476637193867275 8527948919214955790800913)
            ·
              refine ⟨6395961689411216843100685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8527948919214955790800913 6395961689411216843100685)
              ·
                refine ⟨2398485633529206316162757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6395961689411216843100685 2398485633529206316162757)
                ·
                  refine ⟨449716056286726184280517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2398485633529206316162757 449716056286726184280517)
                  ·
                    rfl

theorem cell22_3941185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 4].length) (baseStart_3941185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941185 prefixEnd_3941185 := by exact prefixLift 3941185
  have htrace : WordTrace (prefixWord ++ tailWord_3941185) baseStart_3941185 baseEnd_3941185 := by
    simpa [prefixWord, tailWord_3941185, baseEnd_3941185] using wordTrace_append hprefix tailTrace_3941185
  have hstable : (prefixWord ++ tailWord_3941185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941185).length < 2 ^ (prefixWord ++ tailWord_3941185).sum := by decide
  have hdescent : baseEnd_3941185 < baseStart_3941185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941230 : List Nat := [4, 1, 2, 3, 3, 1, 2, 6]
def baseStart_3941230 : Nat := 118140960795 + 3941230 * 2 ^ 59
def prefixEnd_3941230 : Nat := 4983230072969 + 3 ^ 40 * 3941230 * 2
def baseEnd_3941230 : Nat := 149907063697757048385157

theorem tailTrace_3941230 : CollatzResearch.WordTrace tailWord_3941230 prefixEnd_3941230 149907063697757048385157 := by
  unfold tailWord_3941230
  simp only [CollatzResearch.WordTrace]
  refine ⟨17968558438950536667525643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95832311674402862226803429 17968558438950536667525643)
  ·
    refine ⟨26952837658425805001288465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17968558438950536667525643 26952837658425805001288465)
    ·
      refine ⟨20214628243819353750966349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26952837658425805001288465 20214628243819353750966349)
      ·
        refine ⟨7580485591432257656612381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20214628243819353750966349 7580485591432257656612381)
        ·
          refine ⟨2842682096787096621229643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7580485591432257656612381 2842682096787096621229643)
          ·
            refine ⟨4264023145180644931844465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842682096787096621229643 4264023145180644931844465)
            ·
              refine ⟨3198017358885483698883349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264023145180644931844465 3198017358885483698883349)
              ·
                refine ⟨149907063697757048385157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3198017358885483698883349 149907063697757048385157)
                ·
                  rfl

theorem cell22_3941230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_3941230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941230 prefixEnd_3941230 := by exact prefixLift 3941230
  have htrace : WordTrace (prefixWord ++ tailWord_3941230) baseStart_3941230 baseEnd_3941230 := by
    simpa [prefixWord, tailWord_3941230, baseEnd_3941230] using wordTrace_append hprefix tailTrace_3941230
  have hstable : (prefixWord ++ tailWord_3941230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941230).length < 2 ^ (prefixWord ++ tailWord_3941230).sum := by decide
  have hdescent : baseEnd_3941230 < baseStart_3941230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941301 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3941301 : Nat := 118140960795 + 3941301 * 2 ^ 59
def prefixEnd_3941301 : Nat := 4983230072969 + 3 ^ 40 * 3941301 * 2
def baseEnd_3941301 : Nat := 1349187878030792916941195

theorem tailTrace_3941301 : CollatzResearch.WordTrace tailWord_3941301 prefixEnd_3941301 1349187878030792916941195 := by
  unfold tailWord_3941301
  simp only [CollatzResearch.WordTrace]
  refine ⟨143751057094347072466039757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95834038062898048310693171 143751057094347072466039757)
  ·
    refine ⟨53906646410380152174764909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143751057094347072466039757 53906646410380152174764909)
    ·
      refine ⟨20214992403892557065536841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53906646410380152174764909 20214992403892557065536841)
      ·
        refine ⟨15161244302919417799152631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20214992403892557065536841 15161244302919417799152631)
        ·
          refine ⟨22741866454379126698728947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15161244302919417799152631 22741866454379126698728947)
          ·
            refine ⟨34112799681568690048093421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22741866454379126698728947 34112799681568690048093421)
            ·
              refine ⟨12792299880588258768035033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34112799681568690048093421 12792299880588258768035033)
              ·
                refine ⟨9594224910441194076026275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12792299880588258768035033 9594224910441194076026275)
                ·
                  refine ⟨14391337365661791114039413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9594224910441194076026275 14391337365661791114039413)
                  ·
                    refine ⟨1349187878030792916941195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14391337365661791114039413 1349187878030792916941195)
                    ·
                      rfl

theorem cell22_3941301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3941301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941301 prefixEnd_3941301 := by exact prefixLift 3941301
  have htrace : WordTrace (prefixWord ++ tailWord_3941301) baseStart_3941301 baseEnd_3941301 := by
    simpa [prefixWord, tailWord_3941301, baseEnd_3941301] using wordTrace_append hprefix tailTrace_3941301
  have hstable : (prefixWord ++ tailWord_3941301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941301).length < 2 ^ (prefixWord ++ tailWord_3941301).sum := by decide
  have hdescent : baseEnd_3941301 < baseStart_3941301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941496 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_3941496 : Nat := 118140960795 + 3941496 * 2 ^ 59
def prefixEnd_3941496 : Nat := 4983230072969 + 3 ^ 40 * 3941496 * 2
def baseEnd_3941496 : Nat := 1349254630515877408315597

theorem tailTrace_3941496 : CollatzResearch.WordTrace tailWord_3941496 prefixEnd_3941496 1349254630515877408315597 := by
  unfold tailWord_3941496
  simp only [CollatzResearch.WordTrace]
  refine ⟨71879084664320310384694171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95838779552427080512925561 71879084664320310384694171)
  ·
    refine ⟨107818626996480465577041257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71879084664320310384694171 107818626996480465577041257)
    ·
      refine ⟨80863970247360349182780943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107818626996480465577041257 80863970247360349182780943)
      ·
        refine ⟨121295955371040523774171415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80863970247360349182780943 121295955371040523774171415)
        ·
          refine ⟨181943933056560785661257123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121295955371040523774171415 181943933056560785661257123)
          ·
            refine ⟨272915899584841178491885685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181943933056560785661257123 272915899584841178491885685)
            ·
              refine ⟨25585865586078860483614283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272915899584841178491885685 25585865586078860483614283)
              ·
                refine ⟨38378798379118290725421425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25585865586078860483614283 38378798379118290725421425)
                ·
                  refine ⟨28784098784338718044066069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38378798379118290725421425 28784098784338718044066069)
                  ·
                    refine ⟨1349254630515877408315597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28784098784338718044066069 1349254630515877408315597)
                    ·
                      rfl

theorem cell22_3941496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_3941496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941496 prefixEnd_3941496 := by exact prefixLift 3941496
  have htrace : WordTrace (prefixWord ++ tailWord_3941496) baseStart_3941496 baseEnd_3941496 := by
    simpa [prefixWord, tailWord_3941496, baseEnd_3941496] using wordTrace_append hprefix tailTrace_3941496
  have hstable : (prefixWord ++ tailWord_3941496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941496).length < 2 ^ (prefixWord ++ tailWord_3941496).sum := by decide
  have hdescent : baseEnd_3941496 < baseStart_3941496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941511 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 9]
def baseStart_3941511 : Nat := 118140960795 + 3941511 * 2 ^ 59
def prefixEnd_3941511 : Nat := 4983230072969 + 3 ^ 40 * 3941511 * 2
def baseEnd_3941511 : Nat := 449753255107474123063517

theorem tailTrace_3941511 : CollatzResearch.WordTrace tailWord_3941511 prefixEnd_3941511 449753255107474123063517 := by
  unfold tailWord_3941511
  simp only [CollatzResearch.WordTrace]
  refine ⟨143758716423586278331184387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95839144282390852220789591 143758716423586278331184387)
  ·
    refine ⟨215638074635379417496776581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143758716423586278331184387 215638074635379417496776581)
    ·
      refine ⟨40432138994133640780645609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215638074635379417496776581 40432138994133640780645609)
      ·
        refine ⟨30324104245600230585484207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40432138994133640780645609 30324104245600230585484207)
        ·
          refine ⟨45486156368400345878226311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30324104245600230585484207 45486156368400345878226311)
          ·
            refine ⟨68229234552600518817339467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45486156368400345878226311 68229234552600518817339467)
            ·
              refine ⟨102343851828900778226009201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68229234552600518817339467 102343851828900778226009201)
              ·
                refine ⟨76757888871675583669506901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102343851828900778226009201 76757888871675583669506901)
                ·
                  refine ⟨449753255107474123063517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76757888871675583669506901 449753255107474123063517)
                  ·
                    rfl

theorem cell22_3941511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 9].length) (baseStart_3941511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941511 prefixEnd_3941511 := by exact prefixLift 3941511
  have htrace : WordTrace (prefixWord ++ tailWord_3941511) baseStart_3941511 baseEnd_3941511 := by
    simpa [prefixWord, tailWord_3941511, baseEnd_3941511] using wordTrace_append hprefix tailTrace_3941511
  have hstable : (prefixWord ++ tailWord_3941511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941511).length < 2 ^ (prefixWord ++ tailWord_3941511).sum := by decide
  have hdescent : baseEnd_3941511 < baseStart_3941511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941532 : List Nat := [2, 2, 3, 2, 1, 2, 1, 5, 1, 3]
def baseStart_3941532 : Nat := 118140960795 + 3941532 * 2 ^ 59
def prefixEnd_3941532 : Nat := 4983230072969 + 3 ^ 40 * 3941532 * 2
def baseEnd_3941532 : Nat := 1349266954051585314415487

theorem tailTrace_3941532 : CollatzResearch.WordTrace tailWord_3941532 prefixEnd_3941532 1349266954051585314415487 := by
  unfold tailWord_3941532
  simp only [CollatzResearch.WordTrace]
  refine ⟨71879741178255099458849425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95839654904340132611799233 71879741178255099458849425)
  ·
    refine ⟨53909805883691324594137069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71879741178255099458849425 53909805883691324594137069)
    ·
      refine ⟨20216177206384246722801401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53909805883691324594137069 20216177206384246722801401)
      ·
        refine ⟨15162132904788185042101051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20216177206384246722801401 15162132904788185042101051)
        ·
          refine ⟨22743199357182277563151577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15162132904788185042101051 22743199357182277563151577)
          ·
            refine ⟨17057399517886708172363683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22743199357182277563151577 17057399517886708172363683)
            ·
              refine ⟨25586099276830062258545525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17057399517886708172363683 25586099276830062258545525)
              ·
                refine ⟨2398696807202818336738643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25586099276830062258545525 2398696807202818336738643)
                ·
                  refine ⟨3598045210804227505107965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398696807202818336738643 3598045210804227505107965)
                  ·
                    refine ⟨1349266954051585314415487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3598045210804227505107965 1349266954051585314415487)
                    ·
                      rfl

theorem cell22_3941532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_3941532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941532 prefixEnd_3941532 := by exact prefixLift 3941532
  have htrace : WordTrace (prefixWord ++ tailWord_3941532) baseStart_3941532 baseEnd_3941532 := by
    simpa [prefixWord, tailWord_3941532, baseEnd_3941532] using wordTrace_append hprefix tailTrace_3941532
  have hstable : (prefixWord ++ tailWord_3941532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941532).length < 2 ^ (prefixWord ++ tailWord_3941532).sum := by decide
  have hdescent : baseEnd_3941532 < baseStart_3941532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941607 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 6]
def baseStart_3941607 : Nat := 118140960795 + 3941607 * 2 ^ 59
def prefixEnd_3941607 : Nat := 4983230072969 + 3 ^ 40 * 3941607 * 2
def baseEnd_3941607 : Nat := 449764209361436706263419

theorem tailTrace_3941607 : CollatzResearch.WordTrace tailWord_3941607 prefixEnd_3941607 449764209361436706263419 := by
  unfold tailWord_3941607
  simp only [CollatzResearch.WordTrace]
  refine ⟨143762217831238486726679075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95841478554158991151119383 143762217831238486726679075)
  ·
    refine ⟨215643326746857730090018613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143762217831238486726679075 215643326746857730090018613)
    ·
      refine ⟨20216561882517912195939245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215643326746857730090018613 20216561882517912195939245)
      ·
        refine ⟨7581210705944217073477217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20216561882517912195939245 7581210705944217073477217)
        ·
          refine ⟨5685908029458162805107913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7581210705944217073477217 5685908029458162805107913)
          ·
            refine ⟨4264431022093622103830935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5685908029458162805107913 4264431022093622103830935)
            ·
              refine ⟨6396646533140433155746403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264431022093622103830935 6396646533140433155746403)
              ·
                refine ⟨9594969799710649733619605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6396646533140433155746403 9594969799710649733619605)
                ·
                  refine ⟨449764209361436706263419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9594969799710649733619605 449764209361436706263419)
                  ·
                    rfl

theorem cell22_3941607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 6].length) (baseStart_3941607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941607 prefixEnd_3941607 := by exact prefixLift 3941607
  have htrace : WordTrace (prefixWord ++ tailWord_3941607) baseStart_3941607 baseEnd_3941607 := by
    simpa [prefixWord, tailWord_3941607, baseEnd_3941607] using wordTrace_append hprefix tailTrace_3941607
  have hstable : (prefixWord ++ tailWord_3941607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941607).length < 2 ^ (prefixWord ++ tailWord_3941607).sum := by decide
  have hdescent : baseEnd_3941607 < baseStart_3941607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941755 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 2, 4]
def baseStart_3941755 : Nat := 118140960795 + 3941755 * 2 ^ 59
def prefixEnd_3941755 : Nat := 4983230072969 + 3 ^ 40 * 3941755 * 2
def baseEnd_3941755 : Nat := 1349343291508887066089803

theorem tailTrace_3941755 : CollatzResearch.WordTrace tailWord_3941755 prefixEnd_3941755 1349343291508887066089803 := by
  unfold tailWord_3941755
  simp only [CollatzResearch.WordTrace]
  refine ⟨143767615834702308003066719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95845077223134872002044479 143767615834702308003066719)
  ·
    refine ⟨215651423752053462004600079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143767615834702308003066719 215651423752053462004600079)
    ·
      refine ⟨323477135628080193006900119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215651423752053462004600079 323477135628080193006900119)
      ·
        refine ⟨485215703442120289510350179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323477135628080193006900119 485215703442120289510350179)
        ·
          refine ⟨727823555163180434265525269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485215703442120289510350179 727823555163180434265525269)
          ·
            refine ⟨34116729148274082856196497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 727823555163180434265525269 34116729148274082856196497)
            ·
              refine ⟨25587546861205562142147373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34116729148274082856196497 25587546861205562142147373)
              ·
                refine ⟨9595330072952085803305265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25587546861205562142147373 9595330072952085803305265)
                ·
                  refine ⟨7196497554714064352478949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9595330072952085803305265 7196497554714064352478949)
                  ·
                    refine ⟨1349343291508887066089803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7196497554714064352478949 1349343291508887066089803)
                    ·
                      rfl

theorem cell22_3941755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 4].length) (baseStart_3941755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941755 prefixEnd_3941755 := by exact prefixLift 3941755
  have htrace : WordTrace (prefixWord ++ tailWord_3941755) baseStart_3941755 baseEnd_3941755 := by
    simpa [prefixWord, tailWord_3941755, baseEnd_3941755] using wordTrace_append hprefix tailTrace_3941755
  have hstable : (prefixWord ++ tailWord_3941755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941755).length < 2 ^ (prefixWord ++ tailWord_3941755).sum := by decide
  have hdescent : baseEnd_3941755 < baseStart_3941755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941791 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 2, 3]
def baseStart_3941791 : Nat := 118140960795 + 3941791 * 2 ^ 59
def prefixEnd_3941791 : Nat := 4983230072969 + 3 ^ 40 * 3941791 * 2
def baseEnd_3941791 : Nat := 1349355615044594972189693

theorem tailTrace_3941791 : CollatzResearch.WordTrace tailWord_3941791 prefixEnd_3941791 1349355615044594972189693 := by
  unfold tailWord_3941791
  simp only [CollatzResearch.WordTrace]
  refine ⟨143768928862571886151377227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95845952575047924100918151 143768928862571886151377227)
  ·
    refine ⟨215653393293857829227065841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143768928862571886151377227 215653393293857829227065841)
    ·
      refine ⟨161740044970393371920299381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215653393293857829227065841 161740044970393371920299381)
      ·
        refine ⟨15163129215974378617528067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161740044970393371920299381 15163129215974378617528067)
        ·
          refine ⟨22744693823961567926292101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15163129215974378617528067 22744693823961567926292101)
          ·
            refine ⟨4264630091992793986179769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22744693823961567926292101 4264630091992793986179769)
            ·
              refine ⟨3198472568994595489634827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264630091992793986179769 3198472568994595489634827)
              ·
                refine ⟨4797708853491893234452241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3198472568994595489634827 4797708853491893234452241)
                ·
                  refine ⟨3598281640118919925839181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4797708853491893234452241 3598281640118919925839181)
                  ·
                    refine ⟨1349355615044594972189693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3598281640118919925839181 1349355615044594972189693)
                    ·
                      rfl

theorem cell22_3941791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 2, 3].length) (baseStart_3941791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941791 prefixEnd_3941791 := by exact prefixLift 3941791
  have htrace : WordTrace (prefixWord ++ tailWord_3941791) baseStart_3941791 baseEnd_3941791 := by
    simpa [prefixWord, tailWord_3941791, baseEnd_3941791] using wordTrace_append hprefix tailTrace_3941791
  have hstable : (prefixWord ++ tailWord_3941791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941791).length < 2 ^ (prefixWord ++ tailWord_3941791).sum := by decide
  have hdescent : baseEnd_3941791 < baseStart_3941791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941832 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 5]
def baseStart_3941832 : Nat := 118140960795 + 3941832 * 2 ^ 59
def prefixEnd_3941832 : Nat := 4983230072969 + 3 ^ 40 * 3941832 * 2
def baseEnd_3941832 : Nat := 449789883394161510638189

theorem tailTrace_3941832 : CollatzResearch.WordTrace tailWord_3941832 prefixEnd_3941832 449789883394161510638189 := by
  unfold tailWord_3941832
  simp only [CollatzResearch.WordTrace]
  refine ⟨71885212127711675076809875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95846949503615566769079833 71885212127711675076809875)
  ·
    refine ⟨107827818191567512615214813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71885212127711675076809875 107827818191567512615214813)
    ·
      refine ⟨40435431821837817230705555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107827818191567512615214813 40435431821837817230705555)
      ·
        refine ⟨60653147732756725846058333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40435431821837817230705555 60653147732756725846058333)
        ·
          refine ⟨22744930399783772192271875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60653147732756725846058333 22744930399783772192271875)
          ·
            refine ⟨34117395599675658288407813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22744930399783772192271875 34117395599675658288407813)
            ·
              refine ⟨6397011674939185929076465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34117395599675658288407813 6397011674939185929076465)
              ·
                refine ⟨4797758756204389446807349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6397011674939185929076465 4797758756204389446807349)
                ·
                  refine ⟨449789883394161510638189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4797758756204389446807349 449789883394161510638189)
                  ·
                    rfl

theorem cell22_3941832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_3941832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941832 prefixEnd_3941832 := by exact prefixLift 3941832
  have htrace : WordTrace (prefixWord ++ tailWord_3941832) baseStart_3941832 baseEnd_3941832 := by
    simpa [prefixWord, tailWord_3941832, baseEnd_3941832] using wordTrace_append hprefix tailTrace_3941832
  have hstable : (prefixWord ++ tailWord_3941832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941832).length < 2 ^ (prefixWord ++ tailWord_3941832).sum := by decide
  have hdescent : baseEnd_3941832 < baseStart_3941832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941836 : List Nat := [2, 2, 1, 4, 2, 2, 1, 4, 1, 3]
def baseStart_3941836 : Nat := 118140960795 + 3941836 * 2 ^ 59
def prefixEnd_3941836 : Nat := 4983230072969 + 3 ^ 40 * 3941836 * 2
def baseEnd_3941836 : Nat := 1349371019464229854814555

theorem tailTrace_3941836 : CollatzResearch.WordTrace tailWord_3941836 prefixEnd_3941836 1349371019464229854814555 := by
  unfold tailWord_3941836
  simp only [CollatzResearch.WordTrace]
  refine ⟨71885285073704429418382681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95847046764939239224510241 71885285073704429418382681)
  ·
    refine ⟨53913963805278322063787011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71885285073704429418382681 53913963805278322063787011)
    ·
      refine ⟨80870945707917483095680517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53913963805278322063787011 80870945707917483095680517)
      ·
        refine ⟨15163302320234528080440097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80870945707917483095680517 15163302320234528080440097)
        ·
          refine ⟨11372476740175896060330073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15163302320234528080440097 11372476740175896060330073)
          ·
            refine ⟨8529357555131922045247555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11372476740175896060330073 8529357555131922045247555)
            ·
              refine ⟨12794036332697883067871333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529357555131922045247555 12794036332697883067871333)
              ·
                refine ⟨2398881812380853075225875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12794036332697883067871333 2398881812380853075225875)
                ·
                  refine ⟨3598322718571279612838813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398881812380853075225875 3598322718571279612838813)
                  ·
                    refine ⟨1349371019464229854814555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3598322718571279612838813 1349371019464229854814555)
                    ·
                      rfl

theorem cell22_3941836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_3941836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941836 prefixEnd_3941836 := by exact prefixLift 3941836
  have htrace : WordTrace (prefixWord ++ tailWord_3941836) baseStart_3941836 baseEnd_3941836 := by
    simpa [prefixWord, tailWord_3941836, baseEnd_3941836] using wordTrace_append hprefix tailTrace_3941836
  have hstable : (prefixWord ++ tailWord_3941836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941836).length < 2 ^ (prefixWord ++ tailWord_3941836).sum := by decide
  have hdescent : baseEnd_3941836 < baseStart_3941836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941875 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 3, 5]
def baseStart_3941875 : Nat := 118140960795 + 3941875 * 2 ^ 59
def prefixEnd_3941875 : Nat := 4983230072969 + 3 ^ 40 * 3941875 * 2
def baseEnd_3941875 : Nat := 1349384369961246753089435

theorem tailTrace_3941875 : CollatzResearch.WordTrace tailWord_3941875 prefixEnd_3941875 1349384369961246753089435 := by
  unfold tailWord_3941875
  simp only [CollatzResearch.WordTrace]
  refine ⟨143771992594267568497435079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95847995062845045664956719 143771992594267568497435079)
  ·
    refine ⟨215657988891401352746152619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143771992594267568497435079 215657988891401352746152619)
    ·
      refine ⟨323486983337102029119228929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215657988891401352746152619 323486983337102029119228929)
      ·
        refine ⟨242615237502826521839421697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323486983337102029119228929 242615237502826521839421697)
        ·
          refine ⟨181961428127119891379566273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242615237502826521839421697 181961428127119891379566273)
          ·
            refine ⟨136471071095339918534674705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181961428127119891379566273 136471071095339918534674705)
            ·
              refine ⟨102353303321504938901006029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136471071095339918534674705 102353303321504938901006029)
              ·
                refine ⟨38382488745564352087877261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102353303321504938901006029 38382488745564352087877261)
                ·
                  refine ⟨14393433279586632032953973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38382488745564352087877261 14393433279586632032953973)
                  ·
                    refine ⟨1349384369961246753089435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14393433279586632032953973 1349384369961246753089435)
                    ·
                      rfl

theorem cell22_3941875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_3941875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941875 prefixEnd_3941875 := by exact prefixLift 3941875
  have htrace : WordTrace (prefixWord ++ tailWord_3941875) baseStart_3941875 baseEnd_3941875 := by
    simpa [prefixWord, tailWord_3941875, baseEnd_3941875] using wordTrace_append hprefix tailTrace_3941875
  have hstable : (prefixWord ++ tailWord_3941875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941875).length < 2 ^ (prefixWord ++ tailWord_3941875).sum := by decide
  have hdescent : baseEnd_3941875 < baseStart_3941875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941905 : List Nat := [1, 2, 2, 1, 1, 2, 4, 9]
def baseStart_3941905 : Nat := 118140960795 + 3941905 * 2 ^ 59
def prefixEnd_3941905 : Nat := 4983230072969 + 3 ^ 40 * 3941905 * 2
def baseEnd_3941905 : Nat := 149932737730481852759927

theorem tailTrace_3941905 : CollatzResearch.WordTrace tailWord_3941905 prefixEnd_3941905 149932737730481852759927 := by
  unfold tailWord_3941905
  simp only [CollatzResearch.WordTrace]
  refine ⟨143773086784158883621027169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95848724522772589080684779 143773086784158883621027169)
  ·
    refine ⟨107829815088119162715770377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143773086784158883621027169 107829815088119162715770377)
    ·
      refine ⟨80872361316089372036827783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107829815088119162715770377 80872361316089372036827783)
      ·
        refine ⟨121308541974134058055241675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80872361316089372036827783 121308541974134058055241675)
        ·
          refine ⟨181962812961201087082862513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121308541974134058055241675 181962812961201087082862513)
          ·
            refine ⟨136472109720900815312146885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181962812961201087082862513 136472109720900815312146885)
            ·
              refine ⟨25588520572668902871027541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136472109720900815312146885 25588520572668902871027541)
              ·
                refine ⟨149932737730481852759927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25588520572668902871027541 149932737730481852759927)
                ·
                  rfl

theorem cell22_3941905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 9].length) (baseStart_3941905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941905 prefixEnd_3941905 := by exact prefixLift 3941905
  have htrace : WordTrace (prefixWord ++ tailWord_3941905) baseStart_3941905 baseEnd_3941905 := by
    simpa [prefixWord, tailWord_3941905, baseEnd_3941905] using wordTrace_append hprefix tailTrace_3941905
  have hstable : (prefixWord ++ tailWord_3941905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941905).length < 2 ^ (prefixWord ++ tailWord_3941905).sum := by decide
  have hdescent : baseEnd_3941905 < baseStart_3941905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941909 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 1, 5]
def baseStart_3941909 : Nat := 118140960795 + 3941909 * 2 ^ 59
def prefixEnd_3941909 : Nat := 4983230072969 + 3 ^ 40 * 3941909 * 2
def baseEnd_3941909 : Nat := 1349396008856081997739331

theorem tailTrace_3941909 : CollatzResearch.WordTrace tailWord_3941909 prefixEnd_3941909 1349396008856081997739331 := by
  unfold tailWord_3941909
  simp only [CollatzResearch.WordTrace]
  refine ⟨143773232676144392304172781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95848821784096261536115187 143773232676144392304172781)
  ·
    refine ⟨53914962253554147114064793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143773232676144392304172781 53914962253554147114064793)
    ·
      refine ⟨40436221690165610335548595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53914962253554147114064793 40436221690165610335548595)
      ·
        refine ⟨60654332535248415503322893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40436221690165610335548595 60654332535248415503322893)
        ·
          refine ⟨22745374700718155813746085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60654332535248415503322893 22745374700718155813746085)
          ·
            refine ⟨4264757756384654215077391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22745374700718155813746085 4264757756384654215077391)
            ·
              refine ⟨6397136634576981322616087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264757756384654215077391 6397136634576981322616087)
              ·
                refine ⟨9595704951865471983924131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6397136634576981322616087 9595704951865471983924131)
                ·
                  refine ⟨14393557427798207975886197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9595704951865471983924131 14393557427798207975886197)
                  ·
                    refine ⟨1349396008856081997739331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14393557427798207975886197 1349396008856081997739331)
                    ·
                      rfl

theorem cell22_3941909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_3941909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941909 prefixEnd_3941909 := by exact prefixLift 3941909
  have htrace : WordTrace (prefixWord ++ tailWord_3941909) baseStart_3941909 baseEnd_3941909 := by
    simpa [prefixWord, tailWord_3941909, baseEnd_3941909] using wordTrace_append hprefix tailTrace_3941909
  have hstable : (prefixWord ++ tailWord_3941909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941909).length < 2 ^ (prefixWord ++ tailWord_3941909).sum := by decide
  have hdescent : baseEnd_3941909 < baseStart_3941909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941928 : List Nat := [2, 1, 5, 2, 2, 2, 1, 3, 4]
def baseStart_3941928 : Nat := 118140960795 + 3941928 * 2 ^ 59
def prefixEnd_3941928 : Nat := 4983230072969 + 3 ^ 40 * 3941928 * 2
def baseEnd_3941928 : Nat := 449800837648124093838091

theorem tailTrace_3941928 : CollatzResearch.WordTrace tailWord_3941928 prefixEnd_3941928 449800837648124093838091 := by
  unfold tailWord_3941928
  simp only [CollatzResearch.WordTrace]
  refine ⟨71886962831537779274557219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95849283775383705699409625 71886962831537779274557219)
  ·
    refine ⟨107830444247306668911835829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71886962831537779274557219 107830444247306668911835829)
    ·
      refine ⟨10109104148185000210484609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107830444247306668911835829 10109104148185000210484609)
      ·
        refine ⟨7581828111138750157863457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10109104148185000210484609 7581828111138750157863457)
        ·
          refine ⟨5686371083354062618397593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7581828111138750157863457 5686371083354062618397593)
          ·
            refine ⟨4264778312515546963798195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5686371083354062618397593 4264778312515546963798195)
            ·
              refine ⟨6397167468773320445697293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264778312515546963798195 6397167468773320445697293)
              ·
                refine ⟨2398937800789995167136485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6397167468773320445697293 2398937800789995167136485)
                ·
                  refine ⟨449800837648124093838091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2398937800789995167136485 449800837648124093838091)
                  ·
                    rfl

theorem cell22_3941928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 4].length) (baseStart_3941928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3941928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3941928 prefixEnd_3941928 := by exact prefixLift 3941928
  have htrace : WordTrace (prefixWord ++ tailWord_3941928) baseStart_3941928 baseEnd_3941928 := by
    simpa [prefixWord, tailWord_3941928, baseEnd_3941928] using wordTrace_append hprefix tailTrace_3941928
  have hstable : (prefixWord ++ tailWord_3941928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941928).length < 2 ^ (prefixWord ++ tailWord_3941928).sum := by decide
  have hdescent : baseEnd_3941928 < baseStart_3941928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942005 : List Nat := [1, 3, 4, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3942005 : Nat := 118140960795 + 3942005 * 2 ^ 59
def prefixEnd_3942005 : Nat := 4983230072969 + 3 ^ 40 * 3942005 * 2
def baseEnd_3942005 : Nat := 1349428871617969747339037

theorem tailTrace_3942005 : CollatzResearch.WordTrace tailWord_3942005 prefixEnd_3942005 1349428871617969747339037 := by
  unfold tailWord_3942005
  simp only [CollatzResearch.WordTrace]
  refine ⟨143776734083796600699667469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95851156055864400466444979 143776734083796600699667469)
  ·
    refine ⟨53916275281423725262375301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143776734083796600699667469 53916275281423725262375301)
    ·
      refine ⟨10109301615266948486695369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53916275281423725262375301 10109301615266948486695369)
      ·
        refine ⟨7581976211450211365021527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10109301615266948486695369 7581976211450211365021527)
        ·
          refine ⟨11372964317175317047532291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7581976211450211365021527 11372964317175317047532291)
          ·
            refine ⟨17059446475762975571298437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11372964317175317047532291 17059446475762975571298437)
            ·
              refine ⟨3198646214205557919618457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17059446475762975571298437 3198646214205557919618457)
              ·
                refine ⟨2398984660654168439713843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3198646214205557919618457 2398984660654168439713843)
                ·
                  refine ⟨3598476990981252659570765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398984660654168439713843 3598476990981252659570765)
                  ·
                    refine ⟨1349428871617969747339037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3598476990981252659570765 1349428871617969747339037)
                    ·
                      rfl

theorem cell22_3942005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3942005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942005 prefixEnd_3942005 := by exact prefixLift 3942005
  have htrace : WordTrace (prefixWord ++ tailWord_3942005) baseStart_3942005 baseEnd_3942005 := by
    simpa [prefixWord, tailWord_3942005, baseEnd_3942005] using wordTrace_append hprefix tailTrace_3942005
  have hstable : (prefixWord ++ tailWord_3942005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942005).length < 2 ^ (prefixWord ++ tailWord_3942005).sum := by decide
  have hdescent : baseEnd_3942005 < baseStart_3942005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942012 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 6]
def baseStart_3942012 : Nat := 118140960795 + 3942012 * 2 ^ 59
def prefixEnd_3942012 : Nat := 4983230072969 + 3 ^ 40 * 3942012 * 2
def baseEnd_3942012 : Nat := 449810422620341354138005

theorem tailTrace_3942012 : CollatzResearch.WordTrace tailWord_3942012 prefixEnd_3942012 449810422620341354138005 := by
  unfold tailWord_3942012
  simp only [CollatzResearch.WordTrace]
  refine ⟨71888494697385620447586145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95851326263180827263448193 71888494697385620447586145)
  ·
    refine ⟨53916371023039215335689609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71888494697385620447586145 53916371023039215335689609)
    ·
      refine ⟨40437278267279411501767207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53916371023039215335689609 40437278267279411501767207)
      ·
        refine ⟨60655917400919117252650811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40437278267279411501767207 60655917400919117252650811)
        ·
          refine ⟨90983876101378675878976217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60655917400919117252650811 90983876101378675878976217)
          ·
            refine ⟨68237907076034006909232163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90983876101378675878976217 68237907076034006909232163)
            ·
              refine ⟨102356860614051010363848245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68237907076034006909232163 102356860614051010363848245)
              ·
                refine ⟨9595955682567282221610773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102356860614051010363848245 9595955682567282221610773)
                ·
                  refine ⟨449810422620341354138005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9595955682567282221610773 449810422620341354138005)
                  ·
                    rfl

theorem cell22_3942012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_3942012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942012 prefixEnd_3942012 := by exact prefixLift 3942012
  have htrace : WordTrace (prefixWord ++ tailWord_3942012) baseStart_3942012 baseEnd_3942012 := by
    simpa [prefixWord, tailWord_3942012, baseEnd_3942012] using wordTrace_append hprefix tailTrace_3942012
  have hstable : (prefixWord ++ tailWord_3942012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942012).length < 2 ^ (prefixWord ++ tailWord_3942012).sum := by decide
  have hdescent : baseEnd_3942012 < baseStart_3942012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942048 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 1, 4]
def baseStart_3942048 : Nat := 118140960795 + 3942048 * 2 ^ 59
def prefixEnd_3942048 : Nat := 4983230072969 + 3 ^ 40 * 3942048 * 2
def baseEnd_3942048 : Nat := 1349443591396731968513905

theorem tailTrace_3942048 : CollatzResearch.WordTrace tailWord_3942048 prefixEnd_3942048 1349443591396731968513905 := by
  unfold tailWord_3942048
  simp only [CollatzResearch.WordTrace]
  refine ⟨71889151211320409521741399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95852201615093879362321865 71889151211320409521741399)
  ·
    refine ⟨107833726816980614282612099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71889151211320409521741399 107833726816980614282612099)
    ·
      refine ⟨161750590225470921423918149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107833726816980614282612099 161750590225470921423918149)
      ·
        refine ⟨30328235667275797766984653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161750590225470921423918149 30328235667275797766984653)
        ·
          refine ⟨11373088375228424162619245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30328235667275797766984653 11373088375228424162619245)
          ·
            refine ⟨4264908140710659060982217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11373088375228424162619245 4264908140710659060982217)
            ·
              refine ⟨3198681105532994295736663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264908140710659060982217 3198681105532994295736663)
              ·
                refine ⟨4798021658299491443604995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3198681105532994295736663 4798021658299491443604995)
                ·
                  refine ⟨7197032487449237165407493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4798021658299491443604995 7197032487449237165407493)
                  ·
                    refine ⟨1349443591396731968513905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7197032487449237165407493 1349443591396731968513905)
                    ·
                      rfl

theorem cell22_3942048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 4].length) (baseStart_3942048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942048 prefixEnd_3942048 := by exact prefixLift 3942048
  have htrace : WordTrace (prefixWord ++ tailWord_3942048) baseStart_3942048 baseEnd_3942048 := by
    simpa [prefixWord, tailWord_3942048, baseEnd_3942048] using wordTrace_append hprefix tailTrace_3942048
  have hstable : (prefixWord ++ tailWord_3942048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942048).length < 2 ^ (prefixWord ++ tailWord_3942048).sum := by decide
  have hdescent : baseEnd_3942048 < baseStart_3942048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942061 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3942061 : Nat := 118140960795 + 3942061 * 2 ^ 59
def prefixEnd_3942061 : Nat := 4983230072969 + 3 ^ 40 * 3942061 * 2
def baseEnd_3942061 : Nat := 1349448041562404267938865

theorem tailTrace_3942061 : CollatzResearch.WordTrace tailWord_3942061 prefixEnd_3942061 1349448041562404267938865 := by
  unfold tailWord_3942061
  simp only [CollatzResearch.WordTrace]
  refine ⟨143778776571593722263706037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95852517714395814842470691 143778776571593722263706037)
  ·
    refine ⟨13479260303586911462222441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143778776571593722263706037 13479260303586911462222441)
    ·
      refine ⟨10109445227690183596666831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13479260303586911462222441 10109445227690183596666831)
      ·
        refine ⟨15164167841535275395000247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10109445227690183596666831 15164167841535275395000247)
        ·
          refine ⟨22746251762302913092500371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15164167841535275395000247 22746251762302913092500371)
          ·
            refine ⟨34119377643454369638750557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22746251762302913092500371 34119377643454369638750557)
            ·
              refine ⟨12794766616295388614531459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34119377643454369638750557 12794766616295388614531459)
              ·
                refine ⟨19192149924443082921797189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12794766616295388614531459 19192149924443082921797189)
                ·
                  refine ⟨3598528110833078047836973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19192149924443082921797189 3598528110833078047836973)
                  ·
                    refine ⟨1349448041562404267938865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3598528110833078047836973 1349448041562404267938865)
                    ·
                      rfl

theorem cell22_3942061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3942061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942061 prefixEnd_3942061 := by exact prefixLift 3942061
  have htrace : WordTrace (prefixWord ++ tailWord_3942061) baseStart_3942061 baseEnd_3942061 := by
    simpa [prefixWord, tailWord_3942061, baseEnd_3942061] using wordTrace_append hprefix tailTrace_3942061
  have hstable : (prefixWord ++ tailWord_3942061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942061).length < 2 ^ (prefixWord ++ tailWord_3942061).sum := by decide
  have hdescent : baseEnd_3942061 < baseStart_3942061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942082 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3942082 : Nat := 118140960795 + 3942082 * 2 ^ 59
def prefixEnd_3942082 : Nat := 4983230072969 + 3 ^ 40 * 3942082 * 2
def baseEnd_3942082 : Nat := 1349455230291567213163801

theorem tailTrace_3942082 : CollatzResearch.WordTrace tailWord_3942082 prefixEnd_3942082 1349455230291567213163801 := by
  unfold tailWord_3942082
  simp only [CollatzResearch.WordTrace]
  refine ⟨35944885626129410712555125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95853028336345095233480333 35944885626129410712555125)
  ·
    refine ⟨3369833027449632254302043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35944885626129410712555125 3369833027449632254302043)
    ·
      refine ⟨5054749541174448381453065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3369833027449632254302043 5054749541174448381453065)
      ·
        refine ⟨3791062155880836286089799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5054749541174448381453065 3791062155880836286089799)
        ·
          refine ⟨5686593233821254429134699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791062155880836286089799 5686593233821254429134699)
          ·
            refine ⟨8529889850731881643702049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686593233821254429134699 8529889850731881643702049)
            ·
              refine ⟨6397417388048911232776537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8529889850731881643702049 6397417388048911232776537)
              ·
                refine ⟨4798063041036683424582403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6397417388048911232776537 4798063041036683424582403)
                ·
                  refine ⟨7197094561555025136873605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4798063041036683424582403 7197094561555025136873605)
                  ·
                    refine ⟨1349455230291567213163801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7197094561555025136873605 1349455230291567213163801)
                    ·
                      rfl

theorem cell22_3942082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3942082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942082 prefixEnd_3942082 := by exact prefixLift 3942082
  have htrace : WordTrace (prefixWord ++ tailWord_3942082) baseStart_3942082 baseEnd_3942082 := by
    simpa [prefixWord, tailWord_3942082, baseEnd_3942082] using wordTrace_append hprefix tailTrace_3942082
  have hstable : (prefixWord ++ tailWord_3942082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942082).length < 2 ^ (prefixWord ++ tailWord_3942082).sum := by decide
  have hdescent : baseEnd_3942082 < baseStart_3942082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942108 : List Nat := [2, 2, 5, 1, 3, 1, 8]
def baseStart_3942108 : Nat := 118140960795 + 3942108 * 2 ^ 59
def prefixEnd_3942108 : Nat := 4983230072969 + 3 ^ 40 * 3942108 * 2
def baseEnd_3942108 : Nat := 49980152986033770815323

theorem tailTrace_3942108 : CollatzResearch.WordTrace tailWord_3942108 prefixEnd_3942108 49980152986033770815323 := by
  unfold tailWord_3942108
  simp only [CollatzResearch.WordTrace]
  refine ⟨71890245401211724645333489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95853660534948966193777985 71890245401211724645333489)
  ·
    refine ⟨53917684050908793484000117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71890245401211724645333489 53917684050908793484000117)
    ·
      refine ⟨5054782879772699389125011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53917684050908793484000117 5054782879772699389125011)
      ·
        refine ⟨7582174319659049083687517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5054782879772699389125011 7582174319659049083687517)
        ·
          refine ⟨2843315369872143406382819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7582174319659049083687517 2843315369872143406382819)
          ·
            refine ⟨4264973054808215109574229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843315369872143406382819 4264973054808215109574229)
            ·
              refine ⟨49980152986033770815323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4264973054808215109574229 49980152986033770815323)
              ·
                rfl

theorem cell22_3942108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 8].length) (baseStart_3942108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942108 prefixEnd_3942108 := by exact prefixLift 3942108
  have htrace : WordTrace (prefixWord ++ tailWord_3942108) baseStart_3942108 baseEnd_3942108 := by
    simpa [prefixWord, tailWord_3942108, baseEnd_3942108] using wordTrace_append hprefix tailTrace_3942108
  have hstable : (prefixWord ++ tailWord_3942108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942108).length < 2 ^ (prefixWord ++ tailWord_3942108).sum := by decide
  have hdescent : baseEnd_3942108 < baseStart_3942108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942174 : List Nat := [4, 3, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3942174 : Nat := 118140960795 + 3942174 * 2 ^ 59
def prefixEnd_3942174 : Nat := 4983230072969 + 3 ^ 40 * 3942174 * 2
def baseEnd_3942174 : Nat := 1349486723771709639863519

theorem tailTrace_3942174 : CollatzResearch.WordTrace tailWord_3942174 prefixEnd_3942174 1349486723771709639863519 := by
  unfold tailWord_3942174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972862252523042820321197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95855265346789561708379717 17972862252523042820321197)
  ·
    refine ⟨6739823344696141057620449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17972862252523042820321197 6739823344696141057620449)
    ·
      refine ⟨5054867508522105793215337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6739823344696141057620449 5054867508522105793215337)
      ·
        refine ⟨3791150631391579344911503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5054867508522105793215337 3791150631391579344911503)
        ·
          refine ⟨5686725947087369017367255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791150631391579344911503 5686725947087369017367255)
          ·
            refine ⟨8530088920631053526050883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686725947087369017367255 8530088920631053526050883)
            ·
              refine ⟨12795133380946580289076325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8530088920631053526050883 12795133380946580289076325)
              ·
                refine ⟨2399087508927483804201811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12795133380946580289076325 2399087508927483804201811)
                ·
                  refine ⟨3598631263391225706302717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399087508927483804201811 3598631263391225706302717)
                  ·
                    refine ⟨1349486723771709639863519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3598631263391225706302717 1349486723771709639863519)
                    ·
                      rfl

theorem cell22_3942174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3942174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942174 prefixEnd_3942174 := by exact prefixLift 3942174
  have htrace : WordTrace (prefixWord ++ tailWord_3942174) baseStart_3942174 baseEnd_3942174 := by
    simpa [prefixWord, tailWord_3942174, baseEnd_3942174] using wordTrace_append hprefix tailTrace_3942174
  have hstable : (prefixWord ++ tailWord_3942174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942174).length < 2 ^ (prefixWord ++ tailWord_3942174).sum := by decide
  have hdescent : baseEnd_3942174 < baseStart_3942174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942198 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_3942198 : Nat := 118140960795 + 3942198 * 2 ^ 59
def prefixEnd_3942198 : Nat := 4983230072969 + 3 ^ 40 * 3942198 * 2
def baseEnd_3942198 : Nat := 449831646487393859087815

theorem tailTrace_3942198 : CollatzResearch.WordTrace tailWord_3942198 prefixEnd_3942198 449831646487393859087815 := by
  unfold tailWord_3942198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8986485835756087166340203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95855848914731596440962165 8986485835756087166340203)
  ·
    refine ⟨13479728753634130749510305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8986485835756087166340203 13479728753634130749510305)
    ·
      refine ⟨10109796565225598062132729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13479728753634130749510305 10109796565225598062132729)
      ·
        refine ⟨7582347423919198546599547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10109796565225598062132729 7582347423919198546599547)
        ·
          refine ⟨11373521135878797819899321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7582347423919198546599547 11373521135878797819899321)
          ·
            refine ⟨8530140851909098364924491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11373521135878797819899321 8530140851909098364924491)
            ·
              refine ⟨12795211277863647547386737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8530140851909098364924491 12795211277863647547386737)
              ·
                refine ⟨9596408458397735660540053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12795211277863647547386737 9596408458397735660540053)
                ·
                  refine ⟨449831646487393859087815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9596408458397735660540053 449831646487393859087815)
                  ·
                    rfl

theorem cell22_3942198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_3942198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942198 prefixEnd_3942198 := by exact prefixLift 3942198
  have htrace : WordTrace (prefixWord ++ tailWord_3942198) baseStart_3942198 baseEnd_3942198 := by
    simpa [prefixWord, tailWord_3942198, baseEnd_3942198] using wordTrace_append hprefix tailTrace_3942198
  have hstable : (prefixWord ++ tailWord_3942198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942198).length < 2 ^ (prefixWord ++ tailWord_3942198).sum := by decide
  have hdescent : baseEnd_3942198 < baseStart_3942198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942211 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 2, 4]
def baseStart_3942211 : Nat := 118140960795 + 3942211 * 2 ^ 59
def prefixEnd_3942211 : Nat := 4983230072969 + 3 ^ 40 * 3942211 * 2
def baseEnd_3942211 : Nat := 1349499389627853876688405

theorem tailTrace_3942211 : CollatzResearch.WordTrace tailWord_3942211 prefixEnd_3942211 1349499389627853876688405 := by
  unfold tailWord_3942211
  simp only [CollatzResearch.WordTrace]
  refine ⟨143784247521050297881666487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95856165014033531921110991 143784247521050297881666487)
  ·
    refine ⟨215676371281575446822499731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143784247521050297881666487 215676371281575446822499731)
    ·
      refine ⟨323514556922363170233749597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215676371281575446822499731 323514556922363170233749597)
      ·
        refine ⟨121317958845886188837656099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323514556922363170233749597 121317958845886188837656099)
        ·
          refine ⟨181976938268829283256484149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121317958845886188837656099 181976938268829283256484149)
          ·
            refine ⟨17060337962702745305295389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181976938268829283256484149 17060337962702745305295389)
            ·
              refine ⟨6397626736013529489485771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17060337962702745305295389 6397626736013529489485771)
              ·
                refine ⟨9596440104020294234228657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6397626736013529489485771 9596440104020294234228657)
                ·
                  refine ⟨7197330078015220675671493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9596440104020294234228657 7197330078015220675671493)
                  ·
                    refine ⟨1349499389627853876688405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7197330078015220675671493 1349499389627853876688405)
                    ·
                      rfl

theorem cell22_3942211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 4].length) (baseStart_3942211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942211 prefixEnd_3942211 := by exact prefixLift 3942211
  have htrace : WordTrace (prefixWord ++ tailWord_3942211) baseStart_3942211 baseEnd_3942211 := by
    simpa [prefixWord, tailWord_3942211, baseEnd_3942211] using wordTrace_append hprefix tailTrace_3942211
  have hstable : (prefixWord ++ tailWord_3942211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942211).length < 2 ^ (prefixWord ++ tailWord_3942211).sum := by decide
  have hdescent : baseEnd_3942211 < baseStart_3942211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942275 : List Nat := [1, 1, 1, 3, 4, 2, 3, 3, 1, 3]
def baseStart_3942275 : Nat := 118140960795 + 3942275 * 2 ^ 59
def prefixEnd_3942275 : Nat := 4983230072969 + 3 ^ 40 * 3942275 * 2
def baseEnd_3942275 : Nat := 1349521298135779043088209

theorem tailTrace_3942275 : CollatzResearch.WordTrace tailWord_3942275 prefixEnd_3942275 1349521298135779043088209 := by
  unfold tailWord_3942275
  simp only [CollatzResearch.WordTrace]
  refine ⟨143786581792818436811996279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95857721195212291207997519 143786581792818436811996279)
  ·
    refine ⟨215679872689227655217994419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143786581792818436811996279 215679872689227655217994419)
    ·
      refine ⟨323519809033841482826991629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215679872689227655217994419 323519809033841482826991629)
      ·
        refine ⟨121319928387690556060121861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323519809033841482826991629 121319928387690556060121861)
        ·
          refine ⟨22747486572691979261272849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121319928387690556060121861 22747486572691979261272849)
          ·
            refine ⟨17060614929518984445954637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22747486572691979261272849 17060614929518984445954637)
            ·
              refine ⟨6397730598569619167232989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17060614929518984445954637 6397730598569619167232989)
              ·
                refine ⟨2399148974463607187712371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6397730598569619167232989 2399148974463607187712371)
                ·
                  refine ⟨3598723461695410781568557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399148974463607187712371 3598723461695410781568557)
                  ·
                    refine ⟨1349521298135779043088209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3598723461695410781568557 1349521298135779043088209)
                    ·
                      rfl

theorem cell22_3942275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 1, 3].length) (baseStart_3942275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942275 prefixEnd_3942275 := by exact prefixLift 3942275
  have htrace : WordTrace (prefixWord ++ tailWord_3942275) baseStart_3942275 baseEnd_3942275 := by
    simpa [prefixWord, tailWord_3942275, baseEnd_3942275] using wordTrace_append hprefix tailTrace_3942275
  have hstable : (prefixWord ++ tailWord_3942275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942275).length < 2 ^ (prefixWord ++ tailWord_3942275).sum := by decide
  have hdescent : baseEnd_3942275 < baseStart_3942275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942365 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3942365 : Nat := 118140960795 + 3942365 * 2 ^ 59
def prefixEnd_3942365 : Nat := 4983230072969 + 3 ^ 40 * 3942365 * 2
def baseEnd_3942365 : Nat := 1349552106975048808337933

theorem tailTrace_3942365 : CollatzResearch.WordTrace tailWord_3942365 prefixEnd_3942365 1349552106975048808337933 := by
  unfold tailWord_3942365
  simp only [CollatzResearch.WordTrace]
  refine ⟨143789864362492382182772549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95859909574994921455181699 143789864362492382182772549)
  ·
    refine ⟨26960599567967321659269853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143789864362492382182772549 26960599567967321659269853)
    ·
      refine ⟨10110224837987745622226195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26960599567967321659269853 10110224837987745622226195)
      ·
        refine ⟨15165337256981618433339293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10110224837987745622226195 15165337256981618433339293)
        ·
          refine ⟨5687001471368106912502235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15165337256981618433339293 5687001471368106912502235)
          ·
            refine ⟨8530502207052160368753353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5687001471368106912502235 8530502207052160368753353)
            ·
              refine ⟨6397876655289120276565015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8530502207052160368753353 6397876655289120276565015)
              ·
                refine ⟨9596814982933680414847523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6397876655289120276565015 9596814982933680414847523)
                ·
                  refine ⟨14395222474400520622271285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9596814982933680414847523 14395222474400520622271285)
                  ·
                    refine ⟨1349552106975048808337933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14395222474400520622271285 1349552106975048808337933)
                    ·
                      rfl

theorem cell22_3942365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3942365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942365 prefixEnd_3942365 := by exact prefixLift 3942365
  have htrace : WordTrace (prefixWord ++ tailWord_3942365) baseStart_3942365 baseEnd_3942365 := by
    simpa [prefixWord, tailWord_3942365, baseEnd_3942365] using wordTrace_append hprefix tailTrace_3942365
  have hstable : (prefixWord ++ tailWord_3942365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942365).length < 2 ^ (prefixWord ++ tailWord_3942365).sum := by decide
  have hdescent : baseEnd_3942365 < baseStart_3942365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942378 : List Nat := [3, 1, 3, 1, 2, 1, 5, 6]
def baseStart_3942378 : Nat := 118140960795 + 3942378 * 2 ^ 59
def prefixEnd_3942378 : Nat := 4983230072969 + 3 ^ 40 * 3942378 * 2
def baseEnd_3942378 : Nat := 149950728571191234195877

theorem tailTrace_3942378 : CollatzResearch.WordTrace tailWord_3942378 prefixEnd_3942378 149950728571191234195877 := by
  unfold tailWord_3942378
  simp only [CollatzResearch.WordTrace]
  refine ⟨35947584627861321350748947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95860225674296856935330525 35947584627861321350748947)
  ·
    refine ⟨53921376941791982026123421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35947584627861321350748947 53921376941791982026123421)
    ·
      refine ⟨20220516353171993259796283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53921376941791982026123421 20220516353171993259796283)
      ·
        refine ⟨30330774529757989889694425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20220516353171993259796283 30330774529757989889694425)
        ·
          refine ⟨22748080897318492417270819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30330774529757989889694425 22748080897318492417270819)
          ·
            refine ⟨34122121345977738625906229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22748080897318492417270819 34122121345977738625906229)
            ·
              refine ⟨3198948876185412996178709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34122121345977738625906229 3198948876185412996178709)
              ·
                refine ⟨149950728571191234195877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3198948876185412996178709 149950728571191234195877)
                ·
                  rfl

theorem cell22_3942378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_3942378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942378 prefixEnd_3942378 := by exact prefixLift 3942378
  have htrace : WordTrace (prefixWord ++ tailWord_3942378) baseStart_3942378 baseEnd_3942378 := by
    simpa [prefixWord, tailWord_3942378, baseEnd_3942378] using wordTrace_append hprefix tailTrace_3942378
  have hstable : (prefixWord ++ tailWord_3942378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942378).length < 2 ^ (prefixWord ++ tailWord_3942378).sum := by decide
  have hdescent : baseEnd_3942378 < baseStart_3942378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942451 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 8]
def baseStart_3942451 : Nat := 118140960795 + 3942451 * 2 ^ 59
def prefixEnd_3942451 : Nat := 4983230072969 + 3 ^ 40 * 3942451 * 2
def baseEnd_3942451 : Nat := 449860515510857750229223

theorem tailTrace_3942451 : CollatzResearch.WordTrace tailWord_3942451 prefixEnd_3942451 449860515510857750229223 := by
  unfold tailWord_3942451
  simp only [CollatzResearch.WordTrace]
  refine ⟨143793001040180818870403207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95862000693453879246935471 143793001040180818870403207)
  ·
    refine ⟨215689501560271228305604811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143793001040180818870403207 215689501560271228305604811)
    ·
      refine ⟨323534252340406842458407217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215689501560271228305604811 323534252340406842458407217)
      ·
        refine ⟨242650689255305131843805413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323534252340406842458407217 242650689255305131843805413)
        ·
          refine ⟨45497004235369712220713515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242650689255305131843805413 45497004235369712220713515)
          ·
            refine ⟨68245506353054568331070273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45497004235369712220713515 68245506353054568331070273)
            ·
              refine ⟨51184129764790926248302705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68245506353054568331070273 51184129764790926248302705)
              ·
                refine ⟨38388097323593194686227029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51184129764790926248302705 38388097323593194686227029)
                ·
                  refine ⟨449860515510857750229223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38388097323593194686227029 449860515510857750229223)
                  ·
                    rfl

theorem cell22_3942451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 8].length) (baseStart_3942451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942451 prefixEnd_3942451 := by exact prefixLift 3942451
  have htrace : WordTrace (prefixWord ++ tailWord_3942451) baseStart_3942451 baseEnd_3942451 := by
    simpa [prefixWord, tailWord_3942451, baseEnd_3942451] using wordTrace_append hprefix tailTrace_3942451
  have hstable : (prefixWord ++ tailWord_3942451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942451).length < 2 ^ (prefixWord ++ tailWord_3942451).sum := by decide
  have hdescent : baseEnd_3942451 < baseStart_3942451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942592 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 5]
def baseStart_3942592 : Nat := 118140960795 + 3942592 * 2 ^ 59
def prefixEnd_3942592 : Nat := 4983230072969 + 3 ^ 40 * 3942592 * 2
def baseEnd_3942592 : Nat := 449876604571365294304079

theorem tailTrace_3942592 : CollatzResearch.WordTrace tailWord_3942592 prefixEnd_3942592 449876604571365294304079 := by
  unfold tailWord_3942592
  simp only [CollatzResearch.WordTrace]
  refine ⟨71899071866334999975643015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95865429155113333300857353 71899071866334999975643015)
  ·
    refine ⟨107848607799502499963464523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71899071866334999975643015 107848607799502499963464523)
    ·
      refine ⟨161772911699253749945196785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107848607799502499963464523 161772911699253749945196785)
      ·
        refine ⟨121329683774440312458897589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161772911699253749945196785 121329683774440312458897589)
        ·
          refine ⟨11374657853853779293021649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121329683774440312458897589 11374657853853779293021649)
          ·
            refine ⟨8530993390390334469766237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11374657853853779293021649 8530993390390334469766237)
            ·
              refine ⟨3199122521396375426162339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8530993390390334469766237 3199122521396375426162339)
              ·
                refine ⟨4798683782094563139243509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199122521396375426162339 4798683782094563139243509)
                ·
                  refine ⟨449876604571365294304079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4798683782094563139243509 449876604571365294304079)
                  ·
                    rfl

theorem cell22_3942592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 5].length) (baseStart_3942592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942592 prefixEnd_3942592 := by exact prefixLift 3942592
  have htrace : WordTrace (prefixWord ++ tailWord_3942592) baseStart_3942592 baseEnd_3942592 := by
    simpa [prefixWord, tailWord_3942592, baseEnd_3942592] using wordTrace_append hprefix tailTrace_3942592
  have hstable : (prefixWord ++ tailWord_3942592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942592).length < 2 ^ (prefixWord ++ tailWord_3942592).sum := by decide
  have hdescent : baseEnd_3942592 < baseStart_3942592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942603 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 6]
def baseStart_3942603 : Nat := 118140960795 + 3942603 * 2 ^ 59
def prefixEnd_3942603 : Nat := 4983230072969 + 3 ^ 40 * 3942603 * 2
def baseEnd_3942603 : Nat := 449877859746298506962401

theorem tailTrace_3942603 : CollatzResearch.WordTrace tailWord_3942603 prefixEnd_3942603 449877859746298506962401 := by
  unfold tailWord_3942603
  simp only [CollatzResearch.WordTrace]
  refine ⟨143798544935630148829936463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95865696623753432553290975 143798544935630148829936463)
  ·
    refine ⟨215697817403445223244904695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143798544935630148829936463 215697817403445223244904695)
    ·
      refine ⟨323546726105167834867357043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215697817403445223244904695 323546726105167834867357043)
      ·
        refine ⟨485320089157751752301035565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323546726105167834867357043 485320089157751752301035565)
        ·
          refine ⟨181995033434156907112888337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485320089157751752301035565 181995033434156907112888337)
          ·
            refine ⟨136496275075617680334666253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181995033434156907112888337 136496275075617680334666253)
            ·
              refine ⟨51186103153356630125499845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136496275075617680334666253 51186103153356630125499845)
              ·
                refine ⟨9597394341254368148531221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51186103153356630125499845 9597394341254368148531221)
                ·
                  refine ⟨449877859746298506962401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9597394341254368148531221 449877859746298506962401)
                  ·
                    rfl

theorem cell22_3942603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 6].length) (baseStart_3942603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942603 prefixEnd_3942603 := by exact prefixLift 3942603
  have htrace : WordTrace (prefixWord ++ tailWord_3942603) baseStart_3942603 baseEnd_3942603 := by
    simpa [prefixWord, tailWord_3942603, baseEnd_3942603] using wordTrace_append hprefix tailTrace_3942603
  have hstable : (prefixWord ++ tailWord_3942603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942603).length < 2 ^ (prefixWord ++ tailWord_3942603).sum := by decide
  have hdescent : baseEnd_3942603 < baseStart_3942603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942613 : List Nat := [1, 3, 2, 4, 3, 1, 1, 3, 1, 3]
def baseStart_3942613 : Nat := 118140960795 + 3942613 * 2 ^ 59
def prefixEnd_3942613 : Nat := 4983230072969 + 3 ^ 40 * 3942613 * 2
def baseEnd_3942613 : Nat := 1349637002443258828137173

theorem tailTrace_3942613 : CollatzResearch.WordTrace tailWord_3942613 prefixEnd_3942613 1349637002443258828137173 := by
  unfold tailWord_3942613
  simp only [CollatzResearch.WordTrace]
  refine ⟨143798909665593920537800493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95865939777062613691866995 143798909665593920537800493)
  ·
    refine ⟨53924591124597720201675185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143798909665593920537800493 53924591124597720201675185)
    ·
      refine ⟨40443443343448290151256389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53924591124597720201675185 40443443343448290151256389)
      ·
        refine ⟨7583145626896554403360573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40443443343448290151256389 7583145626896554403360573)
        ·
          refine ⟨2843679610086207901260215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7583145626896554403360573 2843679610086207901260215)
          ·
            refine ⟨4265519415129311851890323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843679610086207901260215 4265519415129311851890323)
            ·
              refine ⟨6398279122693967777835485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4265519415129311851890323 6398279122693967777835485)
              ·
                refine ⟨2399354671010237916688307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6398279122693967777835485 2399354671010237916688307)
                ·
                  refine ⟨3599032006515356875032461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399354671010237916688307 3599032006515356875032461)
                  ·
                    refine ⟨1349637002443258828137173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599032006515356875032461 1349637002443258828137173)
                    ·
                      rfl

theorem cell22_3942613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_3942613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942613 prefixEnd_3942613 := by exact prefixLift 3942613
  have htrace : WordTrace (prefixWord ++ tailWord_3942613) baseStart_3942613 baseEnd_3942613 := by
    simpa [prefixWord, tailWord_3942613, baseEnd_3942613] using wordTrace_append hprefix tailTrace_3942613
  have hstable : (prefixWord ++ tailWord_3942613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942613).length < 2 ^ (prefixWord ++ tailWord_3942613).sum := by decide
  have hdescent : baseEnd_3942613 < baseStart_3942613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942635 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 4, 3]
def baseStart_3942635 : Nat := 118140960795 + 3942635 * 2 ^ 59
def prefixEnd_3942635 : Nat := 4983230072969 + 3 ^ 40 * 3942635 * 2
def baseEnd_3942635 : Nat := 1349644533492858104087105

theorem tailTrace_3942635 : CollatzResearch.WordTrace tailWord_3942635 prefixEnd_3942635 1349644533492858104087105 := by
  unfold tailWord_3942635
  simp only [CollatzResearch.WordTrace]
  refine ⟨143799712071514218295101359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95866474714342812196734239 143799712071514218295101359)
  ·
    refine ⟨215699568107271327442652039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143799712071514218295101359 215699568107271327442652039)
    ·
      refine ⟨323549352160906991163978059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215699568107271327442652039 323549352160906991163978059)
      ·
        refine ⟨485324028241360486745967089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323549352160906991163978059 485324028241360486745967089)
        ·
          refine ⟨363993021181020365059475317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485324028241360486745967089 363993021181020365059475317)
          ·
            refine ⟨34124345735720659224325811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 363993021181020365059475317 34124345735720659224325811)
            ·
              refine ⟨51186518603580988836488717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34124345735720659224325811 51186518603580988836488717)
              ·
                refine ⟨19194944476342870813683269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51186518603580988836488717 19194944476342870813683269)
                ·
                  refine ⟨3599052089314288277565613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19194944476342870813683269 3599052089314288277565613)
                  ·
                    refine ⟨1349644533492858104087105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599052089314288277565613 1349644533492858104087105)
                    ·
                      rfl

theorem cell22_3942635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 3].length) (baseStart_3942635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942635 prefixEnd_3942635 := by exact prefixLift 3942635
  have htrace : WordTrace (prefixWord ++ tailWord_3942635) baseStart_3942635 baseEnd_3942635 := by
    simpa [prefixWord, tailWord_3942635, baseEnd_3942635] using wordTrace_append hprefix tailTrace_3942635
  have hstable : (prefixWord ++ tailWord_3942635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942635).length < 2 ^ (prefixWord ++ tailWord_3942635).sum := by decide
  have hdescent : baseEnd_3942635 < baseStart_3942635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942686 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3942686 : Nat := 118140960795 + 3942686 * 2 ^ 59
def prefixEnd_3942686 : Nat := 4983230072969 + 3 ^ 40 * 3942686 * 2
def baseEnd_3942686 : Nat := 1349661991835110971061949

theorem tailTrace_3942686 : CollatzResearch.WordTrace tailWord_3942686 prefixEnd_3942686 1349661991835110971061949 := by
  unfold tailWord_3942686
  simp only [CollatzResearch.WordTrace]
  refine ⟨17975196524291181750650989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95867714796219636003471941 17975196524291181750650989)
  ·
    refine ⟨6740698696609193156494121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17975196524291181750650989 6740698696609193156494121)
    ·
      refine ⟨5055524022456894867370591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6740698696609193156494121 5055524022456894867370591)
      ·
        refine ⟨7583286033685342301055887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5055524022456894867370591 7583286033685342301055887)
        ·
          refine ⟨11374929050528013451583831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7583286033685342301055887 11374929050528013451583831)
          ·
            refine ⟨17062393575792020177375747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11374929050528013451583831 17062393575792020177375747)
            ·
              refine ⟨25593590363688030266063621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17062393575792020177375747 25593590363688030266063621)
              ·
                refine ⟨4798798193191505674886929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25593590363688030266063621 4798798193191505674886929)
                ·
                  refine ⟨3599098644893629256165197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4798798193191505674886929 3599098644893629256165197)
                  ·
                    refine ⟨1349661991835110971061949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599098644893629256165197 1349661991835110971061949)
                    ·
                      rfl

theorem cell22_3942686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3942686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942686 prefixEnd_3942686 := by exact prefixLift 3942686
  have htrace : WordTrace (prefixWord ++ tailWord_3942686) baseStart_3942686 baseEnd_3942686 := by
    simpa [prefixWord, tailWord_3942686, baseEnd_3942686] using wordTrace_append hprefix tailTrace_3942686
  have hstable : (prefixWord ++ tailWord_3942686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942686).length < 2 ^ (prefixWord ++ tailWord_3942686).sum := by decide
  have hdescent : baseEnd_3942686 < baseStart_3942686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942892 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_3942892 : Nat := 118140960795 + 3942892 * 2 ^ 59
def prefixEnd_3942892 : Nat := 4983230072969 + 3 ^ 40 * 3942892 * 2
def baseEnd_3942892 : Nat := 1349732509844995100411317

theorem tailTrace_3942892 : CollatzResearch.WordTrace tailWord_3942892 prefixEnd_3942892 1349732509844995100411317 := by
  unfold tailWord_3942892
  simp only [CollatzResearch.WordTrace]
  refine ⟨71904542815791575593603465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95872723754388767458137953 71904542815791575593603465)
  ·
    refine ⟨53928407111843681695202599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71904542815791575593603465 53928407111843681695202599)
    ·
      refine ⟨80892610667765522542803899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53928407111843681695202599 80892610667765522542803899)
      ·
        refine ⟨121338916001648283814205849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80892610667765522542803899 121338916001648283814205849)
        ·
          refine ⟨91004187001236212860654387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121338916001648283814205849 91004187001236212860654387)
          ·
            refine ⟨136506280501854319290981581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91004187001236212860654387 136506280501854319290981581)
            ·
              refine ⟨51189855188195369734118093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136506280501854319290981581 51189855188195369734118093)
              ·
                refine ⟨19196195695573263650294285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51189855188195369734118093 19196195695573263650294285)
                ·
                  refine ⟨7198573385839973868860357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19196195695573263650294285 7198573385839973868860357)
                  ·
                    refine ⟨1349732509844995100411317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7198573385839973868860357 1349732509844995100411317)
                    ·
                      rfl

theorem cell22_3942892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_3942892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942892 prefixEnd_3942892 := by exact prefixLift 3942892
  have htrace : WordTrace (prefixWord ++ tailWord_3942892) baseStart_3942892 baseEnd_3942892 := by
    simpa [prefixWord, tailWord_3942892, baseEnd_3942892] using wordTrace_append hprefix tailTrace_3942892
  have hstable : (prefixWord ++ tailWord_3942892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942892).length < 2 ^ (prefixWord ++ tailWord_3942892).sum := by decide
  have hdescent : baseEnd_3942892 < baseStart_3942892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942909 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3942909 : Nat := 118140960795 + 3942909 * 2 ^ 59
def prefixEnd_3942909 : Nat := 4983230072969 + 3 ^ 40 * 3942909 * 2
def baseEnd_3942909 : Nat := 1349738329292412722736265

theorem tailTrace_3942909 : CollatzResearch.WordTrace tailWord_3942909 prefixEnd_3942909 1349738329292412722736265 := by
  unfold tailWord_3942909
  simp only [CollatzResearch.WordTrace]
  refine ⟨143809705672521563090575781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95873137115014375393717187 143809705672521563090575781)
  ·
    refine ⟨26964319813597793079482959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143809705672521563090575781 26964319813597793079482959)
    ·
      refine ⟨40446479720396689619224439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26964319813597793079482959 40446479720396689619224439)
      ·
        refine ⟨60669719580595034428836659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40446479720396689619224439 60669719580595034428836659)
        ·
          refine ⟨91004579370892551643254989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60669719580595034428836659 91004579370892551643254989)
          ·
            refine ⟨34126717264084706866220621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91004579370892551643254989 34126717264084706866220621)
            ·
              refine ⟨12797518974031765074832733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34126717264084706866220621 12797518974031765074832733)
              ·
                refine ⟨4799069615261911903062275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12797518974031765074832733 4799069615261911903062275)
                ·
                  refine ⟨7198604422892867854593413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799069615261911903062275 7198604422892867854593413)
                  ·
                    refine ⟨1349738329292412722736265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7198604422892867854593413 1349738329292412722736265)
                    ·
                      rfl

theorem cell22_3942909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3942909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942909 prefixEnd_3942909 := by exact prefixLift 3942909
  have htrace : WordTrace (prefixWord ++ tailWord_3942909) baseStart_3942909 baseEnd_3942909 := by
    simpa [prefixWord, tailWord_3942909, baseEnd_3942909] using wordTrace_append hprefix tailTrace_3942909
  have hstable : (prefixWord ++ tailWord_3942909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942909).length < 2 ^ (prefixWord ++ tailWord_3942909).sum := by decide
  have hdescent : baseEnd_3942909 < baseStart_3942909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942924 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 6]
def baseStart_3942924 : Nat := 118140960795 + 3942924 * 2 ^ 59
def prefixEnd_3942924 : Nat := 4983230072969 + 3 ^ 40 * 3942924 * 2
def baseEnd_3942924 : Nat := 449914488032985894537073

theorem tailTrace_3942924 : CollatzResearch.WordTrace tailWord_3942924 prefixEnd_3942924 449914488032985894537073 := by
  unfold tailWord_3942924
  simp only [CollatzResearch.WordTrace]
  refine ⟨71905126383733610326185913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95873501844978147101581217 71905126383733610326185913)
  ·
    refine ⟨53928844787800207744639435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71905126383733610326185913 53928844787800207744639435)
    ·
      refine ⟨80893267181700311616959153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53928844787800207744639435 80893267181700311616959153)
      ·
        refine ⟨60669950386275233712719365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80893267181700311616959153 60669950386275233712719365)
        ·
          refine ⟨11375615697426606321134881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60669950386275233712719365 11375615697426606321134881)
          ·
            refine ⟨8531711773069954740851161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11375615697426606321134881 8531711773069954740851161)
            ·
              refine ⟨6398783829802466055638371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8531711773069954740851161 6398783829802466055638371)
              ·
                refine ⟨9598175744703699083457557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6398783829802466055638371 9598175744703699083457557)
                ·
                  refine ⟨449914488032985894537073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9598175744703699083457557 449914488032985894537073)
                  ·
                    rfl

theorem cell22_3942924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_3942924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942924 prefixEnd_3942924 := by exact prefixLift 3942924
  have htrace : WordTrace (prefixWord ++ tailWord_3942924) baseStart_3942924 baseEnd_3942924 := by
    simpa [prefixWord, tailWord_3942924, baseEnd_3942924] using wordTrace_append hprefix tailTrace_3942924
  have hstable : (prefixWord ++ tailWord_3942924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942924).length < 2 ^ (prefixWord ++ tailWord_3942924).sum := by decide
  have hdescent : baseEnd_3942924 < baseStart_3942924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942937 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_3942937 : Nat := 118140960795 + 3942937 * 2 ^ 59
def prefixEnd_3942937 : Nat := 4983230072969 + 3 ^ 40 * 3942937 * 2
def baseEnd_3942937 : Nat := 1349747914264629983036179

theorem tailTrace_3942937 : CollatzResearch.WordTrace tailWord_3942937 prefixEnd_3942937 1349747914264629983036179 := by
  unfold tailWord_3942937
  simp only [CollatzResearch.WordTrace]
  refine ⟨143810726916420123872595065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95873817944280082581730043 143810726916420123872595065)
  ·
    refine ⟨107858045187315092904446299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143810726916420123872595065 107858045187315092904446299)
    ·
      refine ⟨161787067780972639356669449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107858045187315092904446299 161787067780972639356669449)
      ·
        refine ⟨121340300835729479517502087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161787067780972639356669449 121340300835729479517502087)
        ·
          refine ⟨182010451253594219276253131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121340300835729479517502087 182010451253594219276253131)
          ·
            refine ⟨273015676880391328914379697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182010451253594219276253131 273015676880391328914379697)
            ·
              refine ⟨204761757660293496685784773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273015676880391328914379697 204761757660293496685784773)
              ·
                refine ⟨38392829561305030628584645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204761757660293496685784773 38392829561305030628584645)
                ·
                  refine ⟨7198655542744693242859621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38392829561305030628584645 7198655542744693242859621)
                  ·
                    refine ⟨1349747914264629983036179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7198655542744693242859621 1349747914264629983036179)
                    ·
                      rfl

theorem cell22_3942937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_3942937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942937 prefixEnd_3942937 := by exact prefixLift 3942937
  have htrace : WordTrace (prefixWord ++ tailWord_3942937) baseStart_3942937 baseEnd_3942937 := by
    simpa [prefixWord, tailWord_3942937, baseEnd_3942937] using wordTrace_append hprefix tailTrace_3942937
  have hstable : (prefixWord ++ tailWord_3942937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942937).length < 2 ^ (prefixWord ++ tailWord_3942937).sum := by decide
  have hdescent : baseEnd_3942937 < baseStart_3942937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942954 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3942954 : Nat := 118140960795 + 3942954 * 2 ^ 59
def prefixEnd_3942954 : Nat := 4983230072969 + 3 ^ 40 * 3942954 * 2
def baseEnd_3942954 : Nat := 1349753733712047605361127

theorem tailTrace_3942954 : CollatzResearch.WordTrace tailWord_3942954 prefixEnd_3942954 1349753733712047605361127 := by
  unfold tailWord_3942954
  simp only [CollatzResearch.WordTrace]
  refine ⟨35952836739339633943990979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95874231304905690517309277 35952836739339633943990979)
  ·
    refine ⟨53929255109009450915986469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35952836739339633943990979 53929255109009450915986469)
    ·
      refine ⟨10111735332939272046747463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53929255109009450915986469 10111735332939272046747463)
      ·
        refine ⟨15167602999408908070121195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10111735332939272046747463 15167602999408908070121195)
        ·
          refine ⟨22751404499113362105181793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15167602999408908070121195 22751404499113362105181793)
          ·
            refine ⟨17063553374335021578886345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22751404499113362105181793 17063553374335021578886345)
            ·
              refine ⟨12797665030751266184164759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17063553374335021578886345 12797665030751266184164759)
              ·
                refine ⟨19196497546126899276247139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12797665030751266184164759 19196497546126899276247139)
                ·
                  refine ⟨28794746319190348914370709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19196497546126899276247139 28794746319190348914370709)
                  ·
                    refine ⟨1349753733712047605361127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28794746319190348914370709 1349753733712047605361127)
                    ·
                      rfl

theorem cell22_3942954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3942954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3942954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3942954 prefixEnd_3942954 := by exact prefixLift 3942954
  have htrace : WordTrace (prefixWord ++ tailWord_3942954) baseStart_3942954 baseEnd_3942954 := by
    simpa [prefixWord, tailWord_3942954, baseEnd_3942954] using wordTrace_append hprefix tailTrace_3942954
  have hstable : (prefixWord ++ tailWord_3942954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942954).length < 2 ^ (prefixWord ++ tailWord_3942954).sum := by decide
  have hdescent : baseEnd_3942954 < baseStart_3942954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943018 : List Nat := [3, 1, 3, 2, 1, 1, 2, 5, 1, 3]
def baseStart_3943018 : Nat := 118140960795 + 3943018 * 2 ^ 59
def prefixEnd_3943018 : Nat := 4983230072969 + 3 ^ 40 * 3943018 * 2
def baseEnd_3943018 : Nat := 1349775642219972771760931

theorem tailTrace_3943018 : CollatzResearch.WordTrace tailWord_3943018 prefixEnd_3943018 1349775642219972771760931 := by
  unfold tailWord_3943018
  simp only [CollatzResearch.WordTrace]
  refine ⟨35953420307281668676573427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95875787486084449804195805 35953420307281668676573427)
  ·
    refine ⟨53930130460922503014860141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35953420307281668676573427 53930130460922503014860141)
    ·
      refine ⟨20223798922845938630572553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53930130460922503014860141 20223798922845938630572553)
      ·
        refine ⟨15167849192134453972929415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20223798922845938630572553 15167849192134453972929415)
        ·
          refine ⟨22751773788201680959394123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15167849192134453972929415 22751773788201680959394123)
          ·
            refine ⟨34127660682302521439091185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22751773788201680959394123 34127660682302521439091185)
            ·
              refine ⟨25595745511726891079318389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34127660682302521439091185 25595745511726891079318389)
              ·
                refine ⟨2399601141724396038686099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25595745511726891079318389 2399601141724396038686099)
                ·
                  refine ⟨3599401712586594058029149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399601141724396038686099 3599401712586594058029149)
                  ·
                    refine ⟨1349775642219972771760931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599401712586594058029149 1349775642219972771760931)
                    ·
                      rfl

theorem cell22_3943018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_3943018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943018 prefixEnd_3943018 := by exact prefixLift 3943018
  have htrace : WordTrace (prefixWord ++ tailWord_3943018) baseStart_3943018 baseEnd_3943018 := by
    simpa [prefixWord, tailWord_3943018, baseEnd_3943018] using wordTrace_append hprefix tailTrace_3943018
  have hstable : (prefixWord ++ tailWord_3943018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943018).length < 2 ^ (prefixWord ++ tailWord_3943018).sum := by decide
  have hdescent : baseEnd_3943018 < baseStart_3943018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943082 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_3943082 : Nat := 118140960795 + 3943082 * 2 ^ 59
def prefixEnd_3943082 : Nat := 4983230072969 + 3 ^ 40 * 3943082 * 2
def baseEnd_3943082 : Nat := 449932516909299312720245

theorem tailTrace_3943082 : CollatzResearch.WordTrace tailWord_3943082 prefixEnd_3943082 449932516909299312720245 := by
  unfold tailWord_3943082
  simp only [CollatzResearch.WordTrace]
  refine ⟨35954003875223703409155875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95877343667263209091082333 35954003875223703409155875)
  ·
    refine ⟨53931005812835555113733813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35954003875223703409155875 53931005812835555113733813)
    ·
      refine ⟨5056031794953333291912545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53931005812835555113733813 5056031794953333291912545)
      ·
        refine ⟨3792023846214999968934409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5056031794953333291912545 3792023846214999968934409)
        ·
          refine ⟨2844017884661249976700807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3792023846214999968934409 2844017884661249976700807)
          ·
            refine ⟨4266026826991874965051211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844017884661249976700807 4266026826991874965051211)
            ·
              refine ⟨6399040240487812447576817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266026826991874965051211 6399040240487812447576817)
              ·
                refine ⟨4799280180365859335682613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6399040240487812447576817 4799280180365859335682613)
                ·
                  refine ⟨449932516909299312720245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4799280180365859335682613 449932516909299312720245)
                  ·
                    rfl

theorem cell22_3943082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_3943082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943082 prefixEnd_3943082 := by exact prefixLift 3943082
  have htrace : WordTrace (prefixWord ++ tailWord_3943082) baseStart_3943082 baseEnd_3943082 := by
    simpa [prefixWord, tailWord_3943082, baseEnd_3943082] using wordTrace_append hprefix tailTrace_3943082
  have hstable : (prefixWord ++ tailWord_3943082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943082).length < 2 ^ (prefixWord ++ tailWord_3943082).sum := by decide
  have hdescent : baseEnd_3943082 < baseStart_3943082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943091 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 4, 3]
def baseStart_3943091 : Nat := 118140960795 + 3943091 * 2 ^ 59
def prefixEnd_3943091 : Nat := 4983230072969 + 3 ^ 40 * 3943091 * 2
def baseEnd_3943091 : Nat := 1349800631611824914685707

theorem tailTrace_3943091 : CollatzResearch.WordTrace tailWord_3943091 prefixEnd_3943091 1349800631611824914685707 := by
  unfold tailWord_3943091
  simp only [CollatzResearch.WordTrace]
  refine ⟨143816343757862208173701127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95877562505241472115800751 143816343757862208173701127)
  ·
    refine ⟨215724515636793312260551691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143816343757862208173701127 215724515636793312260551691)
    ·
      refine ⟨323586773455189968390827537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215724515636793312260551691 323586773455189968390827537)
      ·
        refine ⟨242690080091392476293120653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323586773455189968390827537 242690080091392476293120653)
        ·
          refine ⟨91008780034272178609920245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242690080091392476293120653 91008780034272178609920245)
          ·
            refine ⟨8532073128213016744680023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91008780034272178609920245 8532073128213016744680023)
            ·
              refine ⟨12798109692319525117020035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8532073128213016744680023 12798109692319525117020035)
              ·
                refine ⟨19197164538479287675530053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12798109692319525117020035 19197164538479287675530053)
                ·
                  refine ⟨3599468350964866439161885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19197164538479287675530053 3599468350964866439161885)
                  ·
                    refine ⟨1349800631611824914685707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599468350964866439161885 1349800631611824914685707)
                    ·
                      rfl

theorem cell22_3943091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 3].length) (baseStart_3943091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943091 prefixEnd_3943091 := by exact prefixLift 3943091
  have htrace : WordTrace (prefixWord ++ tailWord_3943091) baseStart_3943091 baseEnd_3943091 := by
    simpa [prefixWord, tailWord_3943091, baseEnd_3943091] using wordTrace_append hprefix tailTrace_3943091
  have hstable : (prefixWord ++ tailWord_3943091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943091).length < 2 ^ (prefixWord ++ tailWord_3943091).sum := by decide
  have hdescent : baseEnd_3943091 < baseStart_3943091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943093 : List Nat := [1, 3, 3, 3, 1, 1, 2, 4, 4]
def baseStart_3943093 : Nat := 118140960795 + 3943093 * 2 ^ 59
def prefixEnd_3943093 : Nat := 4983230072969 + 3 ^ 40 * 3943093 * 2
def baseEnd_3943093 : Nat := 449933772084232525378567

theorem tailTrace_3943093 : CollatzResearch.WordTrace tailWord_3943093 prefixEnd_3943093 449933772084232525378567 := by
  unfold tailWord_3943093
  simp only [CollatzResearch.WordTrace]
  refine ⟨143816416703854962515273933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95877611135903308343515955 143816416703854962515273933)
  ·
    refine ⟨53931156263945610943227725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143816416703854962515273933 53931156263945610943227725)
    ·
      refine ⟨20224183598979604103710397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53931156263945610943227725 20224183598979604103710397)
      ·
        refine ⟨7584068849617351538891399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20224183598979604103710397 7584068849617351538891399)
        ·
          refine ⟨11376103274426027308337099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7584068849617351538891399 11376103274426027308337099)
          ·
            refine ⟨17064154911639040962505649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11376103274426027308337099 17064154911639040962505649)
            ·
              refine ⟨12798116183729280721879237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17064154911639040962505649 12798116183729280721879237)
              ·
                refine ⟨2399646784449240135352357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12798116183729280721879237 2399646784449240135352357)
                ·
                  refine ⟨449933772084232525378567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399646784449240135352357 449933772084232525378567)
                  ·
                    rfl

theorem cell22_3943093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_3943093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943093 prefixEnd_3943093 := by exact prefixLift 3943093
  have htrace : WordTrace (prefixWord ++ tailWord_3943093) baseStart_3943093 baseEnd_3943093 := by
    simpa [prefixWord, tailWord_3943093, baseEnd_3943093] using wordTrace_append hprefix tailTrace_3943093
  have hstable : (prefixWord ++ tailWord_3943093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943093).length < 2 ^ (prefixWord ++ tailWord_3943093).sum := by decide
  have hdescent : baseEnd_3943093 < baseStart_3943093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943108 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_3943108 : Nat := 118140960795 + 3943108 * 2 ^ 59
def prefixEnd_3943108 : Nat := 4983230072969 + 3 ^ 40 * 3943108 * 2
def baseEnd_3943108 : Nat := 1349806451059242537010655

theorem tailTrace_3943108 : CollatzResearch.WordTrace tailWord_3943108 prefixEnd_3943108 1349806451059242537010655 := by
  unfold tailWord_3943108
  simp only [CollatzResearch.WordTrace]
  refine ⟨71908481899400310038534989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95877975865867080051379985 71908481899400310038534989)
  ·
    refine ⟨26965680712275116264450621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71908481899400310038534989 26965680712275116264450621)
    ·
      refine ⟨10112130267103168599168983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26965680712275116264450621 10112130267103168599168983)
      ·
        refine ⟨15168195400654752898753475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10112130267103168599168983 15168195400654752898753475)
        ·
          refine ⟨22752293100982129348130213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15168195400654752898753475 22752293100982129348130213)
          ·
            refine ⟨4266054956434149252774415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22752293100982129348130213 4266054956434149252774415)
            ·
              refine ⟨6399082434651223879161623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266054956434149252774415 6399082434651223879161623)
              ·
                refine ⟨9598623651976835818742435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399082434651223879161623 9598623651976835818742435)
                ·
                  refine ⟨14397935477965253728113653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9598623651976835818742435 14397935477965253728113653)
                  ·
                    refine ⟨1349806451059242537010655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14397935477965253728113653 1349806451059242537010655)
                    ·
                      rfl

theorem cell22_3943108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_3943108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943108 prefixEnd_3943108 := by exact prefixLift 3943108
  have htrace : WordTrace (prefixWord ++ tailWord_3943108) baseStart_3943108 baseEnd_3943108 := by
    simpa [prefixWord, tailWord_3943108, baseEnd_3943108] using wordTrace_append hprefix tailTrace_3943108
  have hstable : (prefixWord ++ tailWord_3943108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943108).length < 2 ^ (prefixWord ++ tailWord_3943108).sum := by decide
  have hdescent : baseEnd_3943108 < baseStart_3943108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943204 : List Nat := [2, 3, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_3943204 : Nat := 118140960795 + 3943204 * 2 ^ 59
def prefixEnd_3943204 : Nat := 4983230072969 + 3 ^ 40 * 3943204 * 2
def baseEnd_3943204 : Nat := 1349839313821130286610361

theorem tailTrace_3943204 : CollatzResearch.WordTrace tailWord_3943204 prefixEnd_3943204 1349839313821130286610361 := by
  unfold tailWord_3943204
  simp only [CollatzResearch.WordTrace]
  refine ⟨71910232603226414236282333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95880310137635218981709777 71910232603226414236282333)
  ·
    refine ⟨26966337226209905338605875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71910232603226414236282333 26966337226209905338605875)
    ·
      refine ⟨40449505839314858007908813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26966337226209905338605875 40449505839314858007908813)
      ·
        refine ⟨15168564689743071752965805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40449505839314858007908813 15168564689743071752965805)
        ·
          refine ⟨5688211758653651907362177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15168564689743071752965805 5688211758653651907362177)
          ·
            refine ⟨4266158818990238930521633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5688211758653651907362177 4266158818990238930521633)
            ·
              refine ⟨3199619114242679197891225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4266158818990238930521633 3199619114242679197891225)
              ·
                refine ⟨2399714335682009398418419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3199619114242679197891225 2399714335682009398418419)
                ·
                  refine ⟨3599571503523014097627629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399714335682009398418419 3599571503523014097627629)
                  ·
                    refine ⟨1349839313821130286610361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599571503523014097627629 1349839313821130286610361)
                    ·
                      rfl

theorem cell22_3943204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_3943204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943204 prefixEnd_3943204 := by exact prefixLift 3943204
  have htrace : WordTrace (prefixWord ++ tailWord_3943204) baseStart_3943204 baseEnd_3943204 := by
    simpa [prefixWord, tailWord_3943204, baseEnd_3943204] using wordTrace_append hprefix tailTrace_3943204
  have hstable : (prefixWord ++ tailWord_3943204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943204).length < 2 ^ (prefixWord ++ tailWord_3943204).sum := by decide
  have hdescent : baseEnd_3943204 < baseStart_3943204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943241 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_3943241 : Nat := 118140960795 + 3943241 * 2 ^ 59
def prefixEnd_3943241 : Nat := 4983230072969 + 3 ^ 40 * 3943241 * 2
def baseEnd_3943241 : Nat := 1349851979677274523435247

theorem tailTrace_3943241 : CollatzResearch.WordTrace tailWord_3943241 prefixEnd_3943241 1349851979677274523435247 := by
  unfold tailWord_3943241
  simp only [CollatzResearch.WordTrace]
  refine ⟨143821814707318783791661577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95881209804879189194441051 143821814707318783791661577)
  ·
    refine ⟨107866361030489087843746183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143821814707318783791661577 107866361030489087843746183)
    ·
      refine ⟨161799541545733631765619275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107866361030489087843746183 161799541545733631765619275)
      ·
        refine ⟨242699312318600447648428913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161799541545733631765619275 242699312318600447648428913)
        ·
          refine ⟨182024484238950335736321685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242699312318600447648428913 182024484238950335736321685)
          ·
            refine ⟨8532397698700796987640079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182024484238950335736321685 8532397698700796987640079)
            ·
              refine ⟨12798596548051195481460119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8532397698700796987640079 12798596548051195481460119)
              ·
                refine ⟨19197894822076793222190179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12798596548051195481460119 19197894822076793222190179)
                ·
                  refine ⟨28796842233115189833285269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19197894822076793222190179 28796842233115189833285269)
                  ·
                    refine ⟨1349851979677274523435247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28796842233115189833285269 1349851979677274523435247)
                    ·
                      rfl

theorem cell22_3943241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_3943241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943241 prefixEnd_3943241 := by exact prefixLift 3943241
  have htrace : WordTrace (prefixWord ++ tailWord_3943241) baseStart_3943241 baseEnd_3943241 := by
    simpa [prefixWord, tailWord_3943241, baseEnd_3943241] using wordTrace_append hprefix tailTrace_3943241
  have hstable : (prefixWord ++ tailWord_3943241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943241).length < 2 ^ (prefixWord ++ tailWord_3943241).sum := by decide
  have hdescent : baseEnd_3943241 < baseStart_3943241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943260 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3943260 : Nat := 118140960795 + 3943260 * 2 ^ 59
def prefixEnd_3943260 : Nat := 4983230072969 + 3 ^ 40 * 3943260 * 2
def baseEnd_3943260 : Nat := 1349858483765564807210189

theorem tailTrace_3943260 : CollatzResearch.WordTrace tailWord_3943260 prefixEnd_3943260 1349858483765564807210189 := by
  unfold tailWord_3943260
  simp only [CollatzResearch.WordTrace]
  refine ⟨71911253847124975018301617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95881671796166633357735489 71911253847124975018301617)
  ·
    refine ⟨53933440385343731263726213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71911253847124975018301617 53933440385343731263726213)
    ·
      refine ⟨10112520072251949611948665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53933440385343731263726213 10112520072251949611948665)
      ·
        refine ⟨7584390054188962208961499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10112520072251949611948665 7584390054188962208961499)
        ·
          refine ⟨11376585081283443313442249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7584390054188962208961499 11376585081283443313442249)
          ·
            refine ⟨8532438810962582485081687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11376585081283443313442249 8532438810962582485081687)
            ·
              refine ⟨12798658216443873727622531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8532438810962582485081687 12798658216443873727622531)
              ·
                refine ⟨19197987324665810591433797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12798658216443873727622531 19197987324665810591433797)
                ·
                  refine ⟨3599622623374839485893837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19197987324665810591433797 3599622623374839485893837)
                  ·
                    refine ⟨1349858483765564807210189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599622623374839485893837 1349858483765564807210189)
                    ·
                      rfl

theorem cell22_3943260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3943260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943260 prefixEnd_3943260 := by exact prefixLift 3943260
  have htrace : WordTrace (prefixWord ++ tailWord_3943260) baseStart_3943260 baseEnd_3943260 := by
    simpa [prefixWord, tailWord_3943260, baseEnd_3943260] using wordTrace_append hprefix tailTrace_3943260
  have hstable : (prefixWord ++ tailWord_3943260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943260).length < 2 ^ (prefixWord ++ tailWord_3943260).sum := by decide
  have hdescent : baseEnd_3943260 < baseStart_3943260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943301 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 7]
def baseStart_3943301 : Nat := 118140960795 + 3943301 * 2 ^ 59
def prefixEnd_3943301 : Nat := 4983230072969 + 3 ^ 40 * 3943301 * 2
def baseEnd_3943301 : Nat := 449957506301151455645021

theorem tailTrace_3943301 : CollatzResearch.WordTrace tailWord_3943301 prefixEnd_3943301 449957506301151455645021 := by
  unfold tailWord_3943301
  simp only [CollatzResearch.WordTrace]
  refine ⟨143824003087101414038845757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95882668724734276025897171 143824003087101414038845757)
  ·
    refine ⟨53934001157663030264567159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143824003087101414038845757 53934001157663030264567159)
    ·
      refine ⟨80901001736494545396850739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53934001157663030264567159 80901001736494545396850739)
      ·
        refine ⟨121351502604741818095276109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80901001736494545396850739 121351502604741818095276109)
        ·
          refine ⟨45506813476778181785728541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121351502604741818095276109 45506813476778181785728541)
          ·
            refine ⟨17065055053791818169648203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45506813476778181785728541 17065055053791818169648203)
            ·
              refine ⟨25597582580687727254472305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17065055053791818169648203 25597582580687727254472305)
              ·
                refine ⟨19198186935515795440854229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25597582580687727254472305 19198186935515795440854229)
                ·
                  refine ⟨449957506301151455645021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19198186935515795440854229 449957506301151455645021)
                  ·
                    rfl

theorem cell22_3943301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_3943301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943301 prefixEnd_3943301 := by exact prefixLift 3943301
  have htrace : WordTrace (prefixWord ++ tailWord_3943301) baseStart_3943301 baseEnd_3943301 := by
    simpa [prefixWord, tailWord_3943301, baseEnd_3943301] using wordTrace_append hprefix tailTrace_3943301
  have hstable : (prefixWord ++ tailWord_3943301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943301).length < 2 ^ (prefixWord ++ tailWord_3943301).sum := by decide
  have hdescent : baseEnd_3943301 < baseStart_3943301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943322 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 3, 3]
def baseStart_3943322 : Nat := 118140960795 + 3943322 * 2 ^ 59
def prefixEnd_3943322 : Nat := 4983230072969 + 3 ^ 40 * 3943322 * 2
def baseEnd_3943322 : Nat := 1349879707632617312159999

theorem tailTrace_3943322 : CollatzResearch.WordTrace tailWord_3943322 prefixEnd_3943322 1349879707632617312159999 := by
  unfold tailWord_3943322
  simp only [CollatzResearch.WordTrace]
  refine ⟨35956192255006333656340055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95883179346683556416906813 35956192255006333656340055)
  ·
    refine ⟨53934288382509500484510083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35956192255006333656340055 53934288382509500484510083)
    ·
      refine ⟨80901432573764250726765125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53934288382509500484510083 80901432573764250726765125)
      ·
        refine ⟨15169018607580797011268461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80901432573764250726765125 15169018607580797011268461)
        ·
          refine ⟨5688381977842798879225673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15169018607580797011268461 5688381977842798879225673)
          ·
            refine ⟨4266286483382099159419255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5688381977842798879225673 4266286483382099159419255)
            ·
              refine ⟨6399429725073148739128883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266286483382099159419255 6399429725073148739128883)
              ·
                refine ⟨9599144587609723108693325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399429725073148739128883 9599144587609723108693325)
                ·
                  refine ⟨3599679220353646165759997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9599144587609723108693325 3599679220353646165759997)
                  ·
                    refine ⟨1349879707632617312159999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599679220353646165759997 1349879707632617312159999)
                    ·
                      rfl

theorem cell22_3943322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_3943322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943322 prefixEnd_3943322 := by exact prefixLift 3943322
  have htrace : WordTrace (prefixWord ++ tailWord_3943322) baseStart_3943322 baseEnd_3943322 := by
    simpa [prefixWord, tailWord_3943322, baseEnd_3943322] using wordTrace_append hprefix tailTrace_3943322
  have hstable : (prefixWord ++ tailWord_3943322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943322).length < 2 ^ (prefixWord ++ tailWord_3943322).sum := by decide
  have hdescent : baseEnd_3943322 < baseStart_3943322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943335 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 5]
def baseStart_3943335 : Nat := 118140960795 + 3943335 * 2 ^ 59
def prefixEnd_3943335 : Nat := 4983230072969 + 3 ^ 40 * 3943335 * 2
def baseEnd_3943335 : Nat := 449961385932763203861653

theorem tailTrace_3943335 : CollatzResearch.WordTrace tailWord_3943335 prefixEnd_3943335 449961385932763203861653 := by
  unfold tailWord_3943335
  simp only [CollatzResearch.WordTrace]
  refine ⟨143825243168978237845583459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95883495445985491897055639 143825243168978237845583459)
  ·
    refine ⟨215737864753467356768375189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143825243168978237845583459 215737864753467356768375189)
    ·
      refine ⟨10112712410318782348517587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215737864753467356768375189 10112712410318782348517587)
      ·
        refine ⟨15169068615478173522776381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10112712410318782348517587 15169068615478173522776381)
        ·
          refine ⟨5688400730804315071041143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15169068615478173522776381 5688400730804315071041143)
          ·
            refine ⟨8532601096206472606561715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5688400730804315071041143 8532601096206472606561715)
            ·
              refine ⟨12798901644309708909842573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8532601096206472606561715 12798901644309708909842573)
              ·
                refine ⟨4799588116616140841190965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12798901644309708909842573 4799588116616140841190965)
                ·
                  refine ⟨449961385932763203861653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4799588116616140841190965 449961385932763203861653)
                  ·
                    rfl

theorem cell22_3943335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 5].length) (baseStart_3943335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943335 prefixEnd_3943335 := by exact prefixLift 3943335
  have htrace : WordTrace (prefixWord ++ tailWord_3943335) baseStart_3943335 baseEnd_3943335 := by
    simpa [prefixWord, tailWord_3943335, baseEnd_3943335] using wordTrace_append hprefix tailTrace_3943335
  have hstable : (prefixWord ++ tailWord_3943335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943335).length < 2 ^ (prefixWord ++ tailWord_3943335).sum := by decide
  have hdescent : baseEnd_3943335 < baseStart_3943335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943373 : List Nat := [1, 6, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3943373 : Nat := 118140960795 + 3943373 * 2 ^ 59
def prefixEnd_3943373 : Nat := 4983230072969 + 3 ^ 40 * 3943373 * 2
def baseEnd_3943373 : Nat := 1349897165974870179134843

theorem tailTrace_3943373 : CollatzResearch.WordTrace tailWord_3943373 prefixEnd_3943373 1349897165974870179134843 := by
  unfold tailWord_3943373
  simp only [CollatzResearch.WordTrace]
  refine ⟨143826629142840570335466773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95884419428560380223644515 143826629142840570335466773)
  ·
    refine ⟨6741873241070651734475005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143826629142840570335466773 6741873241070651734475005)
    ·
      refine ⟨2528202465401494400428127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6741873241070651734475005 2528202465401494400428127)
      ·
        refine ⟨3792303698102241600642191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528202465401494400428127 3792303698102241600642191)
        ·
          refine ⟨5688455547153362400963287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3792303698102241600642191 5688455547153362400963287)
          ·
            refine ⟨8532683320730043601444931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5688455547153362400963287 8532683320730043601444931)
            ·
              refine ⟨12799024981095065402167397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8532683320730043601444931 12799024981095065402167397)
              ·
                refine ⟨2399817183955324762906387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12799024981095065402167397 2399817183955324762906387)
                ·
                  refine ⟨3599725775932987144359581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399817183955324762906387 3599725775932987144359581)
                  ·
                    refine ⟨1349897165974870179134843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599725775932987144359581 1349897165974870179134843)
                    ·
                      rfl

theorem cell22_3943373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3943373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943373 prefixEnd_3943373 := by exact prefixLift 3943373
  have htrace : WordTrace (prefixWord ++ tailWord_3943373) baseStart_3943373 baseEnd_3943373 := by
    simpa [prefixWord, tailWord_3943373, baseEnd_3943373] using wordTrace_append hprefix tailTrace_3943373
  have hstable : (prefixWord ++ tailWord_3943373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943373).length < 2 ^ (prefixWord ++ tailWord_3943373).sum := by decide
  have hdescent : baseEnd_3943373 < baseStart_3943373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943376 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_3943376 : Nat := 118140960795 + 3943376 * 2 ^ 59
def prefixEnd_3943376 : Nat := 4983230072969 + 3 ^ 40 * 3943376 * 2
def baseEnd_3943376 : Nat := 1349898192936179171309833

theorem tailTrace_3943376 : CollatzResearch.WordTrace tailWord_3943376 prefixEnd_3943376 1349898192936179171309833 := by
  unfold tailWord_3943376
  simp only [CollatzResearch.WordTrace]
  refine ⟨71913369280914850923912991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95884492374553134565217321 71913369280914850923912991)
  ·
    refine ⟨107870053921372276385869487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71913369280914850923912991 107870053921372276385869487)
    ·
      refine ⟨161805080882058414578804231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107870053921372276385869487 161805080882058414578804231)
      ·
        refine ⟨242707621323087621868206347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161805080882058414578804231 242707621323087621868206347)
        ·
          refine ⟨364061431984631432802309521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242707621323087621868206347 364061431984631432802309521)
          ·
            refine ⟨273046073988473574601732141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364061431984631432802309521 273046073988473574601732141)
            ·
              refine ⟨102392277745677590475649553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273046073988473574601732141 102392277745677590475649553)
              ·
                refine ⟨76794208309258192856737165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102392277745677590475649553 76794208309258192856737165)
                ·
                  refine ⟨28797828115971822321276437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76794208309258192856737165 28797828115971822321276437)
                  ·
                    refine ⟨1349898192936179171309833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28797828115971822321276437 1349898192936179171309833)
                    ·
                      rfl

theorem cell22_3943376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_3943376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943376 prefixEnd_3943376 := by exact prefixLift 3943376
  have htrace : WordTrace (prefixWord ++ tailWord_3943376) baseStart_3943376 baseEnd_3943376 := by
    simpa [prefixWord, tailWord_3943376, baseEnd_3943376] using wordTrace_append hprefix tailTrace_3943376
  have hstable : (prefixWord ++ tailWord_3943376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943376).length < 2 ^ (prefixWord ++ tailWord_3943376).sum := by decide
  have hdescent : baseEnd_3943376 < baseStart_3943376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943395 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 2, 3]
def baseStart_3943395 : Nat := 118140960795 + 3943395 * 2 ^ 59
def prefixEnd_3943395 : Nat := 4983230072969 + 3 ^ 40 * 3943395 * 2
def baseEnd_3943395 : Nat := 1349904697024469455084775

theorem tailTrace_3943395 : CollatzResearch.WordTrace tailWord_3943395 prefixEnd_3943395 1349904697024469455084775 := by
  unfold tailWord_3943395
  simp only [CollatzResearch.WordTrace]
  refine ⟨143827431548760868092767639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95884954365840578728511759 143827431548760868092767639)
  ·
    refine ⟨215741147323141302139151459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143827431548760868092767639 215741147323141302139151459)
    ·
      refine ⟨323611720984711953208727189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215741147323141302139151459 323611720984711953208727189)
      ·
        refine ⟨15169299421158372806659087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 323611720984711953208727189 15169299421158372806659087)
        ·
          refine ⟨22753949131737559209988631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15169299421158372806659087 22753949131737559209988631)
          ·
            refine ⟨34130923697606338814982947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22753949131737559209988631 34130923697606338814982947)
            ·
              refine ⟨51196385546409508222474421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34130923697606338814982947 51196385546409508222474421)
              ·
                refine ⟨4799661144975891395856977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51196385546409508222474421 4799661144975891395856977)
                ·
                  refine ⟨3599745858731918546892733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4799661144975891395856977 3599745858731918546892733)
                  ·
                    refine ⟨1349904697024469455084775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599745858731918546892733 1349904697024469455084775)
                    ·
                      rfl

theorem cell22_3943395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 3].length) (baseStart_3943395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943395 prefixEnd_3943395 := by exact prefixLift 3943395
  have htrace : WordTrace (prefixWord ++ tailWord_3943395) baseStart_3943395 baseEnd_3943395 := by
    simpa [prefixWord, tailWord_3943395, baseEnd_3943395] using wordTrace_append hprefix tailTrace_3943395
  have hstable : (prefixWord ++ tailWord_3943395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943395).length < 2 ^ (prefixWord ++ tailWord_3943395).sum := by decide
  have hdescent : baseEnd_3943395 < baseStart_3943395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943530 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_3943530 : Nat := 118140960795 + 3943530 * 2 ^ 59
def prefixEnd_3943530 : Nat := 4983230072969 + 3 ^ 40 * 3943530 * 2
def baseEnd_3943530 : Nat := 1349950910283374102959361

theorem tailTrace_3943530 : CollatzResearch.WordTrace tailWord_3943530 prefixEnd_3943530 1349950910283374102959361 := by
  unfold tailWord_3943530
  simp only [CollatzResearch.WordTrace]
  refine ⟨35958088850817946537233011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95888236935514524099288029 35958088850817946537233011)
  ·
    refine ⟨53937133276226919805849517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35958088850817946537233011 53937133276226919805849517)
    ·
      refine ⟨20226424978585094927193569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53937133276226919805849517 20226424978585094927193569)
      ·
        refine ⟨15169818733938821195395177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20226424978585094927193569 15169818733938821195395177)
        ·
          refine ⟨11377364050454115896546383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15169818733938821195395177 11377364050454115896546383)
          ·
            refine ⟨17066046075681173844819575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11377364050454115896546383 17066046075681173844819575)
            ·
              refine ⟨25599069113521760767229363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17066046075681173844819575 25599069113521760767229363)
              ·
                refine ⟨38398603670282641150844045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25599069113521760767229363 38398603670282641150844045)
                ·
                  refine ⟨14399476376355990431566517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38398603670282641150844045 14399476376355990431566517)
                  ·
                    refine ⟨1349950910283374102959361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14399476376355990431566517 1349950910283374102959361)
                    ·
                      rfl

theorem cell22_3943530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_3943530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943530 prefixEnd_3943530 := by exact prefixLift 3943530
  have htrace : WordTrace (prefixWord ++ tailWord_3943530) baseStart_3943530 baseEnd_3943530 := by
    simpa [prefixWord, tailWord_3943530, baseEnd_3943530] using wordTrace_append hprefix tailTrace_3943530
  have hstable : (prefixWord ++ tailWord_3943530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943530).length < 2 ^ (prefixWord ++ tailWord_3943530).sum := by decide
  have hdescent : baseEnd_3943530 < baseStart_3943530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943534 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_3943534 : Nat := 118140960795 + 3943534 * 2 ^ 59
def prefixEnd_3943534 : Nat := 4983230072969 + 3 ^ 40 * 3943534 * 2
def baseEnd_3943534 : Nat := 1349952279565119425859349

theorem tailTrace_3943534 : CollatzResearch.WordTrace tailWord_3943534 prefixEnd_3943534 1349952279565119425859349 := by
  unfold tailWord_3943534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17979062661907161854009707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95888334196838196554718437 17979062661907161854009707)
  ·
    refine ⟨26968593992860742781014561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17979062661907161854009707 26968593992860742781014561)
    ·
      refine ⟨20226445494645557085760921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26968593992860742781014561 20226445494645557085760921)
      ·
        refine ⟨15169834120984167814320691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20226445494645557085760921 15169834120984167814320691)
        ·
          refine ⟨22754751181476251721481037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15169834120984167814320691 22754751181476251721481037)
          ·
            refine ⟨8533031693053594395555389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22754751181476251721481037 8533031693053594395555389)
            ·
              refine ⟨3199886884895097898333271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8533031693053594395555389 3199886884895097898333271)
              ·
                refine ⟨4799830327342646847499907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199886884895097898333271 4799830327342646847499907)
                ·
                  refine ⟨7199745491013970271249861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799830327342646847499907 7199745491013970271249861)
                  ·
                    refine ⟨1349952279565119425859349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7199745491013970271249861 1349952279565119425859349)
                    ·
                      rfl

theorem cell22_3943534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_3943534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943534 prefixEnd_3943534 := by exact prefixLift 3943534
  have htrace : WordTrace (prefixWord ++ tailWord_3943534) baseStart_3943534 baseEnd_3943534 := by
    simpa [prefixWord, tailWord_3943534, baseEnd_3943534] using wordTrace_append hprefix tailTrace_3943534
  have hstable : (prefixWord ++ tailWord_3943534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943534).length < 2 ^ (prefixWord ++ tailWord_3943534).sum := by decide
  have hdescent : baseEnd_3943534 < baseStart_3943534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943609 : List Nat := [1, 2, 1, 4, 1, 3, 2, 4, 1, 3]
def baseStart_3943609 : Nat := 118140960795 + 3943609 * 2 ^ 59
def prefixEnd_3943609 : Nat := 4983230072969 + 3 ^ 40 * 3943609 * 2
def baseEnd_3943609 : Nat := 1349977953597844230234119

theorem tailTrace_3943609 : CollatzResearch.WordTrace tailWord_3943609 prefixEnd_3943609 1349977953597844230234119 := by
  unfold tailWord_3943609
  simp only [CollatzResearch.WordTrace]
  refine ⟨143835236769985582641057881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95890157846657055094038587 143835236769985582641057881)
  ·
    refine ⟨107876427577489186980793411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143835236769985582641057881 107876427577489186980793411)
    ·
      refine ⟨161814641366233780471190117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107876427577489186980793411 161814641366233780471190117)
      ·
        refine ⟨30340245256168833838348147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161814641366233780471190117 30340245256168833838348147)
        ·
          refine ⟨45510367884253250757522221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30340245256168833838348147 45510367884253250757522221)
          ·
            refine ⟨17066387956594969034070833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45510367884253250757522221 17066387956594969034070833)
            ·
              refine ⟨12799790967446226775553125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17066387956594969034070833 12799790967446226775553125)
              ·
                refine ⟨2399960806396167520416211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12799790967446226775553125 2399960806396167520416211)
                ·
                  refine ⟨3599941209594251280624317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399960806396167520416211 3599941209594251280624317)
                  ·
                    refine ⟨1349977953597844230234119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599941209594251280624317 1349977953597844230234119)
                    ·
                      rfl

theorem cell22_3943609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 1, 3].length) (baseStart_3943609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943609 prefixEnd_3943609 := by exact prefixLift 3943609
  have htrace : WordTrace (prefixWord ++ tailWord_3943609) baseStart_3943609 baseEnd_3943609 := by
    simpa [prefixWord, tailWord_3943609, baseEnd_3943609] using wordTrace_append hprefix tailTrace_3943609
  have hstable : (prefixWord ++ tailWord_3943609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943609).length < 2 ^ (prefixWord ++ tailWord_3943609).sum := by decide
  have hdescent : baseEnd_3943609 < baseStart_3943609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943652 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_3943652 : Nat := 118140960795 + 3943652 * 2 ^ 59
def prefixEnd_3943652 : Nat := 4983230072969 + 3 ^ 40 * 3943652 * 2
def baseEnd_3943652 : Nat := 1349992673376606451408987

theorem tailTrace_3943652 : CollatzResearch.WordTrace tailWord_3943652 prefixEnd_3943652 1349992673376606451408987 := by
  unfold tailWord_3943652
  simp only [CollatzResearch.WordTrace]
  refine ⟨71918402554414900492436605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95891203405886533989915473 71918402554414900492436605)
  ·
    refine ⟨26969400957905587684663727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71918402554414900492436605 26969400957905587684663727)
    ·
      refine ⟨40454101436858381526995591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26969400957905587684663727 40454101436858381526995591)
      ·
        refine ⟨60681152155287572290493387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40454101436858381526995591 60681152155287572290493387)
        ·
          refine ⟨91021728232931358435740081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60681152155287572290493387 91021728232931358435740081)
          ·
            refine ⟨68266296174698518826805061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91021728232931358435740081 68266296174698518826805061)
            ·
              refine ⟨12799930532755972280025949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68266296174698518826805061 12799930532755972280025949)
              ·
                refine ⟨4799973949783489605009731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12799930532755972280025949 4799973949783489605009731)
                ·
                  refine ⟨7199960924675234407514597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799973949783489605009731 7199960924675234407514597)
                  ·
                    refine ⟨1349992673376606451408987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7199960924675234407514597 1349992673376606451408987)
                    ·
                      rfl

theorem cell22_3943652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_3943652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943652 prefixEnd_3943652 := by exact prefixLift 3943652
  have htrace : WordTrace (prefixWord ++ tailWord_3943652) baseStart_3943652 baseEnd_3943652 := by
    simpa [prefixWord, tailWord_3943652, baseEnd_3943652] using wordTrace_append hprefix tailTrace_3943652
  have hstable : (prefixWord ++ tailWord_3943652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943652).length < 2 ^ (prefixWord ++ tailWord_3943652).sum := by decide
  have hdescent : baseEnd_3943652 < baseStart_3943652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943667 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 6]
def baseStart_3943667 : Nat := 118140960795 + 3943667 * 2 ^ 59
def prefixEnd_3943667 : Nat := 4983230072969 + 3 ^ 40 * 3943667 * 2
def baseEnd_3943667 : Nat := 449999269394383804094647

theorem tailTrace_3943667 : CollatzResearch.WordTrace tailWord_3943667 prefixEnd_3943667 449999269394383804094647 := by
  unfold tailWord_3943667
  simp only [CollatzResearch.WordTrace]
  refine ⟨143837352203775458546669255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95891568135850305697779503 143837352203775458546669255)
  ·
    refine ⟨215756028305663187820003883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143837352203775458546669255 215756028305663187820003883)
    ·
      refine ⟨323634042458494781730005825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215756028305663187820003883 323634042458494781730005825)
      ·
        refine ⟨242725531843871086297504369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323634042458494781730005825 242725531843871086297504369)
        ·
          refine ⟨182044148882903314723128277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242725531843871086297504369 182044148882903314723128277)
          ·
            refine ⟨4266659739443046438823319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 182044148882903314723128277 4266659739443046438823319)
            ·
              refine ⟨6399989609164569658234979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266659739443046438823319 6399989609164569658234979)
              ·
                refine ⟨9599984413746854487352469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399989609164569658234979 9599984413746854487352469)
                ·
                  refine ⟨449999269394383804094647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9599984413746854487352469 449999269394383804094647)
                  ·
                    rfl

theorem cell22_3943667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 6].length) (baseStart_3943667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943667 prefixEnd_3943667 := by exact prefixLift 3943667
  have htrace : WordTrace (prefixWord ++ tailWord_3943667) baseStart_3943667 baseEnd_3943667 := by
    simpa [prefixWord, tailWord_3943667, baseEnd_3943667] using wordTrace_append hprefix tailTrace_3943667
  have hstable : (prefixWord ++ tailWord_3943667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943667).length < 2 ^ (prefixWord ++ tailWord_3943667).sum := by decide
  have hdescent : baseEnd_3943667 < baseStart_3943667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943680 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_3943680 : Nat := 118140960795 + 3943680 * 2 ^ 59
def prefixEnd_3943680 : Nat := 4983230072969 + 3 ^ 40 * 3943680 * 2
def baseEnd_3943680 : Nat := 1350002258348823711708901

theorem tailTrace_3943680 : CollatzResearch.WordTrace tailWord_3943680 prefixEnd_3943680 1350002258348823711708901 := by
  unfold tailWord_3943680
  simp only [CollatzResearch.WordTrace]
  refine ⟨71918913176364180883446247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95891884235152241177928329 71918913176364180883446247)
  ·
    refine ⟨107878369764546271325169371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71918913176364180883446247 107878369764546271325169371)
    ·
      refine ⟨161817554646819406987754057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107878369764546271325169371 161817554646819406987754057)
      ·
        refine ⟨121363165985114555240815543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161817554646819406987754057 121363165985114555240815543)
        ·
          refine ⟨182044748977671832861223315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121363165985114555240815543 182044748977671832861223315)
          ·
            refine ⟨273067123466507749291834973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182044748977671832861223315 273067123466507749291834973)
            ·
              refine ⟨102400171299940405984438115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273067123466507749291834973 102400171299940405984438115)
              ·
                refine ⟨153600256949910608976657173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102400171299940405984438115 153600256949910608976657173)
                ·
                  refine ⟨7200012044527059795780805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153600256949910608976657173 7200012044527059795780805)
                  ·
                    refine ⟨1350002258348823711708901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7200012044527059795780805 1350002258348823711708901)
                    ·
                      rfl

theorem cell22_3943680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_3943680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943680 prefixEnd_3943680 := by exact prefixLift 3943680
  have htrace : WordTrace (prefixWord ++ tailWord_3943680) baseStart_3943680 baseEnd_3943680 := by
    simpa [prefixWord, tailWord_3943680, baseEnd_3943680] using wordTrace_append hprefix tailTrace_3943680
  have hstable : (prefixWord ++ tailWord_3943680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943680).length < 2 ^ (prefixWord ++ tailWord_3943680).sum := by decide
  have hdescent : baseEnd_3943680 < baseStart_3943680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943697 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 2, 4]
def baseStart_3943697 : Nat := 118140960795 + 3943697 * 2 ^ 59
def prefixEnd_3943697 : Nat := 4983230072969 + 3 ^ 40 * 3943697 * 2
def baseEnd_3943697 : Nat := 1350008077796241334033849

theorem tailTrace_3943697 : CollatzResearch.WordTrace tailWord_3943697 prefixEnd_3943697 1350008077796241334033849 := by
  unfold tailWord_3943697
  simp only [CollatzResearch.WordTrace]
  refine ⟨143838446393666773670261345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95892297595777849113507563 143838446393666773670261345)
  ·
    refine ⟨107878834795250080252696009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143838446393666773670261345 107878834795250080252696009)
    ·
      refine ⟨80909126096437560189522007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107878834795250080252696009 80909126096437560189522007)
      ·
        refine ⟨121363689144656340284283011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80909126096437560189522007 121363689144656340284283011)
        ·
          refine ⟨182045533716984510426424517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121363689144656340284283011 182045533716984510426424517)
          ·
            refine ⟨34133537571934595704954597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182045533716984510426424517 34133537571934595704954597)
            ·
              refine ⟨6400038294737736694678987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34133537571934595704954597 6400038294737736694678987)
              ·
                refine ⟨9600057442106605042018481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6400038294737736694678987 9600057442106605042018481)
                ·
                  refine ⟨7200043081579953781513861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9600057442106605042018481 7200043081579953781513861)
                  ·
                    refine ⟨1350008077796241334033849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7200043081579953781513861 1350008077796241334033849)
                    ·
                      rfl

theorem cell22_3943697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_3943697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943697 prefixEnd_3943697 := by exact prefixLift 3943697
  have htrace : WordTrace (prefixWord ++ tailWord_3943697) baseStart_3943697 baseEnd_3943697 := by
    simpa [prefixWord, tailWord_3943697, baseEnd_3943697] using wordTrace_append hprefix tailTrace_3943697
  have hstable : (prefixWord ++ tailWord_3943697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943697).length < 2 ^ (prefixWord ++ tailWord_3943697).sum := by decide
  have hdescent : baseEnd_3943697 < baseStart_3943697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943712 : List Nat := [2, 1, 1, 5, 4, 9]
def baseStart_3943712 : Nat := 118140960795 + 3943712 * 2 ^ 59
def prefixEnd_3943712 : Nat := 4983230072969 + 3 ^ 40 * 3943712 * 2
def baseEnd_3943712 : Nat := 16666829785219583887763

theorem tailTrace_3943712 : CollatzResearch.WordTrace tailWord_3943712 prefixEnd_3943712 16666829785219583887763 := by
  unfold tailWord_3943712
  simp only [CollatzResearch.WordTrace]
  refine ⟨71919496744306215616028695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95892662325741620821371593 71919496744306215616028695)
  ·
    refine ⟨107879245116459323424043043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71919496744306215616028695 107879245116459323424043043)
    ·
      refine ⟨161818867674688985136064565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107879245116459323424043043 161818867674688985136064565)
      ·
        refine ⟨15170518844502092356506053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161818867674688985136064565 15170518844502092356506053)
        ·
          refine ⟨2844472283344142316844885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15170518844502092356506053 2844472283344142316844885)
          ·
            refine ⟨16666829785219583887763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2844472283344142316844885 16666829785219583887763)
            ·
              rfl

theorem cell22_3943712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 9].length) (baseStart_3943712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943712 prefixEnd_3943712 := by exact prefixLift 3943712
  have htrace : WordTrace (prefixWord ++ tailWord_3943712) baseStart_3943712 baseEnd_3943712 := by
    simpa [prefixWord, tailWord_3943712, baseEnd_3943712] using wordTrace_append hprefix tailTrace_3943712
  have hstable : (prefixWord ++ tailWord_3943712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943712).length < 2 ^ (prefixWord ++ tailWord_3943712).sum := by decide
  have hdescent : baseEnd_3943712 < baseStart_3943712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943727 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 3, 3]
def baseStart_3943727 : Nat := 118140960795 + 3943727 * 2 ^ 59
def prefixEnd_3943727 : Nat := 4983230072969 + 3 ^ 40 * 3943727 * 2
def baseEnd_3943727 : Nat := 1350018347409331255783757

theorem tailTrace_3943727 : CollatzResearch.WordTrace tailWord_3943727 prefixEnd_3943727 1350018347409331255783757 := by
  unfold tailWord_3943727
  simp only [CollatzResearch.WordTrace]
  refine ⟨143839540583558088793853435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95893027055705392529235623 143839540583558088793853435)
  ·
    refine ⟨215759310875337133190780153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143839540583558088793853435 215759310875337133190780153)
    ·
      refine ⟨161819483156502849893085115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215759310875337133190780153 161819483156502849893085115)
      ·
        refine ⟨242729224734754274839627673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161819483156502849893085115 242729224734754274839627673)
        ·
          refine ⟨182046918551065706129720755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242729224734754274839627673 182046918551065706129720755)
          ·
            refine ⟨273070377826598559194581133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182046918551065706129720755 273070377826598559194581133)
            ·
              refine ⟨102401391684974459697967925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273070377826598559194581133 102401391684974459697967925)
              ·
                refine ⟨9600130470466355596684493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102401391684974459697967925 9600130470466355596684493)
                ·
                  refine ⟨3600048926424883348756685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9600130470466355596684493 3600048926424883348756685)
                  ·
                    refine ⟨1350018347409331255783757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3600048926424883348756685 1350018347409331255783757)
                    ·
                      rfl

theorem cell22_3943727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 3].length) (baseStart_3943727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943727 prefixEnd_3943727 := by exact prefixLift 3943727
  have htrace : WordTrace (prefixWord ++ tailWord_3943727) baseStart_3943727 baseEnd_3943727 := by
    simpa [prefixWord, tailWord_3943727, baseEnd_3943727] using wordTrace_append hprefix tailTrace_3943727
  have hstable : (prefixWord ++ tailWord_3943727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943727).length < 2 ^ (prefixWord ++ tailWord_3943727).sum := by decide
  have hdescent : baseEnd_3943727 < baseStart_3943727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943742 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3943742 : Nat := 118140960795 + 3943742 * 2 ^ 59
def prefixEnd_3943742 : Nat := 4983230072969 + 3 ^ 40 * 3943742 * 2
def baseEnd_3943742 : Nat := 1350023482215876216658711

theorem tailTrace_3943742 : CollatzResearch.WordTrace tailWord_3943742 prefixEnd_3943742 1350023482215876216658711 := by
  unfold tailWord_3943742
  simp only [CollatzResearch.WordTrace]
  refine ⟨17980010959812968294456185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95893391785669164237099653 17980010959812968294456185)
  ·
    refine ⟨13485008219859726220842139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17980010959812968294456185 13485008219859726220842139)
    ·
      refine ⟨20227512329789589331263209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13485008219859726220842139 20227512329789589331263209)
      ·
        refine ⟨15170634247342191998447407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20227512329789589331263209 15170634247342191998447407)
        ·
          refine ⟨22755951371013287997671111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15170634247342191998447407 22755951371013287997671111)
          ·
            refine ⟨34133927056519931996506667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22755951371013287997671111 34133927056519931996506667)
            ·
              refine ⟨51200890584779897994760001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34133927056519931996506667 51200890584779897994760001)
              ·
                refine ⟨38400667938584923496070001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51200890584779897994760001 38400667938584923496070001)
                ·
                  refine ⟨28800500953938692622052501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38400667938584923496070001 28800500953938692622052501)
                  ·
                    refine ⟨1350023482215876216658711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28800500953938692622052501 1350023482215876216658711)
                    ·
                      rfl

theorem cell22_3943742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3943742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943742 prefixEnd_3943742 := by exact prefixLift 3943742
  have htrace : WordTrace (prefixWord ++ tailWord_3943742) baseStart_3943742 baseEnd_3943742 := by
    simpa [prefixWord, tailWord_3943742, baseEnd_3943742] using wordTrace_append hprefix tailTrace_3943742
  have hstable : (prefixWord ++ tailWord_3943742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943742).length < 2 ^ (prefixWord ++ tailWord_3943742).sum := by decide
  have hdescent : baseEnd_3943742 < baseStart_3943742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943761 : List Nat := [1, 2, 2, 1, 4, 1, 4, 3, 1, 3]
def baseStart_3943761 : Nat := 118140960795 + 3943761 * 2 ^ 59
def prefixEnd_3943761 : Nat := 4983230072969 + 3 ^ 40 * 3943761 * 2
def baseEnd_3943761 : Nat := 1350029986304166500433653

theorem tailTrace_3943761 : CollatzResearch.WordTrace tailWord_3943761 prefixEnd_3943761 1350029986304166500433653 := by
  unfold tailWord_3943761
  simp only [CollatzResearch.WordTrace]
  refine ⟨143840780665434912600591137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95893853776956608400394091 143840780665434912600591137)
  ·
    refine ⟨107880585499076184450443353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143840780665434912600591137 107880585499076184450443353)
    ·
      refine ⟨80910439124307138337832515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107880585499076184450443353 80910439124307138337832515)
      ·
        refine ⟨121365658686460707506748773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80910439124307138337832515 121365658686460707506748773)
        ·
          refine ⟨22756061003711382657515395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121365658686460707506748773 22756061003711382657515395)
          ·
            refine ⟨34134091505567073986273093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22756061003711382657515395 34134091505567073986273093)
            ·
              refine ⟨6400142157293826372426205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34134091505567073986273093 6400142157293826372426205)
              ·
                refine ⟨2400053308985184889659827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6400142157293826372426205 2400053308985184889659827)
                ·
                  refine ⟨3600079963477777334489741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400053308985184889659827 3600079963477777334489741)
                  ·
                    refine ⟨1350029986304166500433653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3600079963477777334489741 1350029986304166500433653)
                    ·
                      rfl

theorem cell22_3943761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_3943761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943761 prefixEnd_3943761 := by exact prefixLift 3943761
  have htrace : WordTrace (prefixWord ++ tailWord_3943761) baseStart_3943761 baseEnd_3943761 := by
    simpa [prefixWord, tailWord_3943761, baseEnd_3943761] using wordTrace_append hprefix tailTrace_3943761
  have hstable : (prefixWord ++ tailWord_3943761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943761).length < 2 ^ (prefixWord ++ tailWord_3943761).sum := by decide
  have hdescent : baseEnd_3943761 < baseStart_3943761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943804 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_3943804 : Nat := 118140960795 + 3943804 * 2 ^ 59
def prefixEnd_3943804 : Nat := 4983230072969 + 3 ^ 40 * 3943804 * 2
def baseEnd_3943804 : Nat := 1350044706082928721608521

theorem tailTrace_3943804 : CollatzResearch.WordTrace tailWord_3943804 prefixEnd_3943804 1350044706082928721608521 := by
  unfold tailWord_3943804
  simp only [CollatzResearch.WordTrace]
  refine ⟨71921174502139565472203233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95894899336186087296270977 71921174502139565472203233)
  ·
    refine ⟨53940880876604674104152425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71921174502139565472203233 53940880876604674104152425)
    ·
      refine ⟨40455660657453505578114319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53940880876604674104152425 40455660657453505578114319)
      ·
        refine ⟨60683490986180258367171479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40455660657453505578114319 60683490986180258367171479)
        ·
          refine ⟨91025236479270387550757219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60683490986180258367171479 91025236479270387550757219)
          ·
            refine ⟨136537854718905581326135829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91025236479270387550757219 136537854718905581326135829)
            ·
              refine ⟨6400211939948699124662617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136537854718905581326135829 6400211939948699124662617)
              ·
                refine ⟨4800158954961524343496963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6400211939948699124662617 4800158954961524343496963)
                ·
                  refine ⟨7200238432442286515245445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4800158954961524343496963 7200238432442286515245445)
                  ·
                    refine ⟨1350044706082928721608521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7200238432442286515245445 1350044706082928721608521)
                    ·
                      rfl

theorem cell22_3943804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_3943804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943804 prefixEnd_3943804 := by exact prefixLift 3943804
  have htrace : WordTrace (prefixWord ++ tailWord_3943804) baseStart_3943804 baseEnd_3943804 := by
    simpa [prefixWord, tailWord_3943804, baseEnd_3943804] using wordTrace_append hprefix tailTrace_3943804
  have hstable : (prefixWord ++ tailWord_3943804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943804).length < 2 ^ (prefixWord ++ tailWord_3943804).sum := by decide
  have hdescent : baseEnd_3943804 < baseStart_3943804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943834 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 4, 3]
def baseStart_3943834 : Nat := 118140960795 + 3943834 * 2 ^ 59
def prefixEnd_3943834 : Nat := 4983230072969 + 3 ^ 40 * 3943834 * 2
def baseEnd_3943834 : Nat := 1350054975696018643358429

theorem tailTrace_3943834 : CollatzResearch.WordTrace tailWord_3943834 prefixEnd_3943834 1350054975696018643358429 := by
  unfold tailWord_3943834
  simp only [CollatzResearch.WordTrace]
  refine ⟨35960860798542611516999639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95895628796113630711999037 35960860798542611516999639)
  ·
    refine ⟨53941291197813917275499459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35960860798542611516999639 53941291197813917275499459)
    ·
      refine ⟨80911936796720875913249189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53941291197813917275499459 80911936796720875913249189)
      ·
        refine ⟨15170988149385164233734223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80911936796720875913249189 15170988149385164233734223)
        ·
          refine ⟨22756482224077746350601335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15170988149385164233734223 22756482224077746350601335)
          ·
            refine ⟨34134723336116619525902003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22756482224077746350601335 34134723336116619525902003)
            ·
              refine ⟨51202085004174929288853005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34134723336116619525902003 51202085004174929288853005)
              ·
                refine ⟨19200781876565598483319877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51202085004174929288853005 19200781876565598483319877)
                ·
                  refine ⟨3600146601856049715622477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19200781876565598483319877 3600146601856049715622477)
                  ·
                    refine ⟨1350054975696018643358429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3600146601856049715622477 1350054975696018643358429)
                    ·
                      rfl

theorem cell22_3943834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_3943834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943834 prefixEnd_3943834 := by exact prefixLift 3943834
  have htrace : WordTrace (prefixWord ++ tailWord_3943834) baseStart_3943834 baseEnd_3943834 := by
    simpa [prefixWord, tailWord_3943834, baseEnd_3943834] using wordTrace_append hprefix tailTrace_3943834
  have hstable : (prefixWord ++ tailWord_3943834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943834).length < 2 ^ (prefixWord ++ tailWord_3943834).sum := by decide
  have hdescent : baseEnd_3943834 < baseStart_3943834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943984 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_3943984 : Nat := 118140960795 + 3943984 * 2 ^ 59
def prefixEnd_3943984 : Nat := 4983230072969 + 3 ^ 40 * 3943984 * 2
def baseEnd_3943984 : Nat := 1350106323761468252107969

theorem tailTrace_3943984 : CollatzResearch.WordTrace tailWord_3943984 prefixEnd_3943984 1350106323761468252107969 := by
  unfold tailWord_3943984
  simp only [CollatzResearch.WordTrace]
  refine ⟨71924457071813510842979503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95899276095751347790639337 71924457071813510842979503)
  ·
    refine ⟨107886685607720266264469255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71924457071813510842979503 107886685607720266264469255)
    ·
      refine ⟨161830028411580399396703883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107886685607720266264469255 161830028411580399396703883)
      ·
        refine ⟨242745042617370599095055825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161830028411580399396703883 242745042617370599095055825)
        ·
          refine ⟨182058781963027949321291869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242745042617370599095055825 182058781963027949321291869)
          ·
            refine ⟨68272043236135480995484451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182058781963027949321291869 68272043236135480995484451)
            ·
              refine ⟨102408064854203221493226677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68272043236135480995484451 102408064854203221493226677)
              ·
                refine ⟨9600756080081552014990001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102408064854203221493226677 9600756080081552014990001)
                ·
                  refine ⟨7200567060061164011242501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9600756080081552014990001 7200567060061164011242501)
                  ·
                    refine ⟨1350106323761468252107969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7200567060061164011242501 1350106323761468252107969)
                    ·
                      rfl

theorem cell22_3943984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_3943984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943984 prefixEnd_3943984 := by exact prefixLift 3943984
  have htrace : WordTrace (prefixWord ++ tailWord_3943984) baseStart_3943984 baseEnd_3943984 := by
    simpa [prefixWord, tailWord_3943984, baseEnd_3943984] using wordTrace_append hprefix tailTrace_3943984
  have hstable : (prefixWord ++ tailWord_3943984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943984).length < 2 ^ (prefixWord ++ tailWord_3943984).sum := by decide
  have hdescent : baseEnd_3943984 < baseStart_3943984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943999 : List Nat := [1, 1, 2, 2, 3, 5, 8]
def baseStart_3943999 : Nat := 118140960795 + 3943999 * 2 ^ 59
def prefixEnd_3943999 : Nat := 4983230072969 + 3 ^ 40 * 3943999 * 2
def baseEnd_3943999 : Nat := 50004128095111600480849

theorem tailTrace_3943999 : CollatzResearch.WordTrace tailWord_3943999 prefixEnd_3943999 50004128095111600480849 := by
  unfold tailWord_3943999
  simp only [CollatzResearch.WordTrace]
  refine ⟨143849461238572679247755051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95899640825715119498503367 143849461238572679247755051)
  ·
    refine ⟨215774191857859018871632577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143849461238572679247755051 215774191857859018871632577)
    ·
      refine ⟨161830643893394264153724433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215774191857859018871632577 161830643893394264153724433)
      ·
        refine ⟨121372982920045698115293325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161830643893394264153724433 121372982920045698115293325)
        ·
          refine ⟨45514868595017136793234997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121372982920045698115293325 45514868595017136793234997)
          ·
            refine ⟨4267018930782856574365781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45514868595017136793234997 4267018930782856574365781)
            ·
              refine ⟨50004128095111600480849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4267018930782856574365781 50004128095111600480849)
              ·
                rfl

theorem cell22_3943999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 8].length) (baseStart_3943999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3943999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3943999 prefixEnd_3943999 := by exact prefixLift 3943999
  have htrace : WordTrace (prefixWord ++ tailWord_3943999) baseStart_3943999 baseEnd_3943999 := by
    simpa [prefixWord, tailWord_3943999, baseEnd_3943999] using wordTrace_append hprefix tailTrace_3943999
  have hstable : (prefixWord ++ tailWord_3943999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943999).length < 2 ^ (prefixWord ++ tailWord_3943999).sum := by decide
  have hdescent : baseEnd_3943999 < baseStart_3943999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944001 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3944001 : Nat := 118140960795 + 3944001 * 2 ^ 59
def prefixEnd_3944001 : Nat := 4983230072969 + 3 ^ 40 * 3944001 * 2
def baseEnd_3944001 : Nat := 1350112143208885874432917

theorem tailTrace_3944001 : CollatzResearch.WordTrace tailWord_3944001 prefixEnd_3944001 1350112143208885874432917 := by
  unfold tailWord_3944001
  simp only [CollatzResearch.WordTrace]
  refine ⟨143849534184565433589327857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95899689456376955726218571 143849534184565433589327857)
  ·
    refine ⟨107887150638424075191995893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143849534184565433589327857 107887150638424075191995893)
    ·
      refine ⟨10114420372352257049249615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107887150638424075191995893 10114420372352257049249615)
      ·
        refine ⟨15171630558528385573874423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10114420372352257049249615 15171630558528385573874423)
        ·
          refine ⟨22757445837792578360811635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15171630558528385573874423 22757445837792578360811635)
          ·
            refine ⟨34136168756688867541217453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22757445837792578360811635 34136168756688867541217453)
            ·
              refine ⟨12801063283758325327956545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34136168756688867541217453 12801063283758325327956545)
              ·
                refine ⟨9600797462818743995967409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12801063283758325327956545 9600797462818743995967409)
                ·
                  refine ⟨7200598097114057996975557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9600797462818743995967409 7200598097114057996975557)
                  ·
                    refine ⟨1350112143208885874432917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7200598097114057996975557 1350112143208885874432917)
                    ·
                      rfl

theorem cell22_3944001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3944001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944001 prefixEnd_3944001 := by exact prefixLift 3944001
  have htrace : WordTrace (prefixWord ++ tailWord_3944001) baseStart_3944001 baseEnd_3944001 := by
    simpa [prefixWord, tailWord_3944001, baseEnd_3944001] using wordTrace_append hprefix tailTrace_3944001
  have hstable : (prefixWord ++ tailWord_3944001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944001).length < 2 ^ (prefixWord ++ tailWord_3944001).sum := by decide
  have hdescent : baseEnd_3944001 < baseStart_3944001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944059 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 2, 5]
def baseStart_3944059 : Nat := 118140960795 + 3944059 * 2 ^ 59
def prefixEnd_3944059 : Nat := 4983230072969 + 3 ^ 40 * 3944059 * 2
def baseEnd_3944059 : Nat := 1350131997794193056482739

theorem tailTrace_3944059 : CollatzResearch.WordTrace tailWord_3944059 prefixEnd_3944059 1350131997794193056482739 := by
  unfold tailWord_3944059
  simp only [CollatzResearch.WordTrace]
  refine ⟨143851649618355309494939231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95901099745570206329959487 143851649618355309494939231)
  ·
    refine ⟨215777474427532964242408847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143851649618355309494939231 215777474427532964242408847)
    ·
      refine ⟨323666211641299446363613271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215777474427532964242408847 323666211641299446363613271)
      ·
        refine ⟨485499317461949169545419907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323666211641299446363613271 485499317461949169545419907)
        ·
          refine ⟨728248976192923754318129861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485499317461949169545419907 728248976192923754318129861)
          ·
            refine ⟨136546683036173203934649349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 728248976192923754318129861 136546683036173203934649349)
            ·
              refine ⟨25602503069282475737746753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136546683036173203934649349 25602503069282475737746753)
              ·
                refine ⟨19201877301961856803310065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25602503069282475737746753 19201877301961856803310065)
                ·
                  refine ⟨14401407976471392602482549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19201877301961856803310065 14401407976471392602482549)
                  ·
                    refine ⟨1350131997794193056482739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14401407976471392602482549 1350131997794193056482739)
                    ·
                      rfl

theorem cell22_3944059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_3944059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944059 prefixEnd_3944059 := by exact prefixLift 3944059
  have htrace : WordTrace (prefixWord ++ tailWord_3944059) baseStart_3944059 baseEnd_3944059 := by
    simpa [prefixWord, tailWord_3944059, baseEnd_3944059] using wordTrace_append hprefix tailTrace_3944059
  have hstable : (prefixWord ++ tailWord_3944059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944059).length < 2 ^ (prefixWord ++ tailWord_3944059).sum := by decide
  have hdescent : baseEnd_3944059 < baseStart_3944059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944061 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 5]
def baseStart_3944061 : Nat := 118140960795 + 3944061 * 2 ^ 59
def prefixEnd_3944061 : Nat := 4983230072969 + 3 ^ 40 * 3944061 * 2
def baseEnd_3944061 : Nat := 450044227478355239310911

theorem tailTrace_3944061 : CollatzResearch.WordTrace tailWord_3944061 prefixEnd_3944061 450044227478355239310911 := by
  unfold tailWord_3944061
  simp only [CollatzResearch.WordTrace]
  refine ⟨143851722564348063836512037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95901148376232042557674691 143851722564348063836512037)
  ·
    refine ⟨26972197980815261969346007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143851722564348063836512037 26972197980815261969346007)
    ·
      refine ⟨40458296971222892954019011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26972197980815261969346007 40458296971222892954019011)
      ·
        refine ⟨60687445456834339431028517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40458296971222892954019011 60687445456834339431028517)
        ·
          refine ⟨11378896023156438643317847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60687445456834339431028517 11378896023156438643317847)
          ·
            refine ⟨17068344034734657964976771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11378896023156438643317847 17068344034734657964976771)
            ·
              refine ⟨25602516052101986947465157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17068344034734657964976771 25602516052101986947465157)
              ·
                refine ⟨4800471759769122552649717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25602516052101986947465157 4800471759769122552649717)
                ·
                  refine ⟨450044227478355239310911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4800471759769122552649717 450044227478355239310911)
                  ·
                    rfl

theorem cell22_3944061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_3944061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944061 prefixEnd_3944061 := by exact prefixLift 3944061
  have htrace : WordTrace (prefixWord ++ tailWord_3944061) baseStart_3944061 baseEnd_3944061 := by
    simpa [prefixWord, tailWord_3944061, baseEnd_3944061] using wordTrace_append hprefix tailTrace_3944061
  have hstable : (prefixWord ++ tailWord_3944061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944061).length < 2 ^ (prefixWord ++ tailWord_3944061).sum := by decide
  have hdescent : baseEnd_3944061 < baseStart_3944061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944065 : List Nat := [1, 2, 4, 2, 1, 3, 1, 4, 1, 3]
def baseStart_3944065 : Nat := 118140960795 + 3944065 * 2 ^ 59
def prefixEnd_3944065 : Nat := 4983230072969 + 3 ^ 40 * 3944065 * 2
def baseEnd_3944065 : Nat := 1350134051716811040832721

theorem tailTrace_3944065 : CollatzResearch.WordTrace tailWord_3944065 prefixEnd_3944065 1350134051716811040832721 := by
  unfold tailWord_3944065
  simp only [CollatzResearch.WordTrace]
  refine ⟨143851868456333572519657649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95901245637555715013105099 143851868456333572519657649)
  ·
    refine ⟨107888901342250179389743237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143851868456333572519657649 107888901342250179389743237)
    ·
      refine ⟨20229169001671908635576857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107888901342250179389743237 20229169001671908635576857)
      ·
        refine ⟨15171876751253931476682643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20229169001671908635576857 15171876751253931476682643)
        ·
          refine ⟨22757815126880897215023965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15171876751253931476682643 22757815126880897215023965)
          ·
            refine ⟨8534180672580336455633987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22757815126880897215023965 8534180672580336455633987)
            ·
              refine ⟨12801271008870504683450981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534180672580336455633987 12801271008870504683450981)
              ·
                refine ⟨2400238314163219628147059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12801271008870504683450981 2400238314163219628147059)
                ·
                  refine ⟨3600357471244829442220589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400238314163219628147059 3600357471244829442220589)
                  ·
                    refine ⟨1350134051716811040832721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3600357471244829442220589 1350134051716811040832721)
                    ·
                      rfl

theorem cell22_3944065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_3944065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944065 prefixEnd_3944065 := by exact prefixLift 3944065
  have htrace : WordTrace (prefixWord ++ tailWord_3944065) baseStart_3944065 baseEnd_3944065 := by
    simpa [prefixWord, tailWord_3944065, baseEnd_3944065] using wordTrace_append hprefix tailTrace_3944065
  have hstable : (prefixWord ++ tailWord_3944065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944065).length < 2 ^ (prefixWord ++ tailWord_3944065).sum := by decide
  have hdescent : baseEnd_3944065 < baseStart_3944065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944183 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 3, 3]
def baseStart_3944183 : Nat := 118140960795 + 3944183 * 2 ^ 59
def prefixEnd_3944183 : Nat := 4983230072969 + 3 ^ 40 * 3944183 * 2
def baseEnd_3944183 : Nat := 1350174445528298066382359

theorem tailTrace_3944183 : CollatzResearch.WordTrace tailWord_3944183 prefixEnd_3944183 1350174445528298066382359 := by
  unfold tailWord_3944183
  simp only [CollatzResearch.WordTrace]
  refine ⟨143856172269906078672453203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95904114846604052448302135 143856172269906078672453203)
  ·
    refine ⟨215784258404859118008679805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143856172269906078672453203 215784258404859118008679805)
    ·
      refine ⟨80919096901822169253254927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215784258404859118008679805 80919096901822169253254927)
      ·
        refine ⟨121378645352733253879882391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80919096901822169253254927 121378645352733253879882391)
        ·
          refine ⟨182067968029099880819823587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121378645352733253879882391 182067968029099880819823587)
          ·
            refine ⟨273101952043649821229735381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182067968029099880819823587 273101952043649821229735381)
            ·
              refine ⟨6400827001023042685071923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 273101952043649821229735381 6400827001023042685071923)
              ·
                refine ⟨9601240501534564027607885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6400827001023042685071923 9601240501534564027607885)
                ·
                  refine ⟨3600465188075461510352957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9601240501534564027607885 3600465188075461510352957)
                  ·
                    refine ⟨1350174445528298066382359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3600465188075461510352957 1350174445528298066382359)
                    ·
                      rfl

theorem cell22_3944183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_3944183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944183 prefixEnd_3944183 := by exact prefixLift 3944183
  have htrace : WordTrace (prefixWord ++ tailWord_3944183) baseStart_3944183 baseEnd_3944183 := by
    simpa [prefixWord, tailWord_3944183, baseEnd_3944183] using wordTrace_append hprefix tailTrace_3944183
  have hstable : (prefixWord ++ tailWord_3944183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944183).length < 2 ^ (prefixWord ++ tailWord_3944183).sum := by decide
  have hdescent : baseEnd_3944183 < baseStart_3944183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944273 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_3944273 : Nat := 118140960795 + 3944273 * 2 ^ 59
def prefixEnd_3944273 : Nat := 4983230072969 + 3 ^ 40 * 3944273 * 2
def baseEnd_3944273 : Nat := 1350205254367567831632083

theorem tailTrace_3944273 : CollatzResearch.WordTrace tailWord_3944273 prefixEnd_3944273 1350205254367567831632083 := by
  unfold tailWord_3944273
  simp only [CollatzResearch.WordTrace]
  refine ⟨143859454839580024043229473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95906303226386682695486315 143859454839580024043229473)
  ·
    refine ⟨107894591129685018032422105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143859454839580024043229473 107894591129685018032422105)
    ·
      refine ⟨80920943347263763524316579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107894591129685018032422105 80920943347263763524316579)
      ·
        refine ⟨121381415020895645286474869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80920943347263763524316579 121381415020895645286474869)
        ·
          refine ⟨11379507658208966745607019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121381415020895645286474869 11379507658208966745607019)
          ·
            refine ⟨17069261487313450118410529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11379507658208966745607019 17069261487313450118410529)
            ·
              refine ⟨12801946115485087588807897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17069261487313450118410529 12801946115485087588807897)
              ·
                refine ⟨9601459586613815691605923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12801946115485087588807897 9601459586613815691605923)
                ·
                  refine ⟨14402189379920723537408885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9601459586613815691605923 14402189379920723537408885)
                  ·
                    refine ⟨1350205254367567831632083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14402189379920723537408885 1350205254367567831632083)
                    ·
                      rfl

theorem cell22_3944273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_3944273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944273 prefixEnd_3944273 := by exact prefixLift 3944273
  have htrace : WordTrace (prefixWord ++ tailWord_3944273) baseStart_3944273 baseEnd_3944273 := by
    simpa [prefixWord, tailWord_3944273, baseEnd_3944273] using wordTrace_append hprefix tailTrace_3944273
  have hstable : (prefixWord ++ tailWord_3944273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944273).length < 2 ^ (prefixWord ++ tailWord_3944273).sum := by decide
  have hdescent : baseEnd_3944273 < baseStart_3944273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944277 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 1, 4]
def baseStart_3944277 : Nat := 118140960795 + 3944277 * 2 ^ 59
def prefixEnd_3944277 : Nat := 4983230072969 + 3 ^ 40 * 3944277 * 2
def baseEnd_3944277 : Nat := 1350206623649313154532071

theorem tailTrace_3944277 : CollatzResearch.WordTrace tailWord_3944277 prefixEnd_3944277 1350206623649313154532071 := by
  unfold tailWord_3944277
  simp only [CollatzResearch.WordTrace]
  refine ⟨143859600731565532726375085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95906400487710355150916723 143859600731565532726375085)
  ·
    refine ⟨53947350274337074772390657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143859600731565532726375085 53947350274337074772390657)
    ·
      refine ⟨40460512705752806079292993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53947350274337074772390657 40460512705752806079292993)
      ·
        refine ⟨30345384529314604559469745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40460512705752806079292993 30345384529314604559469745)
        ·
          refine ⟨22759038396985953419602309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30345384529314604559469745 22759038396985953419602309)
          ·
            refine ⟨4267319699434866266175433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22759038396985953419602309 4267319699434866266175433)
            ·
              refine ⟨3200489774576149699631575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4267319699434866266175433 3200489774576149699631575)
              ·
                refine ⟨4800734661864224549447363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200489774576149699631575 4800734661864224549447363)
                ·
                  refine ⟨7201101992796336824171045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4800734661864224549447363 7201101992796336824171045)
                  ·
                    refine ⟨1350206623649313154532071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7201101992796336824171045 1350206623649313154532071)
                    ·
                      rfl

theorem cell22_3944277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_3944277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944277 prefixEnd_3944277 := by exact prefixLift 3944277
  have htrace : WordTrace (prefixWord ++ tailWord_3944277) baseStart_3944277 baseEnd_3944277 := by
    simpa [prefixWord, tailWord_3944277, baseEnd_3944277] using wordTrace_append hprefix tailTrace_3944277
  have hstable : (prefixWord ++ tailWord_3944277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944277).length < 2 ^ (prefixWord ++ tailWord_3944277).sum := by decide
  have hdescent : baseEnd_3944277 < baseStart_3944277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944408 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_3944408 : Nat := 118140960795 + 3944408 * 2 ^ 59
def prefixEnd_3944408 : Nat := 4983230072969 + 3 ^ 40 * 3944408 * 2
def baseEnd_3944408 : Nat := 1350251467626472479506669

theorem tailTrace_3944408 : CollatzResearch.WordTrace tailWord_3944408 prefixEnd_3944408 1350251467626472479506669 := by
  unfold tailWord_3944408
  simp only [CollatzResearch.WordTrace]
  refine ⟨71932189347045471049696939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95909585796060628066262585 71932189347045471049696939)
  ·
    refine ⟨107898284020568206574545409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71932189347045471049696939 107898284020568206574545409)
    ·
      refine ⟨80923713015426154930909057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107898284020568206574545409 80923713015426154930909057)
      ·
        refine ⟨60692784761569616198181793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80923713015426154930909057 60692784761569616198181793)
        ·
          refine ⟨45519588571177212148636345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60692784761569616198181793 45519588571177212148636345)
          ·
            refine ⟨34139691428382909111477259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45519588571177212148636345 34139691428382909111477259)
            ·
              refine ⟨51209537142574363667215889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34139691428382909111477259 51209537142574363667215889)
              ·
                refine ⟨38407152856930772750411917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51209537142574363667215889 38407152856930772750411917)
                ·
                  refine ⟨14402682321349039781404469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38407152856930772750411917 14402682321349039781404469)
                  ·
                    refine ⟨1350251467626472479506669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14402682321349039781404469 1350251467626472479506669)
                    ·
                      rfl

theorem cell22_3944408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_3944408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944408 prefixEnd_3944408 := by exact prefixLift 3944408
  have htrace : WordTrace (prefixWord ++ tailWord_3944408) baseStart_3944408 baseEnd_3944408 := by
    simpa [prefixWord, tailWord_3944408, baseEnd_3944408] using wordTrace_append hprefix tailTrace_3944408
  have hstable : (prefixWord ++ tailWord_3944408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944408).length < 2 ^ (prefixWord ++ tailWord_3944408).sum := by decide
  have hdescent : baseEnd_3944408 < baseStart_3944408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944440 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 2, 4]
def baseStart_3944440 : Nat := 118140960795 + 3944440 * 2 ^ 59
def prefixEnd_3944440 : Nat := 4983230072969 + 3 ^ 40 * 3944440 * 2
def baseEnd_3944440 : Nat := 1350262421880435062706571

theorem tailTrace_3944440 : CollatzResearch.WordTrace tailWord_3944440 prefixEnd_3944440 1350262421880435062706571 := by
  unfold tailWord_3944440
  simp only [CollatzResearch.WordTrace]
  refine ⟨71932772914987505782279387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95910363886650007709705849 71932772914987505782279387)
  ·
    refine ⟨107899159372481258673419081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71932772914987505782279387 107899159372481258673419081)
    ·
      refine ⟨80924369529360944005064311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107899159372481258673419081 80924369529360944005064311)
      ·
        refine ⟨121386554294041416007596467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80924369529360944005064311 121386554294041416007596467)
        ·
          refine ⟨182079831441062124011394701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121386554294041416007596467 182079831441062124011394701)
          ·
            refine ⟨68279936790398296504273013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182079831441062124011394701 68279936790398296504273013)
            ·
              refine ⟨6401244074099840297275595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68279936790398296504273013 6401244074099840297275595)
              ·
                refine ⟨9601866111149760445913393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6401244074099840297275595 9601866111149760445913393)
                ·
                  refine ⟨7201399583362320334435045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9601866111149760445913393 7201399583362320334435045)
                  ·
                    refine ⟨1350262421880435062706571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7201399583362320334435045 1350262421880435062706571)
                    ·
                      rfl

theorem cell22_3944440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_3944440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944440 prefixEnd_3944440 := by exact prefixLift 3944440
  have htrace : WordTrace (prefixWord ++ tailWord_3944440) baseStart_3944440 baseEnd_3944440 := by
    simpa [prefixWord, tailWord_3944440, baseEnd_3944440] using wordTrace_append hprefix tailTrace_3944440
  have hstable : (prefixWord ++ tailWord_3944440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944440).length < 2 ^ (prefixWord ++ tailWord_3944440).sum := by decide
  have hdescent : baseEnd_3944440 < baseStart_3944440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944446 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3944446 : Nat := 118140960795 + 3944446 * 2 ^ 59
def prefixEnd_3944446 : Nat := 4983230072969 + 3 ^ 40 * 3944446 * 2
def baseEnd_3944446 : Nat := 1350264475803053047056553

theorem tailTrace_3944446 : CollatzResearch.WordTrace tailWord_3944446 prefixEnd_3944446 1350264475803053047056553 := by
  unfold tailWord_3944446
  simp only [CollatzResearch.WordTrace]
  refine ⟨17983220583494159323659649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95910509778635516392851461 17983220583494159323659649)
  ·
    refine ⟨13487415437620619492744737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17983220583494159323659649 13487415437620619492744737)
    ·
      refine ⟨10115561578215464619558553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13487415437620619492744737 10115561578215464619558553)
      ·
        refine ⟨7586671183661598464668915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10115561578215464619558553 7586671183661598464668915)
        ·
          refine ⟨11380006775492397697003373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7586671183661598464668915 11380006775492397697003373)
          ·
            refine ⟨4267502540809649136376265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11380006775492397697003373 4267502540809649136376265)
            ·
              refine ⟨3200626905607236852282199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4267502540809649136376265 3200626905607236852282199)
              ·
                refine ⟨4800940358410855278423299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200626905607236852282199 4800940358410855278423299)
                ·
                  refine ⟨7201410537616282917634949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4800940358410855278423299 7201410537616282917634949)
                  ·
                    refine ⟨1350264475803053047056553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7201410537616282917634949 1350264475803053047056553)
                    ·
                      rfl

theorem cell22_3944446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3944446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944446 prefixEnd_3944446 := by exact prefixLift 3944446
  have htrace : WordTrace (prefixWord ++ tailWord_3944446) baseStart_3944446 baseEnd_3944446 := by
    simpa [prefixWord, tailWord_3944446, baseEnd_3944446] using wordTrace_append hprefix tailTrace_3944446
  have hstable : (prefixWord ++ tailWord_3944446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944446).length < 2 ^ (prefixWord ++ tailWord_3944446).sum := by decide
  have hdescent : baseEnd_3944446 < baseStart_3944446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944461 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3944461 : Nat := 118140960795 + 3944461 * 2 ^ 59
def prefixEnd_3944461 : Nat := 4983230072969 + 3 ^ 40 * 3944461 * 2
def baseEnd_3944461 : Nat := 450089870203199335977169

theorem tailTrace_3944461 : CollatzResearch.WordTrace tailWord_3944461 prefixEnd_3944461 450089870203199335977169 := by
  unfold tailWord_3944461
  simp only [CollatzResearch.WordTrace]
  refine ⟨143866311762898932151073237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95910874508599288100715491 143866311762898932151073237)
  ·
    refine ⟨3371866681942943722290779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 143866311762898932151073237 3371866681942943722290779)
    ·
      refine ⟨5057800022914415583436169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371866681942943722290779 5057800022914415583436169)
      ·
        refine ⟨3793350017185811687577127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5057800022914415583436169 3793350017185811687577127)
        ·
          refine ⟨5690025025778717531365691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793350017185811687577127 5690025025778717531365691)
          ·
            refine ⟨8535037538668076297048537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5690025025778717531365691 8535037538668076297048537)
            ·
              refine ⟨6401278154001057222786403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8535037538668076297048537 6401278154001057222786403)
              ·
                refine ⟨9601917231001585834179605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6401278154001057222786403 9601917231001585834179605)
                ·
                  refine ⟨450089870203199335977169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9601917231001585834179605 450089870203199335977169)
                  ·
                    rfl

theorem cell22_3944461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3944461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944461 prefixEnd_3944461 := by exact prefixLift 3944461
  have htrace : WordTrace (prefixWord ++ tailWord_3944461) baseStart_3944461 baseEnd_3944461 := by
    simpa [prefixWord, tailWord_3944461, baseEnd_3944461] using wordTrace_append hprefix tailTrace_3944461
  have hstable : (prefixWord ++ tailWord_3944461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944461).length < 2 ^ (prefixWord ++ tailWord_3944461).sum := by decide
  have hdescent : baseEnd_3944461 < baseStart_3944461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944547 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 1, 4]
def baseStart_3944547 : Nat := 118140960795 + 3944547 * 2 ^ 59
def prefixEnd_3944547 : Nat := 4983230072969 + 3 ^ 40 * 3944547 * 2
def baseEnd_3944547 : Nat := 1350299050167122450281243

theorem tailTrace_3944547 : CollatzResearch.WordTrace tailWord_3944547 prefixEnd_3944547 1350299050167122450281243 := by
  unfold tailWord_3944547
  simp only [CollatzResearch.WordTrace]
  refine ⟨143869448440587368838703895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95912965627058245892469263 143869448440587368838703895)
  ·
    refine ⟨215804172660881053258055843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143869448440587368838703895 215804172660881053258055843)
    ·
      refine ⟨323706258991321579887083765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215804172660881053258055843 323706258991321579887083765)
      ·
        refine ⟨30347461780436398114414103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323706258991321579887083765 30347461780436398114414103)
        ·
          refine ⟨45521192670654597171621155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30347461780436398114414103 45521192670654597171621155)
          ·
            refine ⟨68281789005981895757431733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45521192670654597171621155 68281789005981895757431733)
            ·
              refine ⟨6401417719310802727259225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68281789005981895757431733 6401417719310802727259225)
              ·
                refine ⟨4801063289483102045444419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6401417719310802727259225 4801063289483102045444419)
                ·
                  refine ⟨7201594934224653068166629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801063289483102045444419 7201594934224653068166629)
                  ·
                    refine ⟨1350299050167122450281243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7201594934224653068166629 1350299050167122450281243)
                    ·
                      rfl

theorem cell22_3944547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 4].length) (baseStart_3944547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944547 prefixEnd_3944547 := by exact prefixLift 3944547
  have htrace : WordTrace (prefixWord ++ tailWord_3944547) baseStart_3944547 baseEnd_3944547 := by
    simpa [prefixWord, tailWord_3944547, baseEnd_3944547] using wordTrace_append hprefix tailTrace_3944547
  have hstable : (prefixWord ++ tailWord_3944547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944547).length < 2 ^ (prefixWord ++ tailWord_3944547).sum := by decide
  have hdescent : baseEnd_3944547 < baseStart_3944547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944560 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_3944560 : Nat := 118140960795 + 3944560 * 2 ^ 59
def prefixEnd_3944560 : Nat := 4983230072969 + 3 ^ 40 * 3944560 * 2
def baseEnd_3944560 : Nat := 1350303500332794749706203

theorem tailTrace_3944560 : CollatzResearch.WordTrace tailWord_3944560 prefixEnd_3944560 1350303500332794749706203 := by
  unfold tailWord_3944560
  simp only [CollatzResearch.WordTrace]
  refine ⟨71934961294770136029463567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95913281726360181372618089 71934961294770136029463567)
  ·
    refine ⟨107902441942155204044195351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71934961294770136029463567 107902441942155204044195351)
    ·
      refine ⟨161853662913232806066293027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107902441942155204044195351 161853662913232806066293027)
      ·
        refine ⟨242780494369849209099439541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161853662913232806066293027 242780494369849209099439541)
        ·
          refine ⟨22760671347173363353072457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242780494369849209099439541 22760671347173363353072457)
          ·
            refine ⟨17070503510380022514804343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22760671347173363353072457 17070503510380022514804343)
            ·
              refine ⟨25605755265570033772206515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17070503510380022514804343 25605755265570033772206515)
              ·
                refine ⟨38408632898355050658309773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25605755265570033772206515 38408632898355050658309773)
                ·
                  refine ⟨14403237336883143996866165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38408632898355050658309773 14403237336883143996866165)
                  ·
                    refine ⟨1350303500332794749706203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14403237336883143996866165 1350303500332794749706203)
                    ·
                      rfl

theorem cell22_3944560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_3944560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944560 prefixEnd_3944560 := by exact prefixLift 3944560
  have htrace : WordTrace (prefixWord ++ tailWord_3944560) baseStart_3944560 baseEnd_3944560 := by
    simpa [prefixWord, tailWord_3944560, baseEnd_3944560] using wordTrace_append hprefix tailTrace_3944560
  have hstable : (prefixWord ++ tailWord_3944560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944560).length < 2 ^ (prefixWord ++ tailWord_3944560).sum := by decide
  have hdescent : baseEnd_3944560 < baseStart_3944560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944579 : List Nat := [1, 1, 1, 3, 3, 3, 4, 2, 4]
def baseStart_3944579 : Nat := 118140960795 + 3944579 * 2 ^ 59
def prefixEnd_3944579 : Nat := 4983230072969 + 3 ^ 40 * 3944579 * 2
def baseEnd_3944579 : Nat := 450103334807028344493715

theorem tailTrace_3944579 : CollatzResearch.WordTrace tailWord_3944579 prefixEnd_3944579 450103334807028344493715 := by
  unfold tailWord_3944579
  simp only [CollatzResearch.WordTrace]
  refine ⟨143870615576471438303868791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95913743717647625535912527 143870615576471438303868791)
  ·
    refine ⟨215805923364707157455803187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143870615576471438303868791 215805923364707157455803187)
    ·
      refine ⟨323708885047060736183704781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215805923364707157455803187 323708885047060736183704781)
      ·
        refine ⟨121390831892647776068889293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323708885047060736183704781 121390831892647776068889293)
        ·
          refine ⟨45521561959742916025833485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121390831892647776068889293 45521561959742916025833485)
          ·
            refine ⟨17070585734903593509687557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45521561959742916025833485 17070585734903593509687557)
            ·
              refine ⟨3200734825294423783066417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17070585734903593509687557 3200734825294423783066417)
              ·
                refine ⟨2400551118970817837299813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3200734825294423783066417 2400551118970817837299813)
                ·
                  refine ⟨450103334807028344493715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2400551118970817837299813 450103334807028344493715)
                  ·
                    rfl

theorem cell22_3944579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 4].length) (baseStart_3944579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944579 prefixEnd_3944579 := by exact prefixLift 3944579
  have htrace : WordTrace (prefixWord ++ tailWord_3944579) baseStart_3944579 baseEnd_3944579 := by
    simpa [prefixWord, tailWord_3944579, baseEnd_3944579] using wordTrace_append hprefix tailTrace_3944579
  have hstable : (prefixWord ++ tailWord_3944579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944579).length < 2 ^ (prefixWord ++ tailWord_3944579).sum := by decide
  have hdescent : baseEnd_3944579 < baseStart_3944579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944594 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3944594 : Nat := 118140960795 + 3944594 * 2 ^ 59
def prefixEnd_3944594 : Nat := 4983230072969 + 3 ^ 40 * 3944594 * 2
def baseEnd_3944594 : Nat := 1350315139227629994356099

theorem tailTrace_3944594 : CollatzResearch.WordTrace tailWord_3944594 prefixEnd_3944594 1350315139227629994356099 := by
  unfold tailWord_3944594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35967790667854273966416209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95914108447611397243776557 35967790667854273966416209)
  ·
    refine ⟨26975843000890705474812157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35967790667854273966416209 26975843000890705474812157)
    ·
      refine ⟨10115941125334014553054559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26975843000890705474812157 10115941125334014553054559)
      ·
        refine ⟨15173911688001021829581839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10115941125334014553054559 15173911688001021829581839)
        ·
          refine ⟨22760867532001532744372759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15173911688001021829581839 22760867532001532744372759)
          ·
            refine ⟨34141301298002299116559139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22760867532001532744372759 34141301298002299116559139)
            ·
              refine ⟨51211951947003448674838709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34141301298002299116559139 51211951947003448674838709)
              ·
                refine ⟨4801120495031573313266129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51211951947003448674838709 4801120495031573313266129)
                ·
                  refine ⟨3600840371273679984949597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4801120495031573313266129 3600840371273679984949597)
                  ·
                    refine ⟨1350315139227629994356099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3600840371273679984949597 1350315139227629994356099)
                    ·
                      rfl

theorem cell22_3944594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3944594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944594 prefixEnd_3944594 := by exact prefixLift 3944594
  have htrace : WordTrace (prefixWord ++ tailWord_3944594) baseStart_3944594 baseEnd_3944594 := by
    simpa [prefixWord, tailWord_3944594, baseEnd_3944594] using wordTrace_append hprefix tailTrace_3944594
  have hstable : (prefixWord ++ tailWord_3944594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944594).length < 2 ^ (prefixWord ++ tailWord_3944594).sum := by decide
  have hdescent : baseEnd_3944594 < baseStart_3944594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944609 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 2, 4]
def baseStart_3944609 : Nat := 118140960795 + 3944609 * 2 ^ 59
def prefixEnd_3944609 : Nat := 4983230072969 + 3 ^ 40 * 3944609 * 2
def baseEnd_3944609 : Nat := 1350320274034174955231053

theorem tailTrace_3944609 : CollatzResearch.WordTrace tailWord_3944609 prefixEnd_3944609 1350320274034174955231053 := by
  unfold tailWord_3944609
  simp only [CollatzResearch.WordTrace]
  refine ⟨143871709766362753427460881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95914473177575168951640587 143871709766362753427460881)
  ·
    refine ⟨107903782324772065070595661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143871709766362753427460881 107903782324772065070595661)
    ·
      refine ⟨40463918371789524401473373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107903782324772065070595661 40463918371789524401473373)
      ·
        refine ⟨15173969389421071650552515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40463918371789524401473373 15173969389421071650552515)
        ·
          refine ⟨22760954084131607475828773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15173969389421071650552515 22760954084131607475828773)
          ·
            refine ⟨4267678890774676401717895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22760954084131607475828773 4267678890774676401717895)
            ·
              refine ⟨6401518336162014602576843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267678890774676401717895 6401518336162014602576843)
              ·
                refine ⟨9602277504243021903865265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6401518336162014602576843 9602277504243021903865265)
                ·
                  refine ⟨7201708128182266427898949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9602277504243021903865265 7201708128182266427898949)
                  ·
                    refine ⟨1350320274034174955231053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7201708128182266427898949 1350320274034174955231053)
                    ·
                      rfl

theorem cell22_3944609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_3944609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944609 prefixEnd_3944609 := by exact prefixLift 3944609
  have htrace : WordTrace (prefixWord ++ tailWord_3944609) baseStart_3944609 baseEnd_3944609 := by
    simpa [prefixWord, tailWord_3944609, baseEnd_3944609] using wordTrace_append hprefix tailTrace_3944609
  have hstable : (prefixWord ++ tailWord_3944609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944609).length < 2 ^ (prefixWord ++ tailWord_3944609).sum := by decide
  have hdescent : baseEnd_3944609 < baseStart_3944609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944635 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 7]
def baseStart_3944635 : Nat := 118140960795 + 3944635 * 2 ^ 59
def prefixEnd_3944635 : Nat := 4983230072969 + 3 ^ 40 * 3944635 * 2
def baseEnd_3944635 : Nat := 450109724788506518026991

theorem tailTrace_3944635 : CollatzResearch.WordTrace tailWord_3944635 prefixEnd_3944635 450109724788506518026991 := by
  unfold tailWord_3944635
  simp only [CollatzResearch.WordTrace]
  refine ⟨143872658064268559867907359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95915105376179039911938239 143872658064268559867907359)
  ·
    refine ⟨215808987096402839801861039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143872658064268559867907359 215808987096402839801861039)
    ·
      refine ⟨323713480644604259702791559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215808987096402839801861039 323713480644604259702791559)
      ·
        refine ⟨485570220966906389554187339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323713480644604259702791559 485570220966906389554187339)
        ·
          refine ⟨728355331450359584331281009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485570220966906389554187339 728355331450359584331281009)
          ·
            refine ⟨546266498587769688248460757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 728355331450359584331281009 546266498587769688248460757)
            ·
              refine ⟨12803121060650852068323299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 546266498587769688248460757 12803121060650852068323299)
              ·
                refine ⟨19204681590976278102484949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12803121060650852068323299 19204681590976278102484949)
                ·
                  refine ⟨450109724788506518026991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19204681590976278102484949 450109724788506518026991)
                  ·
                    rfl

theorem cell22_3944635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 7].length) (baseStart_3944635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944635 prefixEnd_3944635 := by exact prefixLift 3944635
  have htrace : WordTrace (prefixWord ++ tailWord_3944635) baseStart_3944635 baseEnd_3944635 := by
    simpa [prefixWord, tailWord_3944635, baseEnd_3944635] using wordTrace_append hprefix tailTrace_3944635
  have hstable : (prefixWord ++ tailWord_3944635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944635).length < 2 ^ (prefixWord ++ tailWord_3944635).sum := by decide
  have hdescent : baseEnd_3944635 < baseStart_3944635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944695 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 2, 9]
def baseStart_3944695 : Nat := 118140960795 + 3944695 * 2 ^ 59
def prefixEnd_3944695 : Nat := 4983230072969 + 3 ^ 40 * 3944695 * 2
def baseEnd_3944695 : Nat := 1350349713591699397580789

theorem tailTrace_3944695 : CollatzResearch.WordTrace tailWord_3944695 prefixEnd_3944695 1350349713591699397580789 := by
  unfold tailWord_3944695
  simp only [CollatzResearch.WordTrace]
  refine ⟨143874846444051190115091539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95916564296034126743394359 143874846444051190115091539)
  ·
    refine ⟨215812269666076785172637309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143874846444051190115091539 215812269666076785172637309)
    ·
      refine ⟨80929601124778794439738991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215812269666076785172637309 80929601124778794439738991)
      ·
        refine ⟨121394401687168191659608487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80929601124778794439738991 121394401687168191659608487)
        ·
          refine ⟨182091602530752287489412731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121394401687168191659608487 182091602530752287489412731)
          ·
            refine ⟨273137403796128431234119097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182091602530752287489412731 273137403796128431234119097)
            ·
              refine ⟨204853052847096323425589323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273137403796128431234119097 204853052847096323425589323)
              ·
                refine ⟨307279579270644485138383985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204853052847096323425589323 307279579270644485138383985)
                ·
                  refine ⟨230459684452983363853787989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307279579270644485138383985 230459684452983363853787989)
                  ·
                    refine ⟨1350349713591699397580789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 230459684452983363853787989 1350349713591699397580789)
                    ·
                      rfl

theorem cell22_3944695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_3944695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944695 prefixEnd_3944695 := by exact prefixLift 3944695
  have htrace : WordTrace (prefixWord ++ tailWord_3944695) baseStart_3944695 baseEnd_3944695 := by
    simpa [prefixWord, tailWord_3944695, baseEnd_3944695] using wordTrace_append hprefix tailTrace_3944695
  have hstable : (prefixWord ++ tailWord_3944695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944695).length < 2 ^ (prefixWord ++ tailWord_3944695).sum := by decide
  have hdescent : baseEnd_3944695 < baseStart_3944695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944733 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3944733 : Nat := 118140960795 + 3944733 * 2 ^ 59
def prefixEnd_3944733 : Nat := 4983230072969 + 3 ^ 40 * 3944733 * 2
def baseEnd_3944733 : Nat := 1350362721768279965130673

theorem tailTrace_3944733 : CollatzResearch.WordTrace tailWord_3944733 prefixEnd_3944733 1350362721768279965130673 := by
  unfold tailWord_3944733
  simp only [CollatzResearch.WordTrace]
  refine ⟨143876232417913522604974853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95917488278609015069983235 143876232417913522604974853)
  ·
    refine ⟨26976793578358785488432785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143876232417913522604974853 26976793578358785488432785)
    ·
      refine ⟨20232595183769089116324589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26976793578358785488432785 20232595183769089116324589)
      ·
        refine ⟨7587223193913408418621721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20232595183769089116324589 7587223193913408418621721)
        ·
          refine ⟨5690417395435056313966291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7587223193913408418621721 5690417395435056313966291)
          ·
            refine ⟨8535626093152584470949437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5690417395435056313966291 8535626093152584470949437)
            ·
              refine ⟨3200859784932219176606039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8535626093152584470949437 3200859784932219176606039)
              ·
                refine ⟨4801289677398328764909059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200859784932219176606039 4801289677398328764909059)
                ·
                  refine ⟨7201934516097493147363589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801289677398328764909059 7201934516097493147363589)
                  ·
                    refine ⟨1350362721768279965130673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7201934516097493147363589 1350362721768279965130673)
                    ·
                      rfl

theorem cell22_3944733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3944733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944733 prefixEnd_3944733 := by exact prefixLift 3944733
  have htrace : WordTrace (prefixWord ++ tailWord_3944733) baseStart_3944733 baseEnd_3944733 := by
    simpa [prefixWord, tailWord_3944733, baseEnd_3944733] using wordTrace_append hprefix tailTrace_3944733
  have hstable : (prefixWord ++ tailWord_3944733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944733).length < 2 ^ (prefixWord ++ tailWord_3944733).sum := by decide
  have hdescent : baseEnd_3944733 < baseStart_3944733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944808 : List Nat := [2, 1, 4, 2, 2, 1, 2, 4, 1, 3]
def baseStart_3944808 : Nat := 118140960795 + 3944808 * 2 ^ 59
def prefixEnd_3944808 : Nat := 4983230072969 + 3 ^ 40 * 3944808 * 2
def baseEnd_3944808 : Nat := 1350388395801004769505443

theorem tailTrace_3944808 : CollatzResearch.WordTrace tailWord_3944808 prefixEnd_3944808 1350388395801004769505443 := by
  unfold tailWord_3944808
  simp only [CollatzResearch.WordTrace]
  refine ⟨71939483946320905206977539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95919311928427873609303385 71939483946320905206977539)
  ·
    refine ⟨107909225919481357810466309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71939483946320905206977539 107909225919481357810466309)
    ·
      refine ⟨20232979859902754589462433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107909225919481357810466309 20232979859902754589462433)
      ·
        refine ⟨15174734894927065942096825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20232979859902754589462433 15174734894927065942096825)
        ·
          refine ⟨11381051171195299456572619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15174734894927065942096825 11381051171195299456572619)
          ·
            refine ⟨17071576756792949184858929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11381051171195299456572619 17071576756792949184858929)
            ·
              refine ⟨12803682567594711888644197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17071576756792949184858929 12803682567594711888644197)
              ·
                refine ⟨2400690481424008479120787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12803682567594711888644197 2400690481424008479120787)
                ·
                  refine ⟨3601035722136012718681181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400690481424008479120787 3601035722136012718681181)
                  ·
                    refine ⟨1350388395801004769505443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3601035722136012718681181 1350388395801004769505443)
                    ·
                      rfl

theorem cell22_3944808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_3944808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944808 prefixEnd_3944808 := by exact prefixLift 3944808
  have htrace : WordTrace (prefixWord ++ tailWord_3944808) baseStart_3944808 baseEnd_3944808 := by
    simpa [prefixWord, tailWord_3944808, baseEnd_3944808] using wordTrace_append hprefix tailTrace_3944808
  have hstable : (prefixWord ++ tailWord_3944808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944808).length < 2 ^ (prefixWord ++ tailWord_3944808).sum := by decide
  have hdescent : baseEnd_3944808 < baseStart_3944808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944842 : List Nat := [3, 1, 2, 5, 1, 2, 1, 3, 1, 3]
def baseStart_3944842 : Nat := 118140960795 + 3944842 * 2 ^ 59
def prefixEnd_3944842 : Nat := 4983230072969 + 3 ^ 40 * 3944842 * 2
def baseEnd_3944842 : Nat := 1350400034695840014155339

theorem tailTrace_3944842 : CollatzResearch.WordTrace tailWord_3944842 prefixEnd_3944842 1350400034695840014155339 := by
  unfold tailWord_3944842
  simp only [CollatzResearch.WordTrace]
  refine ⟨35970051993629658555173195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95920138649679089480461853 35970051993629658555173195)
  ·
    refine ⟨53955077990444487832759793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35970051993629658555173195 53955077990444487832759793)
    ·
      refine ⟨40466308492833365874569845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53955077990444487832759793 40466308492833365874569845)
      ·
        refine ⟨3793716421203128050740923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40466308492833365874569845 3793716421203128050740923)
        ·
          refine ⟨5690574631804692076111385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793716421203128050740923 5690574631804692076111385)
          ·
            refine ⟨4267930973853519057083539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5690574631804692076111385 4267930973853519057083539)
            ·
              refine ⟨6401896460780278585625309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267930973853519057083539 6401896460780278585625309)
              ·
                refine ⟨2400711172792604469609491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6401896460780278585625309 2400711172792604469609491)
                ·
                  refine ⟨3601066759188906704414237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400711172792604469609491 3601066759188906704414237)
                  ·
                    refine ⟨1350400034695840014155339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3601066759188906704414237 1350400034695840014155339)
                    ·
                      rfl

theorem cell22_3944842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_3944842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944842 prefixEnd_3944842 := by exact prefixLift 3944842
  have htrace : WordTrace (prefixWord ++ tailWord_3944842) baseStart_3944842 baseEnd_3944842 := by
    simpa [prefixWord, tailWord_3944842, baseEnd_3944842] using wordTrace_append hprefix tailTrace_3944842
  have hstable : (prefixWord ++ tailWord_3944842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944842).length < 2 ^ (prefixWord ++ tailWord_3944842).sum := by decide
  have hdescent : baseEnd_3944842 < baseStart_3944842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944885 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 1, 4]
def baseStart_3944885 : Nat := 118140960795 + 3944885 * 2 ^ 59
def prefixEnd_3944885 : Nat := 4983230072969 + 3 ^ 40 * 3944885 * 2
def baseEnd_3944885 : Nat := 1350414754474602235330207

theorem tailTrace_3944885 : CollatzResearch.WordTrace tailWord_3944885 prefixEnd_3944885 1350414754474602235330207 := by
  unfold tailWord_3944885
  simp only [CollatzResearch.WordTrace]
  refine ⟨143881776313362852564508109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95921184208908568376338739 143881776313362852564508109)
  ·
    refine ⟨53955666117511069711690541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143881776313362852564508109 53955666117511069711690541)
    ·
      refine ⟨20233374794066651141883953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53955666117511069711690541 20233374794066651141883953)
      ·
        refine ⟨15175031095549988356412965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20233374794066651141883953 15175031095549988356412965)
        ·
          refine ⟨2845318330415622816827431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15175031095549988356412965 2845318330415622816827431)
          ·
            refine ⟨4267977495623434225241147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845318330415622816827431 4267977495623434225241147)
            ·
              refine ⟨6401966243435151337861721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267977495623434225241147 6401966243435151337861721)
              ·
                refine ⟨4801474682576363503396291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6401966243435151337861721 4801474682576363503396291)
                ·
                  refine ⟨7202212023864545255094437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801474682576363503396291 7202212023864545255094437)
                  ·
                    refine ⟨1350414754474602235330207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7202212023864545255094437 1350414754474602235330207)
                    ·
                      rfl

theorem cell22_3944885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_3944885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944885 prefixEnd_3944885 := by exact prefixLift 3944885
  have htrace : WordTrace (prefixWord ++ tailWord_3944885) baseStart_3944885 baseEnd_3944885 := by
    simpa [prefixWord, tailWord_3944885, baseEnd_3944885] using wordTrace_append hprefix tailTrace_3944885
  have hstable : (prefixWord ++ tailWord_3944885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944885).length < 2 ^ (prefixWord ++ tailWord_3944885).sum := by decide
  have hdescent : baseEnd_3944885 < baseStart_3944885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944894 : List Nat := [4, 2, 1, 1, 1, 1, 4, 8]
def baseStart_3944894 : Nat := 118140960795 + 3944894 * 2 ^ 59
def prefixEnd_3944894 : Nat := 4983230072969 + 3 ^ 40 * 3944894 * 2
def baseEnd_3944894 : Nat := 150046426150947690206131

theorem tailTrace_3944894 : CollatzResearch.WordTrace tailWord_3944894 prefixEnd_3944894 150046426150947690206131 := by
  unfold tailWord_3944894
  simp only [CollatzResearch.WordTrace]
  refine ⟨17985263071291280887698217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95921403046886831401057157 17985263071291280887698217)
  ·
    refine ⟨13488947303468460665773663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17985263071291280887698217 13488947303468460665773663)
    ·
      refine ⟨20233420955202690998660495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13488947303468460665773663 20233420955202690998660495)
      ·
        refine ⟨30350131432804036497990743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20233420955202690998660495 30350131432804036497990743)
        ·
          refine ⟨45525197149206054746986115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30350131432804036497990743 45525197149206054746986115)
          ·
            refine ⟨68287795723809082120479173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45525197149206054746986115 68287795723809082120479173)
            ·
              refine ⟨12803961698214202897589845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68287795723809082120479173 12803961698214202897589845)
              ·
                refine ⟨150046426150947690206131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12803961698214202897589845 150046426150947690206131)
                ·
                  rfl

theorem cell22_3944894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_3944894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944894 prefixEnd_3944894 := by exact prefixLift 3944894
  have htrace : WordTrace (prefixWord ++ tailWord_3944894) baseStart_3944894 baseEnd_3944894 := by
    simpa [prefixWord, tailWord_3944894, baseEnd_3944894] using wordTrace_append hprefix tailTrace_3944894
  have hstable : (prefixWord ++ tailWord_3944894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944894).length < 2 ^ (prefixWord ++ tailWord_3944894).sum := by decide
  have hdescent : baseEnd_3944894 < baseStart_3944894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944939 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 5]
def baseStart_3944939 : Nat := 118140960795 + 3944939 * 2 ^ 59
def prefixEnd_3944939 : Nat := 4983230072969 + 3 ^ 40 * 3944939 * 2
def baseEnd_3944939 : Nat := 450144413259388031493347

theorem tailTrace_3944939 : CollatzResearch.WordTrace tailWord_3944939 prefixEnd_3944939 450144413259388031493347 := by
  unfold tailWord_3944939
  simp only [CollatzResearch.WordTrace]
  refine ⟨143883745855167219786973871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95922497236778146524649247 143883745855167219786973871)
  ·
    refine ⟨215825618782750829680460807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143883745855167219786973871 215825618782750829680460807)
    ·
      refine ⟨323738428174126244520691211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215825618782750829680460807 323738428174126244520691211)
      ·
        refine ⟨485607642261189366781036817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323738428174126244520691211 485607642261189366781036817)
        ·
          refine ⟨364205731695892025085777613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485607642261189366781036817 364205731695892025085777613)
          ·
            refine ⟨136577149385959509407166605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364205731695892025085777613 136577149385959509407166605)
            ·
              refine ⟨51216431019734816027687477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136577149385959509407166605 51216431019734816027687477)
              ·
                refine ⟨4801540408100139002595701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51216431019734816027687477 4801540408100139002595701)
                ·
                  refine ⟨450144413259388031493347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4801540408100139002595701 450144413259388031493347)
                  ·
                    rfl

theorem cell22_3944939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 5].length) (baseStart_3944939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944939 prefixEnd_3944939 := by exact prefixLift 3944939
  have htrace : WordTrace (prefixWord ++ tailWord_3944939) baseStart_3944939 baseEnd_3944939 := by
    simpa [prefixWord, tailWord_3944939, baseEnd_3944939] using wordTrace_append hprefix tailTrace_3944939
  have hstable : (prefixWord ++ tailWord_3944939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944939).length < 2 ^ (prefixWord ++ tailWord_3944939).sum := by decide
  have hdescent : baseEnd_3944939 < baseStart_3944939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944969 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_3944969 : Nat := 118140960795 + 3944969 * 2 ^ 59
def prefixEnd_3944969 : Nat := 4983230072969 + 3 ^ 40 * 3944969 * 2
def baseEnd_3944969 : Nat := 1350443509391254016229949

theorem tailTrace_3944969 : CollatzResearch.WordTrace tailWord_3944969 prefixEnd_3944969 1350443509391254016229949 := by
  unfold tailWord_3944969
  simp only [CollatzResearch.WordTrace]
  refine ⟨143884840045058534910565961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95923226696705689940377307 143884840045058534910565961)
  ·
    refine ⟨107913630033793901182924471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143884840045058534910565961 107913630033793901182924471)
    ·
      refine ⟨161870445050690851774386707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107913630033793901182924471 161870445050690851774386707)
      ·
        refine ⟨242805667576036277661580061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161870445050690851774386707 242805667576036277661580061)
        ·
          refine ⟨91052125341013604123092523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242805667576036277661580061 91052125341013604123092523)
          ·
            refine ⟨136578188011520406184638785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91052125341013604123092523 136578188011520406184638785)
            ·
              refine ⟨102433641008640304638479089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136578188011520406184638785 102433641008640304638479089)
              ·
                refine ⟨76825230756480228478859317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102433641008640304638479089 76825230756480228478859317)
                ·
                  refine ⟨7202365383420021419893061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76825230756480228478859317 7202365383420021419893061)
                  ·
                    refine ⟨1350443509391254016229949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7202365383420021419893061 1350443509391254016229949)
                    ·
                      rfl

theorem cell22_3944969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_3944969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3944969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3944969 prefixEnd_3944969 := by exact prefixLift 3944969
  have htrace : WordTrace (prefixWord ++ tailWord_3944969) baseStart_3944969 baseEnd_3944969 := by
    simpa [prefixWord, tailWord_3944969, baseEnd_3944969] using wordTrace_append hprefix tailTrace_3944969
  have hstable : (prefixWord ++ tailWord_3944969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944969).length < 2 ^ (prefixWord ++ tailWord_3944969).sum := by decide
  have hdescent : baseEnd_3944969 < baseStart_3944969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945016 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 6, 3]
def baseStart_3945016 : Nat := 118140960795 + 3945016 * 2 ^ 59
def prefixEnd_3945016 : Nat := 4983230072969 + 3 ^ 40 * 3945016 * 2
def baseEnd_3945016 : Nat := 1350459598451761560304805

theorem tailTrace_3945016 : CollatzResearch.WordTrace tailWord_3945016 prefixEnd_3945016 1350459598451761560304805 := by
  unfold tailWord_3945016
  simp only [CollatzResearch.WordTrace]
  refine ⟨71943277137944130968763451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95924369517258841291684601 71943277137944130968763451)
  ·
    refine ⟨107914915706916196453145177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71943277137944130968763451 107914915706916196453145177)
    ·
      refine ⟨80936186780187147339858883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107914915706916196453145177 80936186780187147339858883)
      ·
        refine ⟨121404280170280721009788325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80936186780187147339858883 121404280170280721009788325)
        ·
          refine ⟨22763302531927635189335311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121404280170280721009788325 22763302531927635189335311)
          ·
            refine ⟨34144953797891452784002967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22763302531927635189335311 34144953797891452784002967)
            ·
              refine ⟨51217430696837179176004451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34144953797891452784002967 51217430696837179176004451)
              ·
                refine ⟨76826146045255768764006677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51217430696837179176004451 76826146045255768764006677)
                ·
                  refine ⟨3601225595871364160812813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76826146045255768764006677 3601225595871364160812813)
                  ·
                    refine ⟨1350459598451761560304805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3601225595871364160812813 1350459598451761560304805)
                    ·
                      rfl

theorem cell22_3945016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_3945016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945016 prefixEnd_3945016 := by exact prefixLift 3945016
  have htrace : WordTrace (prefixWord ++ tailWord_3945016) baseStart_3945016 baseEnd_3945016 := by
    simpa [prefixWord, tailWord_3945016, baseEnd_3945016] using wordTrace_append hprefix tailTrace_3945016
  have hstable : (prefixWord ++ tailWord_3945016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945016).length < 2 ^ (prefixWord ++ tailWord_3945016).sum := by decide
  have hdescent : baseEnd_3945016 < baseStart_3945016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945018 : List Nat := [3, 1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_3945018 : Nat := 118140960795 + 3945018 * 2 ^ 59
def prefixEnd_3945018 : Nat := 4983230072969 + 3 ^ 40 * 3945018 * 2
def baseEnd_3945018 : Nat := 450153427697544740584933

theorem tailTrace_3945018 : CollatzResearch.WordTrace tailWord_3945018 prefixEnd_3945018 450153427697544740584933 := by
  unfold tailWord_3945018
  simp only [CollatzResearch.WordTrace]
  refine ⟨35971656805470254069774927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95924418147920677519399805 35971656805470254069774927)
  ·
    refine ⟨53957485208205381104662391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35971656805470254069774927 53957485208205381104662391)
    ·
      refine ⟨80936227812308071656993587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53957485208205381104662391 80936227812308071656993587)
      ·
        refine ⟨121404341718462107485490381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80936227812308071656993587 121404341718462107485490381)
        ·
          refine ⟨45526628144423290307058893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121404341718462107485490381 45526628144423290307058893)
          ·
            refine ⟨17072485554158733865147085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45526628144423290307058893 17072485554158733865147085)
            ·
              refine ⟨6402182082809525199430157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17072485554158733865147085 6402182082809525199430157)
              ·
                refine ⟨2400818281053571949786309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6402182082809525199430157 2400818281053571949786309)
                ·
                  refine ⟨450153427697544740584933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2400818281053571949786309 450153427697544740584933)
                  ·
                    rfl

theorem cell22_3945018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_3945018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945018 prefixEnd_3945018 := by exact prefixLift 3945018
  have htrace : WordTrace (prefixWord ++ tailWord_3945018) baseStart_3945018 baseEnd_3945018 := by
    simpa [prefixWord, tailWord_3945018, baseEnd_3945018] using wordTrace_append hprefix tailTrace_3945018
  have hstable : (prefixWord ++ tailWord_3945018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945018).length < 2 ^ (prefixWord ++ tailWord_3945018).sum := by decide
  have hdescent : baseEnd_3945018 < baseStart_3945018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945029 : List Nat := [1, 3, 1, 1, 1, 5, 10]
def baseStart_3945029 : Nat := 118140960795 + 3945029 * 2 ^ 59
def prefixEnd_3945029 : Nat := 4983230072969 + 3 ^ 40 * 3945029 * 2
def baseEnd_3945029 : Nat := 50017186985830883693695

theorem tailTrace_3945029 : CollatzResearch.WordTrace tailWord_3945029 prefixEnd_3945029 50017186985830883693695 := by
  unfold tailWord_3945029
  simp only [CollatzResearch.WordTrace]
  refine ⟨143887028424841165157750141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95924685616560776771833427 143887028424841165157750141)
  ·
    refine ⟨53957635659315436934156303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143887028424841165157750141 53957635659315436934156303)
    ·
      refine ⟨80936453488973155401234455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53957635659315436934156303 80936453488973155401234455)
      ·
        refine ⟨121404680233459733101851683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80936453488973155401234455 121404680233459733101851683)
        ·
          refine ⟨182107020350189599652777525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121404680233459733101851683 182107020350189599652777525)
          ·
            refine ⟨17072533157830274967447893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182107020350189599652777525 17072533157830274967447893)
            ·
              refine ⟨50017186985830883693695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17072533157830274967447893 50017186985830883693695)
              ·
                rfl

theorem cell22_3945029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 10].length) (baseStart_3945029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945029 prefixEnd_3945029 := by exact prefixLift 3945029
  have htrace : WordTrace (prefixWord ++ tailWord_3945029) baseStart_3945029 baseEnd_3945029 := by
    simpa [prefixWord, tailWord_3945029, baseEnd_3945029] using wordTrace_append hprefix tailTrace_3945029
  have hstable : (prefixWord ++ tailWord_3945029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945029).length < 2 ^ (prefixWord ++ tailWord_3945029).sum := by decide
  have hdescent : baseEnd_3945029 < baseStart_3945029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945031 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 4, 4]
def baseStart_3945031 : Nat := 118140960795 + 3945031 * 2 ^ 59
def prefixEnd_3945031 : Nat := 4983230072969 + 3 ^ 40 * 3945031 * 2
def baseEnd_3945031 : Nat := 1350464733258306521179759

theorem tailTrace_3945031 : CollatzResearch.WordTrace tailWord_3945031 prefixEnd_3945031 1350464733258306521179759 := by
  unfold tailWord_3945031
  simp only [CollatzResearch.WordTrace]
  refine ⟨143887101370833919499322947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95924734247222612999548631 143887101370833919499322947)
  ·
    refine ⟨215830652056250879248984421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143887101370833919499322947 215830652056250879248984421)
    ·
      refine ⟨40468247260547039859184579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215830652056250879248984421 40468247260547039859184579)
      ·
        refine ⟨60702370890820559788776869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40468247260547039859184579 60702370890820559788776869)
        ·
          refine ⟨11381694542028854960395663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60702370890820559788776869 11381694542028854960395663)
          ·
            refine ⟨17072541813043282440593495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11381694542028854960395663 17072541813043282440593495)
            ·
              refine ⟨25608812719564923660890243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17072541813043282440593495 25608812719564923660890243)
              ·
                refine ⟨38413219079347385491335365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25608812719564923660890243 38413219079347385491335365)
                ·
                  refine ⟨7202478577377634779625381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38413219079347385491335365 7202478577377634779625381)
                  ·
                    refine ⟨1350464733258306521179759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7202478577377634779625381 1350464733258306521179759)
                    ·
                      rfl

theorem cell22_3945031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_3945031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945031 prefixEnd_3945031 := by exact prefixLift 3945031
  have htrace : WordTrace (prefixWord ++ tailWord_3945031) baseStart_3945031 baseEnd_3945031 := by
    simpa [prefixWord, tailWord_3945031, baseEnd_3945031] using wordTrace_append hprefix tailTrace_3945031
  have hstable : (prefixWord ++ tailWord_3945031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945031).length < 2 ^ (prefixWord ++ tailWord_3945031).sum := by decide
  have hdescent : baseEnd_3945031 < baseStart_3945031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945091 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 5]
def baseStart_3945091 : Nat := 118140960795 + 3945091 * 2 ^ 59
def prefixEnd_3945091 : Nat := 4983230072969 + 3 ^ 40 * 3945091 * 2
def baseEnd_3945091 : Nat := 450161757494828788226525

theorem tailTrace_3945091 : CollatzResearch.WordTrace tailWord_3945091 prefixEnd_3945091 450161757494828788226525 := by
  unfold tailWord_3945091
  simp only [CollatzResearch.WordTrace]
  refine ⟨143889289750616549746507127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95926193167077699831004751 143889289750616549746507127)
  ·
    refine ⟨215833934625924824619760691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143889289750616549746507127 215833934625924824619760691)
    ·
      refine ⟨323750901938887236929641037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215833934625924824619760691 323750901938887236929641037)
      ·
        refine ⟨121406588227082713848615389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323750901938887236929641037 121406588227082713848615389)
        ·
          refine ⟨45527470585156017693230771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121406588227082713848615389 45527470585156017693230771)
          ·
            refine ⟨68291205877734026539846157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45527470585156017693230771 68291205877734026539846157)
            ·
              refine ⟨25609202204150259952442309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68291205877734026539846157 25609202204150259952442309)
              ·
                refine ⟨4801725413278173741082933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25609202204150259952442309 4801725413278173741082933)
                ·
                  refine ⟨450161757494828788226525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4801725413278173741082933 450161757494828788226525)
                  ·
                    rfl

theorem cell22_3945091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 5].length) (baseStart_3945091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945091 prefixEnd_3945091 := by exact prefixLift 3945091
  have htrace : WordTrace (prefixWord ++ tailWord_3945091) baseStart_3945091 baseEnd_3945091 := by
    simpa [prefixWord, tailWord_3945091, baseEnd_3945091] using wordTrace_append hprefix tailTrace_3945091
  have hstable : (prefixWord ++ tailWord_3945091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945091).length < 2 ^ (prefixWord ++ tailWord_3945091).sum := by decide
  have hdescent : baseEnd_3945091 < baseStart_3945091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945095 : List Nat := [1, 1, 4, 2, 1, 2, 3, 4, 1, 3]
def baseStart_3945095 : Nat := 118140960795 + 3945095 * 2 ^ 59
def prefixEnd_3945095 : Nat := 4983230072969 + 3 ^ 40 * 3945095 * 2
def baseEnd_3945095 : Nat := 1350486641766231687579563

theorem tailTrace_3945095 : CollatzResearch.WordTrace tailWord_3945095 prefixEnd_3945095 1350486641766231687579563 := by
  unfold tailWord_3945095
  simp only [CollatzResearch.WordTrace]
  refine ⟨143889435642602058429652739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95926290428401372286435159 143889435642602058429652739)
  ·
    refine ⟨215834153463903087644479109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143889435642602058429652739 215834153463903087644479109)
    ·
      refine ⟨40468903774481828933339833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215834153463903087644479109 40468903774481828933339833)
      ·
        refine ⟨30351677830861371700004875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40468903774481828933339833 30351677830861371700004875)
        ·
          refine ⟨45527516746292057550007313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30351677830861371700004875 45527516746292057550007313)
          ·
            refine ⟨34145637559719043162505485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45527516746292057550007313 34145637559719043162505485)
            ·
              refine ⟨12804614084894641185939557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34145637559719043162505485 12804614084894641185939557)
              ·
                refine ⟨2400865140917745222363667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12804614084894641185939557 2400865140917745222363667)
                ·
                  refine ⟨3601297711376617833545501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400865140917745222363667 3601297711376617833545501)
                  ·
                    refine ⟨1350486641766231687579563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3601297711376617833545501 1350486641766231687579563)
                    ·
                      rfl

theorem cell22_3945095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_3945095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945095 prefixEnd_3945095 := by exact prefixLift 3945095
  have htrace : WordTrace (prefixWord ++ tailWord_3945095) baseStart_3945095 baseEnd_3945095 := by
    simpa [prefixWord, tailWord_3945095, baseEnd_3945095] using wordTrace_append hprefix tailTrace_3945095
  have hstable : (prefixWord ++ tailWord_3945095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945095).length < 2 ^ (prefixWord ++ tailWord_3945095).sum := by decide
  have hdescent : baseEnd_3945095 < baseStart_3945095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945172 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_3945172 : Nat := 118140960795 + 3945172 * 2 ^ 59
def prefixEnd_3945172 : Nat := 4983230072969 + 3 ^ 40 * 3945172 * 2
def baseEnd_3945172 : Nat := 1350513000439829153404327

theorem tailTrace_3945172 : CollatzResearch.WordTrace tailWord_3945172 prefixEnd_3945172 1350513000439829153404327 := by
  unfold tailWord_3945172
  simp only [CollatzResearch.WordTrace]
  refine ⟨71946122031661550290102885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95928162708882067053470513 71946122031661550290102885)
  ·
    refine ⟨13489897880936540679394291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71946122031661550290102885 13489897880936540679394291)
    ·
      refine ⟨20234846821404811019091437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13489897880936540679394291 20234846821404811019091437)
      ·
        refine ⟨7588067558026804132159289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20234846821404811019091437 7588067558026804132159289)
        ·
          refine ⟨5691050668520103099119467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7588067558026804132159289 5691050668520103099119467)
          ·
            refine ⟨8536576002780154648679201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5691050668520103099119467 8536576002780154648679201)
            ·
              refine ⟨6402432002085115986509401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8536576002780154648679201 6402432002085115986509401)
              ·
                refine ⟨4801824001563836989882051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6402432002085115986509401 4801824001563836989882051)
                ·
                  refine ⟨7202736002345755484823077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801824001563836989882051 7202736002345755484823077)
                  ·
                    refine ⟨1350513000439829153404327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7202736002345755484823077 1350513000439829153404327)
                    ·
                      rfl

theorem cell22_3945172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_3945172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945172 prefixEnd_3945172 := by exact prefixLift 3945172
  have htrace : WordTrace (prefixWord ++ tailWord_3945172) baseStart_3945172 baseEnd_3945172 := by
    simpa [prefixWord, tailWord_3945172, baseEnd_3945172] using wordTrace_append hprefix tailTrace_3945172
  have hstable : (prefixWord ++ tailWord_3945172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945172).length < 2 ^ (prefixWord ++ tailWord_3945172).sum := by decide
  have hdescent : baseEnd_3945172 < baseStart_3945172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945187 : List Nat := [1, 1, 1, 7, 1, 3, 1, 3, 4]
def baseStart_3945187 : Nat := 118140960795 + 3945187 * 2 ^ 59
def prefixEnd_3945187 : Nat := 4983230072969 + 3 ^ 40 * 3945187 * 2
def baseEnd_3945187 : Nat := 450172711748791371426427

theorem tailTrace_3945187 : CollatzResearch.WordTrace tailWord_3945187 prefixEnd_3945187 450172711748791371426427 := by
  unfold tailWord_3945187
  simp only [CollatzResearch.WordTrace]
  refine ⟨143892791158268758142001815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95928527438845838761334543 143892791158268758142001815)
  ·
    refine ⟨215839186737403137213002723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143892791158268758142001815 215839186737403137213002723)
    ·
      refine ⟨323758780106104705819504085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215839186737403137213002723 323758780106104705819504085)
      ·
        refine ⟨7588096408736829042644627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 323758780106104705819504085 7588096408736829042644627)
        ·
          refine ⟨11382144613105243563966941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588096408736829042644627 11382144613105243563966941)
          ·
            refine ⟨4268304229914466336487603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11382144613105243563966941 4268304229914466336487603)
            ·
              refine ⟨6402456344871699504731405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268304229914466336487603 6402456344871699504731405)
              ·
                refine ⟨2400921129326887314274277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6402456344871699504731405 2400921129326887314274277)
                ·
                  refine ⟨450172711748791371426427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2400921129326887314274277 450172711748791371426427)
                  ·
                    rfl

theorem cell22_3945187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 4].length) (baseStart_3945187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945187 prefixEnd_3945187 := by exact prefixLift 3945187
  have htrace : WordTrace (prefixWord ++ tailWord_3945187) baseStart_3945187 baseEnd_3945187 := by
    simpa [prefixWord, tailWord_3945187, baseEnd_3945187] using wordTrace_append hprefix tailTrace_3945187
  have hstable : (prefixWord ++ tailWord_3945187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945187).length < 2 ^ (prefixWord ++ tailWord_3945187).sum := by decide
  have hdescent : baseEnd_3945187 < baseStart_3945187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945198 : List Nat := [4, 1, 2, 1, 1, 5, 8]
def baseStart_3945198 : Nat := 118140960795 + 3945198 * 2 ^ 59
def prefixEnd_3945198 : Nat := 4983230072969 + 3 ^ 40 * 3945198 * 2
def baseEnd_3945198 : Nat := 50019329658191620453861

theorem tailTrace_3945198 : CollatzResearch.WordTrace tailWord_3945198 prefixEnd_3945198 50019329658191620453861 := by
  unfold tailWord_3945198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17986649045153613377581531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95928794907485938013768165 17986649045153613377581531)
  ·
    refine ⟨26979973567730420066372297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17986649045153613377581531 26979973567730420066372297)
    ·
      refine ⟨20234980175797815049779223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26979973567730420066372297 20234980175797815049779223)
      ·
        refine ⟨30352470263696722574668835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20234980175797815049779223 30352470263696722574668835)
        ·
          refine ⟨45528705395545083862003253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30352470263696722574668835 45528705395545083862003253)
          ·
            refine ⟨4268316130832351612062805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45528705395545083862003253 4268316130832351612062805)
            ·
              refine ⟨50019329658191620453861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4268316130832351612062805 50019329658191620453861)
              ·
                rfl

theorem cell22_3945198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 8].length) (baseStart_3945198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945198 prefixEnd_3945198 := by exact prefixLift 3945198
  have htrace : WordTrace (prefixWord ++ tailWord_3945198) baseStart_3945198 baseEnd_3945198 := by
    simpa [prefixWord, tailWord_3945198, baseEnd_3945198] using wordTrace_append hprefix tailTrace_3945198
  have hstable : (prefixWord ++ tailWord_3945198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945198).length < 2 ^ (prefixWord ++ tailWord_3945198).sum := by decide
  have hdescent : baseEnd_3945198 < baseStart_3945198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945204 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3945204 : Nat := 118140960795 + 3945204 * 2 ^ 59
def prefixEnd_3945204 : Nat := 4983230072969 + 3 ^ 40 * 3945204 * 2
def baseEnd_3945204 : Nat := 450174651564597245534743

theorem tailTrace_3945204 : CollatzResearch.WordTrace tailWord_3945204 prefixEnd_3945204 450174651564597245534743 := by
  unfold tailWord_3945204
  simp only [CollatzResearch.WordTrace]
  refine ⟨71946705599603585022685333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95928940799471446696913777 71946705599603585022685333)
  ·
    refine ⟨3372501824981418047938375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71946705599603585022685333 3372501824981418047938375)
    ·
      refine ⟨5058752737472127071907563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3372501824981418047938375 5058752737472127071907563)
      ·
        refine ⟨7588129106208190607861345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5058752737472127071907563 7588129106208190607861345)
        ·
          refine ⟨5691096829656142955896009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7588129106208190607861345 5691096829656142955896009)
          ·
            refine ⟨4268322622242107216922007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5691096829656142955896009 4268322622242107216922007)
            ·
              refine ⟨6402483933363160825383011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268322622242107216922007 6402483933363160825383011)
              ·
                refine ⟨9603725900044741238074517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6402483933363160825383011 9603725900044741238074517)
                ·
                  refine ⟨450174651564597245534743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9603725900044741238074517 450174651564597245534743)
                  ·
                    rfl

theorem cell22_3945204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3945204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945204 prefixEnd_3945204 := by exact prefixLift 3945204
  have htrace : WordTrace (prefixWord ++ tailWord_3945204) baseStart_3945204 baseEnd_3945204 := by
    simpa [prefixWord, tailWord_3945204, baseEnd_3945204] using wordTrace_append hprefix tailTrace_3945204
  have hstable : (prefixWord ++ tailWord_3945204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945204).length < 2 ^ (prefixWord ++ tailWord_3945204).sum := by decide
  have hdescent : baseEnd_3945204 < baseStart_3945204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945241 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_3945241 : Nat := 118140960795 + 3945241 * 2 ^ 59
def prefixEnd_3945241 : Nat := 4983230072969 + 3 ^ 40 * 3945241 * 2
def baseEnd_3945241 : Nat := 1350536620549935973429115

theorem tailTrace_3945241 : CollatzResearch.WordTrace tailWord_3945241 prefixEnd_3945241 1350536620549935973429115 := by
  unfold tailWord_3945241
  simp only [CollatzResearch.WordTrace]
  refine ⟨143894760700073125364467577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95929840466715416909645051 143894760700073125364467577)
  ·
    refine ⟨107921070525054844023350683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143894760700073125364467577 107921070525054844023350683)
    ·
      refine ⟨161881605787582266035026025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107921070525054844023350683 161881605787582266035026025)
      ·
        refine ⟨121411204340686699526269519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161881605787582266035026025 121411204340686699526269519)
        ·
          refine ⟨182116806511030049289404279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121411204340686699526269519 182116806511030049289404279)
          ·
            refine ⟨273175209766545073934106419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182116806511030049289404279 273175209766545073934106419)
            ·
              refine ⟨409762814649817610901159629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273175209766545073934106419 409762814649817610901159629)
              ·
                refine ⟨153661055493681604087934861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409762814649817610901159629 153661055493681604087934861)
                ·
                  refine ⟨57622895810130601532975573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153661055493681604087934861 57622895810130601532975573)
                  ·
                    refine ⟨1350536620549935973429115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57622895810130601532975573 1350536620549935973429115)
                    ·
                      rfl

theorem cell22_3945241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_3945241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945241 prefixEnd_3945241 := by exact prefixLift 3945241
  have htrace : WordTrace (prefixWord ++ tailWord_3945241) baseStart_3945241 baseEnd_3945241 := by
    simpa [prefixWord, tailWord_3945241, baseEnd_3945241] using wordTrace_append hprefix tailTrace_3945241
  have hstable : (prefixWord ++ tailWord_3945241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945241).length < 2 ^ (prefixWord ++ tailWord_3945241).sum := by decide
  have hdescent : baseEnd_3945241 < baseStart_3945241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945288 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 6]
def baseStart_3945288 : Nat := 118140960795 + 3945288 * 2 ^ 59
def prefixEnd_3945288 : Nat := 4983230072969 + 3 ^ 40 * 3945288 * 2
def baseEnd_3945288 : Nat := 450184236536814505834657

theorem tailTrace_3945288 : CollatzResearch.WordTrace tailWord_3945288 prefixEnd_3945288 450184236536814505834657 := by
  unfold tailWord_3945288
  simp only [CollatzResearch.WordTrace]
  refine ⟨71948237465451426195714259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95930983287268568260952345 71948237465451426195714259)
  ·
    refine ⟨107922356198177139293571389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71948237465451426195714259 107922356198177139293571389)
    ·
      refine ⟨40470883574316427235089271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107922356198177139293571389 40470883574316427235089271)
      ·
        refine ⟨60706325361474640852633907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40470883574316427235089271 60706325361474640852633907)
        ·
          refine ⟨91059488042211961278950861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60706325361474640852633907 91059488042211961278950861)
          ·
            refine ⟨34147308015829485479606573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91059488042211961278950861 34147308015829485479606573)
            ·
              refine ⟨12805240505936057054852465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34147308015829485479606573 12805240505936057054852465)
              ·
                refine ⟨9603930379452042791139349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12805240505936057054852465 9603930379452042791139349)
                ·
                  refine ⟨450184236536814505834657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9603930379452042791139349 450184236536814505834657)
                  ·
                    rfl

theorem cell22_3945288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_3945288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945288 prefixEnd_3945288 := by exact prefixLift 3945288
  have htrace : WordTrace (prefixWord ++ tailWord_3945288) baseStart_3945288 baseEnd_3945288 := by
    simpa [prefixWord, tailWord_3945288, baseEnd_3945288] using wordTrace_append hprefix tailTrace_3945288
  have hstable : (prefixWord ++ tailWord_3945288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945288).length < 2 ^ (prefixWord ++ tailWord_3945288).sum := by decide
  have hdescent : baseEnd_3945288 < baseStart_3945288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945305 : List Nat := [1, 2, 1, 2, 2, 4, 1, 5, 4]
def baseStart_3945305 : Nat := 118140960795 + 3945305 * 2 ^ 59
def prefixEnd_3945305 : Nat := 4983230072969 + 3 ^ 40 * 3945305 * 2
def baseEnd_3945305 : Nat := 450186176352620379942973

theorem tailTrace_3945305 : CollatzResearch.WordTrace tailWord_3945305 prefixEnd_3945305 450186176352620379942973 := by
  unfold tailWord_3945305
  simp only [CollatzResearch.WordTrace]
  refine ⟨143897094971841264294797369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95931396647894176196531579 143897094971841264294797369)
  ·
    refine ⟨107922821228880948221098027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143897094971841264294797369 107922821228880948221098027)
    ·
      refine ⟨161884231843321422331647041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107922821228880948221098027 161884231843321422331647041)
      ·
        refine ⟨121413173882491066748735281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161884231843321422331647041 121413173882491066748735281)
        ·
          refine ⟨91059880411868300061551461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121413173882491066748735281 91059880411868300061551461)
          ·
            refine ⟨17073727577225306261540899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91059880411868300061551461 17073727577225306261540899)
            ·
              refine ⟨25610591365837959392311349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17073727577225306261540899 25610591365837959392311349)
              ·
                refine ⟨2400992940547308693029189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25610591365837959392311349 2400992940547308693029189)
                ·
                  refine ⟨450186176352620379942973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2400992940547308693029189 450186176352620379942973)
                  ·
                    rfl

theorem cell22_3945305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 4].length) (baseStart_3945305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945305 prefixEnd_3945305 := by exact prefixLift 3945305
  have htrace : WordTrace (prefixWord ++ tailWord_3945305) baseStart_3945305 baseEnd_3945305 := by
    simpa [prefixWord, tailWord_3945305, baseEnd_3945305] using wordTrace_append hprefix tailTrace_3945305
  have hstable : (prefixWord ++ tailWord_3945305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945305).length < 2 ^ (prefixWord ++ tailWord_3945305).sum := by decide
  have hdescent : baseEnd_3945305 < baseStart_3945305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945348 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_3945348 : Nat := 118140960795 + 3945348 * 2 ^ 59
def prefixEnd_3945348 : Nat := 4983230072969 + 3 ^ 40 * 3945348 * 2
def baseEnd_3945348 : Nat := 1350573248836623361003787

theorem tailTrace_3945348 : CollatzResearch.WordTrace tailWord_3945348 prefixEnd_3945348 1350573248836623361003787 := by
  unfold tailWord_3945348
  simp only [CollatzResearch.WordTrace]
  refine ⟨71949331655342741319306349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95932442207123655092408465 71949331655342741319306349)
  ·
    refine ⟨26980999370753527994739881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71949331655342741319306349 26980999370753527994739881)
    ·
      refine ⟨20235749528065145996054911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26980999370753527994739881 20235749528065145996054911)
      ·
        refine ⟨30353624292097718994082367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20235749528065145996054911 30353624292097718994082367)
        ·
          refine ⟨45530436438146578491123551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30353624292097718994082367 45530436438146578491123551)
          ·
            refine ⟨68295654657219867736685327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45530436438146578491123551 68295654657219867736685327)
            ·
              refine ⟨102443481985829801605027991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68295654657219867736685327 102443481985829801605027991)
              ·
                refine ⟨153665222978744702407541987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102443481985829801605027991 153665222978744702407541987)
                ·
                  refine ⟨230497834468117053611312981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153665222978744702407541987 230497834468117053611312981)
                  ·
                    refine ⟨1350573248836623361003787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 230497834468117053611312981 1350573248836623361003787)
                    ·
                      rfl

theorem cell22_3945348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_3945348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945348 prefixEnd_3945348 := by exact prefixLift 3945348
  have htrace : WordTrace (prefixWord ++ tailWord_3945348) baseStart_3945348 baseEnd_3945348 := by
    simpa [prefixWord, tailWord_3945348, baseEnd_3945348] using wordTrace_append hprefix tailTrace_3945348
  have hstable : (prefixWord ++ tailWord_3945348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945348).length < 2 ^ (prefixWord ++ tailWord_3945348).sum := by decide
  have hdescent : baseEnd_3945348 < baseStart_3945348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945455 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 1, 5]
def baseStart_3945455 : Nat := 118140960795 + 3945455 * 2 ^ 59
def prefixEnd_3945455 : Nat := 4983230072969 + 3 ^ 40 * 3945455 * 2
def baseEnd_3945455 : Nat := 1350609877123310748578459

theorem tailTrace_3945455 : CollatzResearch.WordTrace tailWord_3945455 prefixEnd_3945455 1350609877123310748578459 := by
  unfold tailWord_3945455
  simp only [CollatzResearch.WordTrace]
  refine ⟨143902565921297839912757819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95935043947531893275171879 143902565921297839912757819)
  ·
    refine ⟨215853848881946759869136729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143902565921297839912757819 215853848881946759869136729)
    ·
      refine ⟨161890386661460069901852547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215853848881946759869136729 161890386661460069901852547)
      ·
        refine ⟨242835579992190104852778821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161890386661460069901852547 242835579992190104852778821)
        ·
          refine ⟨45531671248535644659896029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242835579992190104852778821 45531671248535644659896029)
          ·
            refine ⟨17074376718200866747461011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45531671248535644659896029 17074376718200866747461011)
            ·
              refine ⟨25611565077301300121191517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17074376718200866747461011 25611565077301300121191517)
              ·
                refine ⟨9604336903987987545446819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25611565077301300121191517 9604336903987987545446819)
                ·
                  refine ⟨14406505355981981318170229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9604336903987987545446819 14406505355981981318170229)
                  ·
                    refine ⟨1350609877123310748578459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14406505355981981318170229 1350609877123310748578459)
                    ·
                      rfl

theorem cell22_3945455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_3945455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945455 prefixEnd_3945455 := by exact prefixLift 3945455
  have htrace : WordTrace (prefixWord ++ tailWord_3945455) baseStart_3945455 baseEnd_3945455 := by
    simpa [prefixWord, tailWord_3945455, baseEnd_3945455] using wordTrace_append hprefix tailTrace_3945455
  have hstable : (prefixWord ++ tailWord_3945455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945455).length < 2 ^ (prefixWord ++ tailWord_3945455).sum := by decide
  have hdescent : baseEnd_3945455 < baseStart_3945455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945506 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3945506 : Nat := 118140960795 + 3945506 * 2 ^ 59
def prefixEnd_3945506 : Nat := 4983230072969 + 3 ^ 40 * 3945506 * 2
def baseEnd_3945506 : Nat := 1350627335465563615553303

theorem tailTrace_3945506 : CollatzResearch.WordTrace tailWord_3945506 prefixEnd_3945506 1350627335465563615553303 := by
  unfold tailWord_3945506
  simp only [CollatzResearch.WordTrace]
  refine ⟨35976106511028268905716093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95936284029408717081909581 35976106511028268905716093)
  ·
    refine ⟨13491039941635600839643535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35976106511028268905716093 13491039941635600839643535)
    ·
      refine ⟨20236559912453401259465303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13491039941635600839643535 20236559912453401259465303)
      ·
        refine ⟨30354839868680101889197955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20236559912453401259465303 30354839868680101889197955)
        ·
          refine ⟨45532259803020152833796933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30354839868680101889197955 45532259803020152833796933)
          ·
            refine ⟨8537298713066278656336925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45532259803020152833796933 8537298713066278656336925)
            ·
              refine ⟨3201487017399854496126347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8537298713066278656336925 3201487017399854496126347)
              ·
                refine ⟨4802230526099781744189521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201487017399854496126347 4802230526099781744189521)
                ·
                  refine ⟨3601672894574836308142141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4802230526099781744189521 3601672894574836308142141)
                  ·
                    refine ⟨1350627335465563615553303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3601672894574836308142141 1350627335465563615553303)
                    ·
                      rfl

theorem cell22_3945506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3945506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945506 prefixEnd_3945506 := by exact prefixLift 3945506
  have htrace : WordTrace (prefixWord ++ tailWord_3945506) baseStart_3945506 baseEnd_3945506 := by
    simpa [prefixWord, tailWord_3945506, baseEnd_3945506] using wordTrace_append hprefix tailTrace_3945506
  have hstable : (prefixWord ++ tailWord_3945506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945506).length < 2 ^ (prefixWord ++ tailWord_3945506).sum := by decide
  have hdescent : baseEnd_3945506 < baseStart_3945506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945530 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_3945530 : Nat := 118140960795 + 3945530 * 2 ^ 59
def prefixEnd_3945530 : Nat := 4983230072969 + 3 ^ 40 * 3945530 * 2
def baseEnd_3945530 : Nat := 450211850385345184317743

theorem tailTrace_3945530 : CollatzResearch.WordTrace tailWord_3945530 prefixEnd_3945530 450211850385345184317743 := by
  unfold tailWord_3945530
  simp only [CollatzResearch.WordTrace]
  refine ⟨35976325349006531930434511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95936867597350751814492029 35976325349006531930434511)
  ·
    refine ⟨53964488023509797895651767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35976325349006531930434511 53964488023509797895651767)
    ·
      refine ⟨80946732035264696843477651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53964488023509797895651767 80946732035264696843477651)
      ·
        refine ⟨121420098052897045265216477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80946732035264696843477651 121420098052897045265216477)
        ·
          refine ⟨45532536769836391974456179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121420098052897045265216477 45532536769836391974456179)
          ·
            refine ⟨68298805154754587961684269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45532536769836391974456179 68298805154754587961684269)
            ·
              refine ⟨25612051933032970485631601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68298805154754587961684269 25612051933032970485631601)
              ·
                refine ⟨19209038949774727864223701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25612051933032970485631601 19209038949774727864223701)
                ·
                  refine ⟨450211850385345184317743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19209038949774727864223701 450211850385345184317743)
                  ·
                    rfl

theorem cell22_3945530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_3945530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945530 prefixEnd_3945530 := by exact prefixLift 3945530
  have htrace : WordTrace (prefixWord ++ tailWord_3945530) baseStart_3945530 baseEnd_3945530 := by
    simpa [prefixWord, tailWord_3945530, baseEnd_3945530] using wordTrace_append hprefix tailTrace_3945530
  have hstable : (prefixWord ++ tailWord_3945530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945530).length < 2 ^ (prefixWord ++ tailWord_3945530).sum := by decide
  have hdescent : baseEnd_3945530 < baseStart_3945530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945545 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_3945545 : Nat := 118140960795 + 3945545 * 2 ^ 59
def prefixEnd_3945545 : Nat := 4983230072969 + 3 ^ 40 * 3945545 * 2
def baseEnd_3945545 : Nat := 1350640685962580513828183

theorem tailTrace_3945545 : CollatzResearch.WordTrace tailWord_3945545 prefixEnd_3945545 1350640685962580513828183 := by
  unfold tailWord_3945545
  simp only [CollatzResearch.WordTrace]
  refine ⟨143905848490971785283534089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95937232327314523522356059 143905848490971785283534089)
  ·
    refine ⟨107929386368228838962650567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143905848490971785283534089 107929386368228838962650567)
    ·
      refine ⟨161894079552343258443975851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107929386368228838962650567 161894079552343258443975851)
      ·
        refine ⟨242841119328514887665963777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161894079552343258443975851 242841119328514887665963777)
        ·
          refine ⟨182130839496386165749472833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242841119328514887665963777 182130839496386165749472833)
          ·
            refine ⟨136598129622289624312104625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182130839496386165749472833 136598129622289624312104625)
            ·
              refine ⟨102448597216717218234078469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136598129622289624312104625 102448597216717218234078469)
              ·
                refine ⟨19209111978134478418889713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102448597216717218234078469 19209111978134478418889713)
                ·
                  refine ⟨14406833983600858814167285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19209111978134478418889713 14406833983600858814167285)
                  ·
                    refine ⟨1350640685962580513828183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14406833983600858814167285 1350640685962580513828183)
                    ·
                      rfl

theorem cell22_3945545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_3945545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945545 prefixEnd_3945545 := by exact prefixLift 3945545
  have htrace : WordTrace (prefixWord ++ tailWord_3945545) baseStart_3945545 baseEnd_3945545 := by
    simpa [prefixWord, tailWord_3945545, baseEnd_3945545] using wordTrace_append hprefix tailTrace_3945545
  have hstable : (prefixWord ++ tailWord_3945545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945545).length < 2 ^ (prefixWord ++ tailWord_3945545).sum := by decide
  have hdescent : baseEnd_3945545 < baseStart_3945545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945577 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_3945577 : Nat := 118140960795 + 3945577 * 2 ^ 59
def prefixEnd_3945577 : Nat := 4983230072969 + 3 ^ 40 * 3945577 * 2
def baseEnd_3945577 : Nat := 1350651640216543097028085

theorem tailTrace_3945577 : CollatzResearch.WordTrace tailWord_3945577 prefixEnd_3945577 1350651640216543097028085 := by
  unfold tailWord_3945577
  simp only [CollatzResearch.WordTrace]
  refine ⟨143907015626855854748698985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95938010417903903165799323 143907015626855854748698985)
  ·
    refine ⟨107930261720141891061524239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143907015626855854748698985 107930261720141891061524239)
    ·
      refine ⟨161895392580212836592286359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107930261720141891061524239 161895392580212836592286359)
      ·
        refine ⟨242843088870319254888429539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161895392580212836592286359 242843088870319254888429539)
        ·
          refine ⟨364264633305478882332644309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242843088870319254888429539 364264633305478882332644309)
          ·
            refine ⟨8537452343097161304671351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 364264633305478882332644309 8537452343097161304671351)
            ·
              refine ⟨12806178514645741957007027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8537452343097161304671351 12806178514645741957007027)
              ·
                refine ⟨19209267771968612935510541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12806178514645741957007027 19209267771968612935510541)
                ·
                  refine ⟨7203475414488229850816453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19209267771968612935510541 7203475414488229850816453)
                  ·
                    refine ⟨1350651640216543097028085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7203475414488229850816453 1350651640216543097028085)
                    ·
                      rfl

theorem cell22_3945577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_3945577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945577 prefixEnd_3945577 := by exact prefixLift 3945577
  have htrace : WordTrace (prefixWord ++ tailWord_3945577) baseStart_3945577 baseEnd_3945577 := by
    simpa [prefixWord, tailWord_3945577, baseEnd_3945577] using wordTrace_append hprefix tailTrace_3945577
  have hstable : (prefixWord ++ tailWord_3945577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945577).length < 2 ^ (prefixWord ++ tailWord_3945577).sum := by decide
  have hdescent : baseEnd_3945577 < baseStart_3945577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945609 : List Nat := [1, 2, 1, 1, 4, 4, 1, 4, 4]
def baseStart_3945609 : Nat := 118140960795 + 3945609 * 2 ^ 59
def prefixEnd_3945609 : Nat := 4983230072969 + 3 ^ 40 * 3945609 * 2
def baseEnd_3945609 : Nat := 450220864823501893409329

theorem tailTrace_3945609 : CollatzResearch.WordTrace tailWord_3945609 prefixEnd_3945609 450220864823501893409329 := by
  unfold tailWord_3945609
  simp only [CollatzResearch.WordTrace]
  refine ⟨143908182762739924213863881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95938788508493282809242587 143908182762739924213863881)
  ·
    refine ⟨107931137072054943160397911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143908182762739924213863881 107931137072054943160397911)
    ·
      refine ⟨161896705608082414740596867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107931137072054943160397911 161896705608082414740596867)
      ·
        refine ⟨242845058412123622110895301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161896705608082414740596867 242845058412123622110895301)
        ·
          refine ⟨45533448452273179145792869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242845058412123622110895301 45533448452273179145792869)
          ·
            refine ⟨8537521584801221089836163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45533448452273179145792869 8537521584801221089836163)
            ·
              refine ⟨12806282377201831634754245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8537521584801221089836163 12806282377201831634754245)
              ·
                refine ⟨2401177945725343431516421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12806282377201831634754245 2401177945725343431516421)
                ·
                  refine ⟨450220864823501893409329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401177945725343431516421 450220864823501893409329)
                  ·
                    rfl

theorem cell22_3945609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 4].length) (baseStart_3945609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945609 prefixEnd_3945609 := by exact prefixLift 3945609
  have htrace : WordTrace (prefixWord ++ tailWord_3945609) baseStart_3945609 baseEnd_3945609 := by
    simpa [prefixWord, tailWord_3945609, baseEnd_3945609] using wordTrace_append hprefix tailTrace_3945609
  have hstable : (prefixWord ++ tailWord_3945609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945609).length < 2 ^ (prefixWord ++ tailWord_3945609).sum := by decide
  have hdescent : baseEnd_3945609 < baseStart_3945609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945624 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 1, 5]
def baseStart_3945624 : Nat := 118140960795 + 3945624 * 2 ^ 59
def prefixEnd_3945624 : Nat := 4983230072969 + 3 ^ 40 * 3945624 * 2
def baseEnd_3945624 : Nat := 1350667729277050641102941

theorem tailTrace_3945624 : CollatzResearch.WordTrace tailWord_3945624 prefixEnd_3945624 1350667729277050641102941 := by
  unfold tailWord_3945624
  simp only [CollatzResearch.WordTrace]
  refine ⟨71954364928842790887829963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95939153238457054517106617 71954364928842790887829963)
  ·
    refine ⟨107931547393264186331744945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71954364928842790887829963 107931547393264186331744945)
    ·
      refine ⟨80948660544948139748808709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107931547393264186331744945 80948660544948139748808709)
      ·
        refine ⟨15177873852177776202901633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80948660544948139748808709 15177873852177776202901633)
        ·
          refine ⟨11383405389133332152176225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15177873852177776202901633 11383405389133332152176225)
          ·
            refine ⟨8537554041849999114132169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11383405389133332152176225 8537554041849999114132169)
            ·
              refine ⟨6403165531387499335599127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8537554041849999114132169 6403165531387499335599127)
              ·
                refine ⟨9604748297081249003398691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403165531387499335599127 9604748297081249003398691)
                ·
                  refine ⟨14407122445621873505098037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9604748297081249003398691 14407122445621873505098037)
                  ·
                    refine ⟨1350667729277050641102941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14407122445621873505098037 1350667729277050641102941)
                    ·
                      rfl

theorem cell22_3945624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_3945624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945624 prefixEnd_3945624 := by exact prefixLift 3945624
  have htrace : WordTrace (prefixWord ++ tailWord_3945624) baseStart_3945624 baseEnd_3945624 := by
    simpa [prefixWord, tailWord_3945624, baseEnd_3945624] using wordTrace_append hprefix tailTrace_3945624
  have hstable : (prefixWord ++ tailWord_3945624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945624).length < 2 ^ (prefixWord ++ tailWord_3945624).sum := by decide
  have hdescent : baseEnd_3945624 < baseStart_3945624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945639 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3945639 : Nat := 118140960795 + 3945639 * 2 ^ 59
def prefixEnd_3945639 : Nat := 4983230072969 + 3 ^ 40 * 3945639 * 2
def baseEnd_3945639 : Nat := 1350672864083595601977895

theorem tailTrace_3945639 : CollatzResearch.WordTrace tailWord_3945639 prefixEnd_3945639 1350672864083595601977895 := by
  unfold tailWord_3945639
  simp only [CollatzResearch.WordTrace]
  refine ⟨143909276952631239337455971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95939517968420826224970647 143909276952631239337455971)
  ·
    refine ⟨215863915428946859006183957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143909276952631239337455971 215863915428946859006183957)
    ·
      refine ⟨10118621035731884015914873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215863915428946859006183957 10118621035731884015914873)
      ·
        refine ⟨7588965776798913011936155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10118621035731884015914873 7588965776798913011936155)
        ·
          refine ⟨11383448665198369517904233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588965776798913011936155 11383448665198369517904233)
          ·
            refine ⟨8537586498898777138428175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11383448665198369517904233 8537586498898777138428175)
            ·
              refine ⟨12806379748348165707642263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8537586498898777138428175 12806379748348165707642263)
              ·
                refine ⟨19209569622522248561463395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12806379748348165707642263 19209569622522248561463395)
                ·
                  refine ⟨28814354433783372842195093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19209569622522248561463395 28814354433783372842195093)
                  ·
                    refine ⟨1350672864083595601977895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28814354433783372842195093 1350672864083595601977895)
                    ·
                      rfl

theorem cell22_3945639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3945639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945639 prefixEnd_3945639 := by exact prefixLift 3945639
  have htrace : WordTrace (prefixWord ++ tailWord_3945639) baseStart_3945639 baseEnd_3945639 := by
    simpa [prefixWord, tailWord_3945639, baseEnd_3945639] using wordTrace_append hprefix tailTrace_3945639
  have hstable : (prefixWord ++ tailWord_3945639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945639).length < 2 ^ (prefixWord ++ tailWord_3945639).sum := by decide
  have hdescent : baseEnd_3945639 < baseStart_3945639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945645 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_3945645 : Nat := 118140960795 + 3945645 * 2 ^ 59
def prefixEnd_3945645 : Nat := 4983230072969 + 3 ^ 40 * 3945645 * 2
def baseEnd_3945645 : Nat := 1350674918006213586327877

theorem tailTrace_3945645 : CollatzResearch.WordTrace tailWord_3945645 prefixEnd_3945645 1350674918006213586327877 := by
  unfold tailWord_3945645
  simp only [CollatzResearch.WordTrace]
  refine ⟨143909495790609502362174389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95939663860406334908116259 143909495790609502362174389)
  ·
    refine ⟨13491515230369640846453849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143909495790609502362174389 13491515230369640846453849)
    ·
      refine ⟨10118636422777230634840387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13491515230369640846453849 10118636422777230634840387)
      ·
        refine ⟨15177954634165845952260581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10118636422777230634840387 15177954634165845952260581)
        ·
          refine ⟨2845866493906096116048859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15177954634165845952260581 2845866493906096116048859)
          ·
            refine ⟨4268799740859144174073289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845866493906096116048859 4268799740859144174073289)
            ·
              refine ⟨3201599805644358130554967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4268799740859144174073289 3201599805644358130554967)
              ·
                refine ⟨4802399708466537195832451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201599805644358130554967 4802399708466537195832451)
                ·
                  refine ⟨7203599562699805793748677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802399708466537195832451 7203599562699805793748677)
                  ·
                    refine ⟨1350674918006213586327877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7203599562699805793748677 1350674918006213586327877)
                    ·
                      rfl

theorem cell22_3945645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_3945645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945645 prefixEnd_3945645 := by exact prefixLift 3945645
  have htrace : WordTrace (prefixWord ++ tailWord_3945645) baseStart_3945645 baseEnd_3945645 := by
    simpa [prefixWord, tailWord_3945645, baseEnd_3945645] using wordTrace_append hprefix tailTrace_3945645
  have hstable : (prefixWord ++ tailWord_3945645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945645).length < 2 ^ (prefixWord ++ tailWord_3945645).sum := by decide
  have hdescent : baseEnd_3945645 < baseStart_3945645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945712 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_3945712 : Nat := 118140960795 + 3945712 * 2 ^ 59
def prefixEnd_3945712 : Nat := 4983230072969 + 3 ^ 40 * 3945712 * 2
def baseEnd_3945712 : Nat := 1350697853475447744902671

theorem tailTrace_3945712 : CollatzResearch.WordTrace tailWord_3945712 prefixEnd_3945712 1350697853475447744902671 := by
  unfold tailWord_3945712
  simp only [CollatzResearch.WordTrace]
  refine ⟨71955969740683386402431695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95941292987577848536575593 71955969740683386402431695)
  ·
    refine ⟨107933954611025079603647543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71955969740683386402431695 107933954611025079603647543)
    ·
      refine ⟨161900931916537619405471315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107933954611025079603647543 161900931916537619405471315)
      ·
        refine ⟨242851397874806429108206973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161900931916537619405471315 242851397874806429108206973)
        ·
          refine ⟨91069274203052410915577615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242851397874806429108206973 91069274203052410915577615)
          ·
            refine ⟨136603911304578616373366423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91069274203052410915577615 136603911304578616373366423)
            ·
              refine ⟨204905866956867924560049635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136603911304578616373366423 204905866956867924560049635)
              ·
                refine ⟨307358800435301886840074453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204905866956867924560049635 307358800435301886840074453)
                ·
                  refine ⟨7203721885202387972814245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 307358800435301886840074453 7203721885202387972814245)
                  ·
                    refine ⟨1350697853475447744902671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7203721885202387972814245 1350697853475447744902671)
                    ·
                      rfl

theorem cell22_3945712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_3945712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945712 prefixEnd_3945712 := by exact prefixLift 3945712
  have htrace : WordTrace (prefixWord ++ tailWord_3945712) baseStart_3945712 baseEnd_3945712 := by
    simpa [prefixWord, tailWord_3945712, baseEnd_3945712] using wordTrace_append hprefix tailTrace_3945712
  have hstable : (prefixWord ++ tailWord_3945712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945712).length < 2 ^ (prefixWord ++ tailWord_3945712).sum := by decide
  have hdescent : baseEnd_3945712 < baseStart_3945712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945776 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 2, 3]
def baseStart_3945776 : Nat := 118140960795 + 3945776 * 2 ^ 59
def prefixEnd_3945776 : Nat := 4983230072969 + 3 ^ 40 * 3945776 * 2
def baseEnd_3945776 : Nat := 1350719761983372911302475

theorem tailTrace_3945776 : CollatzResearch.WordTrace tailWord_3945776 prefixEnd_3945776 1350719761983372911302475 := by
  unfold tailWord_3945776
  simp only [CollatzResearch.WordTrace]
  refine ⟨71957136876567455867596591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95942849168756607823462121 71957136876567455867596591)
  ·
    refine ⟨107935705314851183801394887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71957136876567455867596591 107935705314851183801394887)
    ·
      refine ⟨161903557972276775702092331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107935705314851183801394887 161903557972276775702092331)
      ·
        refine ⟨242855336958415163553138497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161903557972276775702092331 242855336958415163553138497)
        ·
          refine ⟨182141502718811372664853873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242855336958415163553138497 182141502718811372664853873)
          ·
            refine ⟨136606127039108529498640405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182141502718811372664853873 136606127039108529498640405)
            ·
              refine ⟨6403412204958212320248769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136606127039108529498640405 6403412204958212320248769)
              ·
                refine ⟨4802559153718659240186577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6403412204958212320248769 4802559153718659240186577)
                ·
                  refine ⟨3601919365288994430139933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4802559153718659240186577 3601919365288994430139933)
                  ·
                    refine ⟨1350719761983372911302475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3601919365288994430139933 1350719761983372911302475)
                    ·
                      rfl

theorem cell22_3945776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2, 3].length) (baseStart_3945776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945776 prefixEnd_3945776 := by exact prefixLift 3945776
  have htrace : WordTrace (prefixWord ++ tailWord_3945776) baseStart_3945776 baseEnd_3945776 := by
    simpa [prefixWord, tailWord_3945776, baseEnd_3945776] using wordTrace_append hprefix tailTrace_3945776
  have hstable : (prefixWord ++ tailWord_3945776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945776).length < 2 ^ (prefixWord ++ tailWord_3945776).sum := by decide
  have hdescent : baseEnd_3945776 < baseStart_3945776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945778 : List Nat := [3, 2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_3945778 : Nat := 118140960795 + 3945778 * 2 ^ 59
def prefixEnd_3945778 : Nat := 4983230072969 + 3 ^ 40 * 3945778 * 2
def baseEnd_3945778 : Nat := 450240148874748524250823

theorem tailTrace_3945778 : CollatzResearch.WordTrace tailWord_3945778 prefixEnd_3945778 450240148874748524250823 := by
  unfold tailWord_3945778
  simp only [CollatzResearch.WordTrace]
  refine ⟨35978586674781916519191497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95942897799418444051177325 35978586674781916519191497)
  ·
    refine ⟨26983940006086437389393623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35978586674781916519191497 26983940006086437389393623)
    ·
      refine ⟨40475910009129656084090435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26983940006086437389393623 40475910009129656084090435)
      ·
        refine ⟨60713865013694484126135653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40475910009129656084090435 60713865013694484126135653)
        ·
          refine ⟨11383849690067715773650435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60713865013694484126135653 11383849690067715773650435)
          ·
            refine ⟨17075774535101573660475653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11383849690067715773650435 17075774535101573660475653)
            ·
              refine ⟨3201707725331545061339185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17075774535101573660475653 3201707725331545061339185)
              ·
                refine ⟨2401280793998658796004389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3201707725331545061339185 2401280793998658796004389)
                ·
                  refine ⟨450240148874748524250823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401280793998658796004389 450240148874748524250823)
                  ·
                    rfl

theorem cell22_3945778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_3945778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945778 prefixEnd_3945778 := by exact prefixLift 3945778
  have htrace : WordTrace (prefixWord ++ tailWord_3945778) baseStart_3945778 baseEnd_3945778 := by
    simpa [prefixWord, tailWord_3945778, baseEnd_3945778] using wordTrace_append hprefix tailTrace_3945778
  have hstable : (prefixWord ++ tailWord_3945778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945778).length < 2 ^ (prefixWord ++ tailWord_3945778).sum := by decide
  have hdescent : baseEnd_3945778 < baseStart_3945778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945793 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3945793 : Nat := 118140960795 + 3945793 * 2 ^ 59
def prefixEnd_3945793 : Nat := 4983230072969 + 3 ^ 40 * 3945793 * 2
def baseEnd_3945793 : Nat := 1350725581430790533627423

theorem tailTrace_3945793 : CollatzResearch.WordTrace tailWord_3945793 prefixEnd_3945793 1350725581430790533627423 := by
  unfold tailWord_3945793
  simp only [CollatzResearch.WordTrace]
  refine ⟨143914893794073323638562033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95943262529382215759041355 143914893794073323638562033)
  ·
    refine ⟨107936170345554992728921525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143914893794073323638562033 107936170345554992728921525)
    ·
      refine ⟨10119015969895780568336393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107936170345554992728921525 10119015969895780568336393)
      ·
        refine ⟨7589261977421835426252295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10119015969895780568336393 7589261977421835426252295)
        ·
          refine ⟨11383892966132753139378443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7589261977421835426252295 11383892966132753139378443)
          ·
            refine ⟨17075839449199129709067665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11383892966132753139378443 17075839449199129709067665)
            ·
              refine ⟨12806879586899347281800749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17075839449199129709067665 12806879586899347281800749)
              ·
                refine ⟨4802579845087255230675281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12806879586899347281800749 4802579845087255230675281)
                ·
                  refine ⟨3601934883815441423006461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4802579845087255230675281 3601934883815441423006461)
                  ·
                    refine ⟨1350725581430790533627423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3601934883815441423006461 1350725581430790533627423)
                    ·
                      rfl

theorem cell22_3945793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3945793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945793 prefixEnd_3945793 := by exact prefixLift 3945793
  have htrace : WordTrace (prefixWord ++ tailWord_3945793) baseStart_3945793 baseEnd_3945793 := by
    simpa [prefixWord, tailWord_3945793, baseEnd_3945793] using wordTrace_append hprefix tailTrace_3945793
  have hstable : (prefixWord ++ tailWord_3945793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945793).length < 2 ^ (prefixWord ++ tailWord_3945793).sum := by decide
  have hdescent : baseEnd_3945793 < baseStart_3945793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945849 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_3945849 : Nat := 118140960795 + 3945849 * 2 ^ 59
def prefixEnd_3945849 : Nat := 4983230072969 + 3 ^ 40 * 3945849 * 2
def baseEnd_3945849 : Nat := 1350744751375225054227251

theorem tailTrace_3945849 : CollatzResearch.WordTrace tailWord_3945849 prefixEnd_3945849 1350744751375225054227251 := by
  unfold tailWord_3945849
  simp only [CollatzResearch.WordTrace]
  refine ⟨143916936281870445202600601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95944624187913630135067067 143916936281870445202600601)
  ·
    refine ⟨107937702211402833901950451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143916936281870445202600601 107937702211402833901950451)
    ·
      refine ⟨161906553317104250852925677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107937702211402833901950451 161906553317104250852925677)
      ·
        refine ⟨60714957493914094069847129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161906553317104250852925677 60714957493914094069847129)
        ·
          refine ⟨45536218120435570552385347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60714957493914094069847129 45536218120435570552385347)
          ·
            refine ⟨68304327180653355828578021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45536218120435570552385347 68304327180653355828578021)
            ·
              refine ⟨12807061346372504217858379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68304327180653355828578021 12807061346372504217858379)
              ·
                refine ⟨19210592019558756326787569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12807061346372504217858379 19210592019558756326787569)
                ·
                  refine ⟨14407944014669067245090677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19210592019558756326787569 14407944014669067245090677)
                  ·
                    refine ⟨1350744751375225054227251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14407944014669067245090677 1350744751375225054227251)
                    ·
                      rfl

theorem cell22_3945849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_3945849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945849 prefixEnd_3945849 := by exact prefixLift 3945849
  have htrace : WordTrace (prefixWord ++ tailWord_3945849) baseStart_3945849 baseEnd_3945849 := by
    simpa [prefixWord, tailWord_3945849, baseEnd_3945849] using wordTrace_append hprefix tailTrace_3945849
  have hstable : (prefixWord ++ tailWord_3945849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945849).length < 2 ^ (prefixWord ++ tailWord_3945849).sum := by decide
  have hdescent : baseEnd_3945849 < baseStart_3945849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945851 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 5]
def baseStart_3945851 : Nat := 118140960795 + 3945851 * 2 ^ 59
def prefixEnd_3945851 : Nat := 4983230072969 + 3 ^ 40 * 3945851 * 2
def baseEnd_3945851 : Nat := 450248478672032571892415

theorem tailTrace_3945851 : CollatzResearch.WordTrace tailWord_3945851 prefixEnd_3945851 450248478672032571892415 := by
  unfold tailWord_3945851
  simp only [CollatzResearch.WordTrace]
  refine ⟨143917009227863199544173407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95944672818575466362782271 143917009227863199544173407)
  ·
    refine ⟨215875513841794799316260111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143917009227863199544173407 215875513841794799316260111)
    ·
      refine ⟨323813270762692198974390167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215875513841794799316260111 323813270762692198974390167)
      ·
        refine ⟨485719906144038298461585251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323813270762692198974390167 485719906144038298461585251)
        ·
          refine ⟨728579859216057447692377877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485719906144038298461585251 728579859216057447692377877)
          ·
            refine ⟨34152180900752692860580213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 728579859216057447692377877 34152180900752692860580213)
            ·
              refine ⟨3201766959445564955679395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34152180900752692860580213 3201766959445564955679395)
              ·
                refine ⟨4802650439168347433519093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201766959445564955679395 4802650439168347433519093)
                ·
                  refine ⟨450248478672032571892415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4802650439168347433519093 450248478672032571892415)
                  ·
                    rfl

theorem cell22_3945851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 5].length) (baseStart_3945851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945851 prefixEnd_3945851 := by exact prefixLift 3945851
  have htrace : WordTrace (prefixWord ++ tailWord_3945851) baseStart_3945851 baseEnd_3945851 := by
    simpa [prefixWord, tailWord_3945851, baseEnd_3945851] using wordTrace_append hprefix tailTrace_3945851
  have hstable : (prefixWord ++ tailWord_3945851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945851).length < 2 ^ (prefixWord ++ tailWord_3945851).sum := by decide
  have hdescent : baseEnd_3945851 < baseStart_3945851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945881 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 1, 4]
def baseStart_3945881 : Nat := 118140960795 + 3945881 * 2 ^ 59
def prefixEnd_3945881 : Nat := 4983230072969 + 3 ^ 40 * 3945881 * 2
def baseEnd_3945881 : Nat := 1350755705629187637427153

theorem tailTrace_3945881 : CollatzResearch.WordTrace tailWord_3945881 prefixEnd_3945881 1350755705629187637427153 := by
  unfold tailWord_3945881
  simp only [CollatzResearch.WordTrace]
  refine ⟨143918103417754514667765497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95945402278503009778510331 143918103417754514667765497)
  ·
    refine ⟨107938577563315886000824123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143918103417754514667765497 107938577563315886000824123)
    ·
      refine ⟨161907866344973829001236185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107938577563315886000824123 161907866344973829001236185)
      ·
        refine ⟨121430899758730371750927139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161907866344973829001236185 121430899758730371750927139)
        ·
          refine ⟨182146349638095557626390709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121430899758730371750927139 182146349638095557626390709)
          ·
            refine ⟨17076220278571458527474129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182146349638095557626390709 17076220278571458527474129)
            ·
              refine ⟨12807165208928593895605597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17076220278571458527474129 12807165208928593895605597)
              ·
                refine ⟨4802686953348222710852099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12807165208928593895605597 4802686953348222710852099)
                ·
                  refine ⟨7204030430022334066278149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802686953348222710852099 7204030430022334066278149)
                  ·
                    refine ⟨1350755705629187637427153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7204030430022334066278149 1350755705629187637427153)
                    ·
                      rfl

theorem cell22_3945881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_3945881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945881 prefixEnd_3945881 := by exact prefixLift 3945881
  have htrace : WordTrace (prefixWord ++ tailWord_3945881) baseStart_3945881 baseEnd_3945881 := by
    simpa [prefixWord, tailWord_3945881, baseEnd_3945881] using wordTrace_append hprefix tailTrace_3945881
  have hstable : (prefixWord ++ tailWord_3945881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945881).length < 2 ^ (prefixWord ++ tailWord_3945881).sum := by decide
  have hdescent : baseEnd_3945881 < baseStart_3945881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945956 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_3945956 : Nat := 118140960795 + 3945956 * 2 ^ 59
def prefixEnd_3945956 : Nat := 4983230072969 + 3 ^ 40 * 3945956 * 2
def baseEnd_3945956 : Nat := 1350781379661912441801923

theorem tailTrace_3945956 : CollatzResearch.WordTrace tailWord_3945956 prefixEnd_3945956 1350781379661912441801923 := by
  unfold tailWord_3945956
  simp only [CollatzResearch.WordTrace]
  refine ⟨71960419446241401238372861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95947225928321868317830481 71960419446241401238372861)
  ·
    refine ⟨26985157292340525464389823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71960419446241401238372861 26985157292340525464389823)
    ·
      refine ⟨40477735938510788196584735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26985157292340525464389823 40477735938510788196584735)
      ·
        refine ⟨60716603907766182294877103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40477735938510788196584735 60716603907766182294877103)
        ·
          refine ⟨91074905861649273442315655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60716603907766182294877103 91074905861649273442315655)
          ·
            refine ⟨136612358792473910163473483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91074905861649273442315655 136612358792473910163473483)
            ·
              refine ⟨204918538188710865245210225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136612358792473910163473483 204918538188710865245210225)
              ·
                refine ⟨153688903641533148933907669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204918538188710865245210225 153688903641533148933907669)
                ·
                  refine ⟨3602083679098433178138461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 153688903641533148933907669 3602083679098433178138461)
                  ·
                    refine ⟨1350781379661912441801923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3602083679098433178138461 1350781379661912441801923)
                    ·
                      rfl

theorem cell22_3945956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_3945956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945956 prefixEnd_3945956 := by exact prefixLift 3945956
  have htrace : WordTrace (prefixWord ++ tailWord_3945956) baseStart_3945956 baseEnd_3945956 := by
    simpa [prefixWord, tailWord_3945956, baseEnd_3945956] using wordTrace_append hprefix tailTrace_3945956
  have hstable : (prefixWord ++ tailWord_3945956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945956).length < 2 ^ (prefixWord ++ tailWord_3945956).sum := by decide
  have hdescent : baseEnd_3945956 < baseStart_3945956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945999 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 1, 10]
def baseStart_3945999 : Nat := 118140960795 + 3945999 * 2 ^ 59
def prefixEnd_3945999 : Nat := 4983230072969 + 3 ^ 40 * 3945999 * 2
def baseEnd_3945999 : Nat := 1350796099440674662976791

theorem tailTrace_3945999 : CollatzResearch.WordTrace tailWord_3945999 prefixEnd_3945999 1350796099440674662976791 := by
  unfold tailWord_3945999
  simp only [CollatzResearch.WordTrace]
  refine ⟨143922407231327020820561051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95948271487551347213707367 143922407231327020820561051)
  ·
    refine ⟨215883610846990531230841577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143922407231327020820561051 215883610846990531230841577)
    ·
      refine ⟨161912708135242898423131183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215883610846990531230841577 161912708135242898423131183)
      ·
        refine ⟨242869062202864347634696775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161912708135242898423131183 242869062202864347634696775)
        ·
          refine ⟨364303593304296521452045163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242869062202864347634696775 364303593304296521452045163)
          ·
            refine ⟨546455389956444782178067745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364303593304296521452045163 546455389956444782178067745)
            ·
              refine ⟨409841542467333586633550809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546455389956444782178067745 409841542467333586633550809)
              ·
                refine ⟨307381156850500189975163107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409841542467333586633550809 307381156850500189975163107)
                ·
                  refine ⟨461071735275750284962744661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307381156850500189975163107 461071735275750284962744661)
                  ·
                    refine ⟨1350796099440674662976791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 461071735275750284962744661 1350796099440674662976791)
                    ·
                      rfl

theorem cell22_3945999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_3945999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3945999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3945999 prefixEnd_3945999 := by exact prefixLift 3945999
  have htrace : WordTrace (prefixWord ++ tailWord_3945999) baseStart_3945999 baseEnd_3945999 := by
    simpa [prefixWord, tailWord_3945999, baseEnd_3945999] using wordTrace_append hprefix tailTrace_3945999
  have hstable : (prefixWord ++ tailWord_3945999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945999).length < 2 ^ (prefixWord ++ tailWord_3945999).sum := by decide
  have hdescent : baseEnd_3945999 < baseStart_3945999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946003 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 5]
def baseStart_3946003 : Nat := 118140960795 + 3946003 * 2 ^ 59
def prefixEnd_3946003 : Nat := 4983230072969 + 3 ^ 40 * 3946003 * 2
def baseEnd_3946003 : Nat := 450265822907473328625593

theorem tailTrace_3946003 : CollatzResearch.WordTrace tailWord_3946003 prefixEnd_3946003 450265822907473328625593 := by
  unfold tailWord_3946003
  simp only [CollatzResearch.WordTrace]
  refine ⟨143922553123312529503706663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95948368748875019669137775 143922553123312529503706663)
  ·
    refine ⟨215883829684968794255559995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143922553123312529503706663 215883829684968794255559995)
    ·
      refine ⟨323825744527453191383339993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215883829684968794255559995 323825744527453191383339993)
      ·
        refine ⟨242869308395589893537504995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323825744527453191383339993 242869308395589893537504995)
        ·
          refine ⟨364303962593384840306257493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242869308395589893537504995 364303962593384840306257493)
          ·
            refine ⟨4269187061641228597338955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 364303962593384840306257493 4269187061641228597338955)
            ·
              refine ⟨6403780592461842896008433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269187061641228597338955 6403780592461842896008433)
              ·
                refine ⟨4802835444346382172006325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6403780592461842896008433 4802835444346382172006325)
                ·
                  refine ⟨450265822907473328625593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4802835444346382172006325 450265822907473328625593)
                  ·
                    rfl

theorem cell22_3946003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 5].length) (baseStart_3946003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946003 prefixEnd_3946003 := by exact prefixLift 3946003
  have htrace : WordTrace (prefixWord ++ tailWord_3946003) baseStart_3946003 baseEnd_3946003 := by
    simpa [prefixWord, tailWord_3946003, baseEnd_3946003] using wordTrace_append hprefix tailTrace_3946003
  have hstable : (prefixWord ++ tailWord_3946003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946003).length < 2 ^ (prefixWord ++ tailWord_3946003).sum := by decide
  have hdescent : baseEnd_3946003 < baseStart_3946003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946063 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 2, 3]
def baseStart_3946063 : Nat := 118140960795 + 3946063 * 2 ^ 59
def prefixEnd_3946063 : Nat := 4983230072969 + 3 ^ 40 * 3946063 * 2
def baseEnd_3946063 : Nat := 1350818007948599829376595

theorem tailTrace_3946063 : CollatzResearch.WordTrace tailWord_3946063 prefixEnd_3946063 1350818007948599829376595 := by
  unfold tailWord_3946063
  simp only [CollatzResearch.WordTrace]
  refine ⟨143924741503095159750890843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95949827668730106500593895 143924741503095159750890843)
  ·
    refine ⟨215887112254642739626336265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143924741503095159750890843 215887112254642739626336265)
    ·
      refine ⟨161915334190982054719752199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215887112254642739626336265 161915334190982054719752199)
      ·
        refine ⟨242873001286473082079628299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161915334190982054719752199 242873001286473082079628299)
        ·
          refine ⟨364309501929709623119442449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242873001286473082079628299 364309501929709623119442449)
          ·
            refine ⟨273232126447282217339581837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364309501929709623119442449 273232126447282217339581837)
            ·
              refine ⟨102462047417730831502343189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273232126447282217339581837 102462047417730831502343189)
              ·
                refine ⟨4802908472706132726672337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102462047417730831502343189 4802908472706132726672337)
                ·
                  refine ⟨3602181354529599545004253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4802908472706132726672337 3602181354529599545004253)
                  ·
                    refine ⟨1350818007948599829376595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3602181354529599545004253 1350818007948599829376595)
                    ·
                      rfl

theorem cell22_3946063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 3].length) (baseStart_3946063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946063 prefixEnd_3946063 := by exact prefixLift 3946063
  have htrace : WordTrace (prefixWord ++ tailWord_3946063) baseStart_3946063 baseEnd_3946063 := by
    simpa [prefixWord, tailWord_3946063, baseEnd_3946063] using wordTrace_append hprefix tailTrace_3946063
  have hstable : (prefixWord ++ tailWord_3946063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946063).length < 2 ^ (prefixWord ++ tailWord_3946063).sum := by decide
  have hdescent : baseEnd_3946063 < baseStart_3946063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946065 : List Nat := [1, 2, 2, 1, 3, 2, 5, 2, 4]
def baseStart_3946065 : Nat := 118140960795 + 3946065 * 2 ^ 59
def prefixEnd_3946065 : Nat := 4983230072969 + 3 ^ 40 * 3946065 * 2
def baseEnd_3946065 : Nat := 450272897529824163608863

theorem tailTrace_3946065 : CollatzResearch.WordTrace tailWord_3946065 prefixEnd_3946065 450272897529824163608863 := by
  unfold tailWord_3946065
  simp only [CollatzResearch.WordTrace]
  refine ⟨143924814449087914092463649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95949876299391942728309099 143924814449087914092463649)
  ·
    refine ⟨107943610836815935569347737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143924814449087914092463649 107943610836815935569347737)
    ·
      refine ⟨80957708127611951677010803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107943610836815935569347737 80957708127611951677010803)
      ·
        refine ⟨121436562191417927515516205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80957708127611951677010803 121436562191417927515516205)
        ·
          refine ⟨45538710821781722818318577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121436562191417927515516205 45538710821781722818318577)
          ·
            refine ⟨34154033116336292113738933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45538710821781722818318577 34154033116336292113738933)
            ·
              refine ⟨3201940604656527385663025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34154033116336292113738933 3201940604656527385663025)
              ·
                refine ⟨2401455453492395539247269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3201940604656527385663025 2401455453492395539247269)
                ·
                  refine ⟨450272897529824163608863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401455453492395539247269 450272897529824163608863)
                  ·
                    rfl

theorem cell22_3946065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 4].length) (baseStart_3946065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946065 prefixEnd_3946065 := by exact prefixLift 3946065
  have htrace : WordTrace (prefixWord ++ tailWord_3946065) baseStart_3946065 baseEnd_3946065 := by
    simpa [prefixWord, tailWord_3946065, baseEnd_3946065] using wordTrace_append hprefix tailTrace_3946065
  have hstable : (prefixWord ++ tailWord_3946065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946065).length < 2 ^ (prefixWord ++ tailWord_3946065).sum := by decide
  have hdescent : baseEnd_3946065 < baseStart_3946065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946121 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 7]
def baseStart_3946121 : Nat := 118140960795 + 3946121 * 2 ^ 59
def prefixEnd_3946121 : Nat := 4983230072969 + 3 ^ 40 * 3946121 * 2
def baseEnd_3946121 : Nat := 450279287511302337142139

theorem tailTrace_3946121 : CollatzResearch.WordTrace tailWord_3946121 prefixEnd_3946121 450279287511302337142139 := by
  unfold tailWord_3946121
  simp only [CollatzResearch.WordTrace]
  refine ⟨143926856936885035656502217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95951237957923357104334811 143926856936885035656502217)
  ·
    refine ⟨107945142702663776742376663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143926856936885035656502217 107945142702663776742376663)
    ·
      refine ⟨161917714053995665113564995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107945142702663776742376663 161917714053995665113564995)
      ·
        refine ⟨242876571080993497670347493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161917714053995665113564995 242876571080993497670347493)
        ·
          refine ⟨45539357077686280813190155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242876571080993497670347493 45539357077686280813190155)
          ·
            refine ⟨68309035616529421219785233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45539357077686280813190155 68309035616529421219785233)
            ·
              refine ⟨51231776712397065914838925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68309035616529421219785233 51231776712397065914838925)
              ·
                refine ⟨19211916267148899718064597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51231776712397065914838925 19211916267148899718064597)
                ·
                  refine ⟨450279287511302337142139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19211916267148899718064597 450279287511302337142139)
                  ·
                    rfl

theorem cell22_3946121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_3946121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946121 prefixEnd_3946121 := by exact prefixLift 3946121
  have htrace : WordTrace (prefixWord ++ tailWord_3946121) baseStart_3946121 baseEnd_3946121 := by
    simpa [prefixWord, tailWord_3946121, baseEnd_3946121] using wordTrace_append hprefix tailTrace_3946121
  have hstable : (prefixWord ++ tailWord_3946121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946121).length < 2 ^ (prefixWord ++ tailWord_3946121).sum := by decide
  have hdescent : baseEnd_3946121 < baseStart_3946121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946142 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3946142 : Nat := 118140960795 + 3946142 * 2 ^ 59
def prefixEnd_3946142 : Nat := 4983230072969 + 3 ^ 40 * 3946142 * 2
def baseEnd_3946142 : Nat := 1350845051263069956651353

theorem tailTrace_3946142 : CollatzResearch.WordTrace tailWord_3946142 prefixEnd_3946142 1350845051263069956651353 := by
  unfold tailWord_3946142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17990952858726119530377085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95951748579872637495344453 17990952858726119530377085)
  ·
    refine ⟨6746607322022294823891407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17990952858726119530377085 6746607322022294823891407)
    ·
      refine ⟨10119910983033442235837111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6746607322022294823891407 10119910983033442235837111)
      ·
        refine ⟨15179866474550163353755667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10119910983033442235837111 15179866474550163353755667)
        ·
          refine ⟨22769799711825245030633501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15179866474550163353755667 22769799711825245030633501)
          ·
            refine ⟨8538674891934466886487563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22769799711825245030633501 8538674891934466886487563)
            ·
              refine ⟨12808012337901700329731345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8538674891934466886487563 12808012337901700329731345)
              ·
                refine ⟨9606009253426275247298509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12808012337901700329731345 9606009253426275247298509)
                ·
                  refine ⟨3602253470034853217736941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9606009253426275247298509 3602253470034853217736941)
                  ·
                    refine ⟨1350845051263069956651353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3602253470034853217736941 1350845051263069956651353)
                    ·
                      rfl

theorem cell22_3946142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3946142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946142 prefixEnd_3946142 := by exact prefixLift 3946142
  have htrace : WordTrace (prefixWord ++ tailWord_3946142) baseStart_3946142 baseEnd_3946142 := by
    simpa [prefixWord, tailWord_3946142, baseEnd_3946142] using wordTrace_append hprefix tailTrace_3946142
  have hstable : (prefixWord ++ tailWord_3946142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946142).length < 2 ^ (prefixWord ++ tailWord_3946142).sum := by decide
  have hdescent : baseEnd_3946142 < baseStart_3946142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946183 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 6]
def baseStart_3946183 : Nat := 118140960795 + 3946183 * 2 ^ 59
def prefixEnd_3946183 : Nat := 4983230072969 + 3 ^ 40 * 3946183 * 2
def baseEnd_3946183 : Nat := 450286362133653172125409

theorem tailTrace_3946183 : CollatzResearch.WordTrace tailWord_3946183 prefixEnd_3946183 450286362133653172125409 := by
  unfold tailWord_3946183
  simp only [CollatzResearch.WordTrace]
  refine ⟨143929118262660420245259203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95952745508440280163506135 143929118262660420245259203)
  ·
    refine ⟨215893677393990630367888805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143929118262660420245259203 215893677393990630367888805)
    ·
      refine ⟨40480064511373243193979151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215893677393990630367888805 40480064511373243193979151)
      ·
        refine ⟨60720096767059864790968727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40480064511373243193979151 60720096767059864790968727)
        ·
          refine ⟨91080145150589797186453091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60720096767059864790968727 91080145150589797186453091)
          ·
            refine ⟨136620217725884695779679637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91080145150589797186453091 136620217725884695779679637)
            ·
              refine ⟨6404072705900845114672483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136620217725884695779679637 6404072705900845114672483)
              ·
                refine ⟨9606109058851267672008725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6404072705900845114672483 9606109058851267672008725)
                ·
                  refine ⟨450286362133653172125409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9606109058851267672008725 450286362133653172125409)
                  ·
                    rfl

theorem cell22_3946183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 6].length) (baseStart_3946183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946183 prefixEnd_3946183 := by exact prefixLift 3946183
  have htrace : WordTrace (prefixWord ++ tailWord_3946183) baseStart_3946183 baseEnd_3946183 := by
    simpa [prefixWord, tailWord_3946183, baseEnd_3946183] using wordTrace_append hprefix tailTrace_3946183
  have hstable : (prefixWord ++ tailWord_3946183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946183).length < 2 ^ (prefixWord ++ tailWord_3946183).sum := by decide
  have hdescent : baseEnd_3946183 < baseStart_3946183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946189 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3946189 : Nat := 118140960795 + 3946189 * 2 ^ 59
def prefixEnd_3946189 : Nat := 4983230072969 + 3 ^ 40 * 3946189 * 2
def baseEnd_3946189 : Nat := 450287046774525833575403

theorem tailTrace_3946189 : CollatzResearch.WordTrace tailWord_3946189 prefixEnd_3946189 450287046774525833575403 := by
  unfold tailWord_3946189
  simp only [CollatzResearch.WordTrace]
  refine ⟨143929337100638683269977621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95952891400425788846651747 143929337100638683269977621)
  ·
    refine ⟨6746687676592438278280201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143929337100638683269977621 6746687676592438278280201)
    ·
      refine ⟨5060015757444328708710151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6746687676592438278280201 5060015757444328708710151)
      ·
        refine ⟨7590023636166493063065227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5060015757444328708710151 7590023636166493063065227)
        ·
          refine ⟨11385035454249739594597841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7590023636166493063065227 11385035454249739594597841)
          ·
            refine ⟨8538776590687304695948381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11385035454249739594597841 8538776590687304695948381)
            ·
              refine ⟨3202041221507739260980643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8538776590687304695948381 3202041221507739260980643)
              ·
                refine ⟨4803061832261608891470965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202041221507739260980643 4803061832261608891470965)
                ·
                  refine ⟨450287046774525833575403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4803061832261608891470965 450287046774525833575403)
                  ·
                    rfl

theorem cell22_3946189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3946189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946189 prefixEnd_3946189 := by exact prefixLift 3946189
  have htrace : WordTrace (prefixWord ++ tailWord_3946189) baseStart_3946189 baseEnd_3946189 := by
    simpa [prefixWord, tailWord_3946189, baseEnd_3946189] using wordTrace_append hprefix tailTrace_3946189
  have hstable : (prefixWord ++ tailWord_3946189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946189).length < 2 ^ (prefixWord ++ tailWord_3946189).sum := by decide
  have hdescent : baseEnd_3946189 < baseStart_3946189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946213 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_3946213 : Nat := 118140960795 + 3946213 * 2 ^ 59
def prefixEnd_3946213 : Nat := 4983230072969 + 3 ^ 40 * 3946213 * 2
def baseEnd_3946213 : Nat := 1350869356014049438126135

theorem tailTrace_3946213 : CollatzResearch.WordTrace tailWord_3946213 prefixEnd_3946213 1350869356014049438126135 := by
  unfold tailWord_3946213
  simp only [CollatzResearch.WordTrace]
  refine ⟨143930212452551735368851293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95953474968367823579234195 143930212452551735368851293)
  ·
    refine ⟨53973829669706900763319235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143930212452551735368851293 53973829669706900763319235)
    ·
      refine ⟨80960744504560351144978853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53973829669706900763319235 80960744504560351144978853)
      ·
        refine ⟨15180139594605065839683535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80960744504560351144978853 15180139594605065839683535)
        ·
          refine ⟨22770209391907598759525303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15180139594605065839683535 22770209391907598759525303)
          ·
            refine ⟨34155314087861398139287955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22770209391907598759525303 34155314087861398139287955)
            ·
              refine ⟨51232971131792097208931933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34155314087861398139287955 51232971131792097208931933)
              ·
                refine ⟨19212364174422036453349475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51232971131792097208931933 19212364174422036453349475)
                ·
                  refine ⟨28818546261633054680024213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19212364174422036453349475 28818546261633054680024213)
                  ·
                    refine ⟨1350869356014049438126135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28818546261633054680024213 1350869356014049438126135)
                    ·
                      rfl

theorem cell22_3946213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_3946213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946213 prefixEnd_3946213 := by exact prefixLift 3946213
  have htrace : WordTrace (prefixWord ++ tailWord_3946213) baseStart_3946213 baseEnd_3946213 := by
    simpa [prefixWord, tailWord_3946213, baseEnd_3946213] using wordTrace_append hprefix tailTrace_3946213
  have hstable : (prefixWord ++ tailWord_3946213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946213).length < 2 ^ (prefixWord ++ tailWord_3946213).sum := by decide
  have hdescent : baseEnd_3946213 < baseStart_3946213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946230 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_3946230 : Nat := 118140960795 + 3946230 * 2 ^ 59
def prefixEnd_3946230 : Nat := 4983230072969 + 3 ^ 40 * 3946230 * 2
def baseEnd_3946230 : Nat := 1350875175461467060451083

theorem tailTrace_3946230 : CollatzResearch.WordTrace tailWord_3946230 prefixEnd_3946230 1350875175461467060451083 := by
  unfold tailWord_3946230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8995677030843134204513759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95953888328993431514813429 8995677030843134204513759)
  ·
    refine ⟨13493515546264701306770639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8995677030843134204513759 13493515546264701306770639)
    ·
      refine ⟨20240273319397051960155959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13493515546264701306770639 20240273319397051960155959)
      ·
        refine ⟨30360409979095577940233939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20240273319397051960155959 30360409979095577940233939)
        ·
          refine ⟨45540614968643366910350909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30360409979095577940233939 45540614968643366910350909)
          ·
            refine ⟨17077730613241262591381591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45540614968643366910350909 17077730613241262591381591)
            ·
              refine ⟨25616595919861893887072387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17077730613241262591381591 25616595919861893887072387)
              ·
                refine ⟨38424893879792840830608581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25616595919861893887072387 38424893879792840830608581)
                ·
                  refine ⟨7204667602461157655739109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38424893879792840830608581 7204667602461157655739109)
                  ·
                    refine ⟨1350875175461467060451083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7204667602461157655739109 1350875175461467060451083)
                    ·
                      rfl

theorem cell22_3946230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_3946230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946230 prefixEnd_3946230 := by exact prefixLift 3946230
  have htrace : WordTrace (prefixWord ++ tailWord_3946230) baseStart_3946230 baseEnd_3946230 := by
    simpa [prefixWord, tailWord_3946230, baseEnd_3946230] using wordTrace_append hprefix tailTrace_3946230
  have hstable : (prefixWord ++ tailWord_3946230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946230).length < 2 ^ (prefixWord ++ tailWord_3946230).sum := by decide
  have hdescent : baseEnd_3946230 < baseStart_3946230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946290 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_3946290 : Nat := 118140960795 + 3946290 * 2 ^ 59
def prefixEnd_3946290 : Nat := 4983230072969 + 3 ^ 40 * 3946290 * 2
def baseEnd_3946290 : Nat := 450298571562548967983633

theorem tailTrace_3946290 : CollatzResearch.WordTrace tailWord_3946290 prefixEnd_3946290 450298571562548967983633 := by
  unfold tailWord_3946290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35983255218318194379851081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95955347248848518346269549 35983255218318194379851081)
  ·
    refine ⟨26987441413738645784888311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35983255218318194379851081 26987441413738645784888311)
    ·
      refine ⟨40481162120607968677332467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26987441413738645784888311 40481162120607968677332467)
      ·
        refine ⟨60721743180911953015998701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40481162120607968677332467 60721743180911953015998701)
        ·
          refine ⟨22770653692841982380999513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60721743180911953015998701 22770653692841982380999513)
          ·
            refine ⟨17077990269631486785749635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22770653692841982380999513 17077990269631486785749635)
            ·
              refine ⟨25616985404447230178624453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17077990269631486785749635 25616985404447230178624453)
              ·
                refine ⟨4803184763333855658492085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25616985404447230178624453 4803184763333855658492085)
                ·
                  refine ⟨450298571562548967983633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4803184763333855658492085 450298571562548967983633)
                  ·
                    rfl

theorem cell22_3946290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_3946290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946290 prefixEnd_3946290 := by exact prefixLift 3946290
  have htrace : WordTrace (prefixWord ++ tailWord_3946290) baseStart_3946290 baseEnd_3946290 := by
    simpa [prefixWord, tailWord_3946290, baseEnd_3946290] using wordTrace_append hprefix tailTrace_3946290
  have hstable : (prefixWord ++ tailWord_3946290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946290).length < 2 ^ (prefixWord ++ tailWord_3946290).sum := by decide
  have hdescent : baseEnd_3946290 < baseStart_3946290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946320 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 1, 4]
def baseStart_3946320 : Nat := 118140960795 + 3946320 * 2 ^ 59
def prefixEnd_3946320 : Nat := 4983230072969 + 3 ^ 40 * 3946320 * 2
def baseEnd_3946320 : Nat := 1350905984300736825700807

theorem tailTrace_3946320 : CollatzResearch.WordTrace tailWord_3946320 prefixEnd_3946320 1350905984300736825700807 := by
  unfold tailWord_3946320
  simp only [CollatzResearch.WordTrace]
  refine ⟨71967057531582046321498207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95956076708776061761997609 71967057531582046321498207)
  ·
    refine ⟨107950586297373069482247311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71967057531582046321498207 107950586297373069482247311)
    ·
      refine ⟨161925879446059604223370967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107950586297373069482247311 161925879446059604223370967)
      ·
        refine ⟨242888819169089406335056451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161925879446059604223370967 242888819169089406335056451)
        ·
          refine ⟨364333228753634109502584677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242888819169089406335056451 364333228753634109502584677)
          ·
            refine ⟨68312480391306395531734627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364333228753634109502584677 68312480391306395531734627)
            ·
              refine ⟨102468720586959593297601941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68312480391306395531734627 102468720586959593297601941)
              ·
                refine ⟨4803221277513730935825091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102468720586959593297601941 4803221277513730935825091)
                ·
                  refine ⟨7204831916270596403737637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803221277513730935825091 7204831916270596403737637)
                  ·
                    refine ⟨1350905984300736825700807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7204831916270596403737637 1350905984300736825700807)
                    ·
                      rfl

theorem cell22_3946320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_3946320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946320 prefixEnd_3946320 := by exact prefixLift 3946320
  have htrace : WordTrace (prefixWord ++ tailWord_3946320) baseStart_3946320 baseEnd_3946320 := by
    simpa [prefixWord, tailWord_3946320, baseEnd_3946320] using wordTrace_append hprefix tailTrace_3946320
  have hstable : (prefixWord ++ tailWord_3946320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946320).length < 2 ^ (prefixWord ++ tailWord_3946320).sum := by decide
  have hdescent : baseEnd_3946320 < baseStart_3946320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946363 : List Nat := [1, 1, 1, 1, 1, 5, 1, 11]
def baseStart_3946363 : Nat := 118140960795 + 3946363 * 2 ^ 59
def prefixEnd_3946363 : Nat := 4983230072969 + 3 ^ 40 * 3946363 * 2
def baseEnd_3946363 : Nat := 150102300453277671875075

theorem tailTrace_3946363 : CollatzResearch.WordTrace tailWord_3946363 prefixEnd_3946363 150102300453277671875075 := by
  unfold tailWord_3946363
  simp only [CollatzResearch.WordTrace]
  refine ⟨143935683402008310986811743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95957122268005540657874495 143935683402008310986811743)
  ·
    refine ⟨215903525103012466480217615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143935683402008310986811743 215903525103012466480217615)
    ·
      refine ⟨323855287654518699720326423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215903525103012466480217615 323855287654518699720326423)
      ·
        refine ⟨485782931481778049580489635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323855287654518699720326423 485782931481778049580489635)
        ·
          refine ⟨728674397222667074370734453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485782931481778049580489635 728674397222667074370734453)
          ·
            refine ⟨68313224739625038222256355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 728674397222667074370734453 68313224739625038222256355)
            ·
              refine ⟨102469837109437557333384533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68313224739625038222256355 102469837109437557333384533)
              ·
                refine ⟨150102300453277671875075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 102469837109437557333384533 150102300453277671875075)
                ·
                  rfl

theorem cell22_3946363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 11].length) (baseStart_3946363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946363 prefixEnd_3946363 := by exact prefixLift 3946363
  have htrace : WordTrace (prefixWord ++ tailWord_3946363) baseStart_3946363 baseEnd_3946363 := by
    simpa [prefixWord, tailWord_3946363, baseEnd_3946363] using wordTrace_append hprefix tailTrace_3946363
  have hstable : (prefixWord ++ tailWord_3946363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946363).length < 2 ^ (prefixWord ++ tailWord_3946363).sum := by decide
  have hdescent : baseEnd_3946363 < baseStart_3946363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946386 : List Nat := [3, 2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_3946386 : Nat := 118140960795 + 3946386 * 2 ^ 59
def prefixEnd_3946386 : Nat := 4983230072969 + 3 ^ 40 * 3946386 * 2
def baseEnd_3946386 : Nat := 450309525816511551183535

theorem tailTrace_3946386 : CollatzResearch.WordTrace tailWord_3946386 prefixEnd_3946386 450309525816511551183535 := by
  unfold tailWord_3946386
  simp only [CollatzResearch.WordTrace]
  refine ⟨35984130570231246478724753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95957681520616657276599341 35984130570231246478724753)
  ·
    refine ⟨26988097927673434859043565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35984130570231246478724753 26988097927673434859043565)
    ·
      refine ⟨10120536722877538072141337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26988097927673434859043565 10120536722877538072141337)
      ·
        refine ⟨7590402542158153554106003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10120536722877538072141337 7590402542158153554106003)
        ·
          refine ⟨11385603813237230331159005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7590402542158153554106003 11385603813237230331159005)
          ·
            refine ⟨4269601429963961374184627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11385603813237230331159005 4269601429963961374184627)
            ·
              refine ⟨6404402144945942061276941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269601429963961374184627 6404402144945942061276941)
              ·
                refine ⟨2401650804354728272978853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6404402144945942061276941 2401650804354728272978853)
                ·
                  refine ⟨450309525816511551183535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401650804354728272978853 450309525816511551183535)
                  ·
                    rfl

theorem cell22_3946386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_3946386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946386 prefixEnd_3946386 := by exact prefixLift 3946386
  have htrace : WordTrace (prefixWord ++ tailWord_3946386) baseStart_3946386 baseEnd_3946386 := by
    simpa [prefixWord, tailWord_3946386, baseEnd_3946386] using wordTrace_append hprefix tailTrace_3946386
  have hstable : (prefixWord ++ tailWord_3946386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946386).length < 2 ^ (prefixWord ++ tailWord_3946386).sum := by decide
  have hdescent : baseEnd_3946386 < baseStart_3946386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946463 : List Nat := [1, 1, 2, 3, 4, 3, 2, 2, 1, 3]
def baseStart_3946463 : Nat := 118140960795 + 3946463 * 2 ^ 59
def prefixEnd_3946463 : Nat := 4983230072969 + 3 ^ 40 * 3946463 * 2
def baseEnd_3946463 : Nat := 1350954936123132119375369

theorem tailTrace_3946463 : CollatzResearch.WordTrace tailWord_3946463 prefixEnd_3946463 1350954936123132119375369 := by
  unfold tailWord_3946463
  simp only [CollatzResearch.WordTrace]
  refine ⟨143939330701646028065452043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95959553801097352043634695 143939330701646028065452043)
  ·
    refine ⟨215908996052469042098178065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143939330701646028065452043 215908996052469042098178065)
    ·
      refine ⟨161931747039351781573633549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215908996052469042098178065 161931747039351781573633549)
      ·
        refine ⟨60724405139756918090112581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161931747039351781573633549 60724405139756918090112581)
        ·
          refine ⟨11385825963704422141896109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60724405139756918090112581 11385825963704422141896109)
          ·
            refine ⟨4269684736389158303211041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11385825963704422141896109 4269684736389158303211041)
            ·
              refine ⟨3202263552291868727408281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4269684736389158303211041 3202263552291868727408281)
              ·
                refine ⟨2401697664218901545556211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202263552291868727408281 2401697664218901545556211)
                ·
                  refine ⟨3602546496328352318334317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401697664218901545556211 3602546496328352318334317)
                  ·
                    refine ⟨1350954936123132119375369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3602546496328352318334317 1350954936123132119375369)
                    ·
                      rfl

theorem cell22_3946463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 1, 3].length) (baseStart_3946463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946463 prefixEnd_3946463 := by exact prefixLift 3946463
  have htrace : WordTrace (prefixWord ++ tailWord_3946463) baseStart_3946463 baseEnd_3946463 := by
    simpa [prefixWord, tailWord_3946463, baseEnd_3946463] using wordTrace_append hprefix tailTrace_3946463
  have hstable : (prefixWord ++ tailWord_3946463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946463).length < 2 ^ (prefixWord ++ tailWord_3946463).sum := by decide
  have hdescent : baseEnd_3946463 < baseStart_3946463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946504 : List Nat := [2, 1, 3, 2, 1, 2, 4, 3, 4]
def baseStart_3946504 : Nat := 118140960795 + 3946504 * 2 ^ 59
def prefixEnd_3946504 : Nat := 4983230072969 + 3 ^ 40 * 3946504 * 2
def baseEnd_3946504 : Nat := 450322990420340559700081

theorem tailTrace_3946504 : CollatzResearch.WordTrace tailWord_3946504 prefixEnd_3946504 450322990420340559700081 := by
  unfold tailWord_3946504
  simp only [CollatzResearch.WordTrace]
  refine ⟨71970413047248746033847283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95960550729664994711796377 71970413047248746033847283)
  ·
    refine ⟨107955619570873119050770925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71970413047248746033847283 107955619570873119050770925)
    ·
      refine ⟨40483357339077419644039097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107955619570873119050770925 40483357339077419644039097)
      ·
        refine ⟨30362518004308064733029323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40483357339077419644039097 30362518004308064733029323)
        ·
          refine ⟨45543777006462097099543985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30362518004308064733029323 45543777006462097099543985)
          ·
            refine ⟨34157832754846572824657989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45543777006462097099543985 34157832754846572824657989)
            ·
              refine ⟨6404593641533732404623373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34157832754846572824657989 6404593641533732404623373)
              ·
                refine ⟨2401722615575149651733765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6404593641533732404623373 2401722615575149651733765)
                ·
                  refine ⟨450322990420340559700081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401722615575149651733765 450322990420340559700081)
                  ·
                    rfl

theorem cell22_3946504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 4].length) (baseStart_3946504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946504 prefixEnd_3946504 := by exact prefixLift 3946504
  have htrace : WordTrace (prefixWord ++ tailWord_3946504) baseStart_3946504 baseEnd_3946504 := by
    simpa [prefixWord, tailWord_3946504, baseEnd_3946504] using wordTrace_append hprefix tailTrace_3946504
  have hstable : (prefixWord ++ tailWord_3946504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946504).length < 2 ^ (prefixWord ++ tailWord_3946504).sum := by decide
  have hdescent : baseEnd_3946504 < baseStart_3946504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946577 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 5]
def baseStart_3946577 : Nat := 118140960795 + 3946577 * 2 ^ 59
def prefixEnd_3946577 : Nat := 4983230072969 + 3 ^ 40 * 3946577 * 2
def baseEnd_3946577 : Nat := 450331320217624607341673

theorem tailTrace_3946577 : CollatzResearch.WordTrace tailWord_3946577 prefixEnd_3946577 450331320217624607341673 := by
  unfold tailWord_3946577
  simp only [CollatzResearch.WordTrace]
  refine ⟨143943488623233025535101985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95962325748822017023401323 143943488623233025535101985)
  ·
    refine ⟨107957616467424769151326489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143943488623233025535101985 107957616467424769151326489)
    ·
      refine ⟨80968212350568576863494867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107957616467424769151326489 80968212350568576863494867)
      ·
        refine ⟨121452318525852865295242301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80968212350568576863494867 121452318525852865295242301)
        ·
          refine ⟨45544619447194824485715863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121452318525852865295242301 45544619447194824485715863)
          ·
            refine ⟨68316929170792236728573795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45544619447194824485715863 68316929170792236728573795)
            ·
              refine ⟨102475393756188355092860693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68316929170792236728573795 102475393756188355092860693)
              ·
                refine ⟨4803534082321329144977845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102475393756188355092860693 4803534082321329144977845)
                ·
                  refine ⟨450331320217624607341673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4803534082321329144977845 450331320217624607341673)
                  ·
                    rfl

theorem cell22_3946577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_3946577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946577 prefixEnd_3946577 := by exact prefixLift 3946577
  have htrace : WordTrace (prefixWord ++ tailWord_3946577) baseStart_3946577 baseEnd_3946577 := by
    simpa [prefixWord, tailWord_3946577, baseEnd_3946577] using wordTrace_append hprefix tailTrace_3946577
  have hstable : (prefixWord ++ tailWord_3946577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946577).length < 2 ^ (prefixWord ++ tailWord_3946577).sum := by decide
  have hdescent : baseEnd_3946577 < baseStart_3946577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946581 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 3, 3]
def baseStart_3946581 : Nat := 118140960795 + 3946581 * 2 ^ 59
def prefixEnd_3946581 : Nat := 4983230072969 + 3 ^ 40 * 3946581 * 2
def baseEnd_3946581 : Nat := 1350995329934619144925007

theorem tailTrace_3946581 : CollatzResearch.WordTrace tailWord_3946581 prefixEnd_3946581 1350995329934619144925007 := by
  unfold tailWord_3946581
  simp only [CollatzResearch.WordTrace]
  refine ⟨143943634515218534218247597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95962423010145689478831731 143943634515218534218247597)
  ·
    refine ⟨53978862943206950331842849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143943634515218534218247597 53978862943206950331842849)
    ·
      refine ⟨40484147207405212748882137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53978862943206950331842849 40484147207405212748882137)
      ·
        refine ⟨30363110405553909561661603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40484147207405212748882137 30363110405553909561661603)
        ·
          refine ⟨45544665608330864342492405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30363110405553909561661603 45544665608330864342492405)
          ·
            refine ⟨4269812400781018532108663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45544665608330864342492405 4269812400781018532108663)
            ·
              refine ⟨6404718601171527798162995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269812400781018532108663 6404718601171527798162995)
              ·
                refine ⟨9607077901757291697244493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6404718601171527798162995 9607077901757291697244493)
                ·
                  refine ⟨3602654213158984386466685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9607077901757291697244493 3602654213158984386466685)
                  ·
                    refine ⟨1350995329934619144925007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3602654213158984386466685 1350995329934619144925007)
                    ·
                      rfl

theorem cell22_3946581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_3946581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946581 prefixEnd_3946581 := by exact prefixLift 3946581
  have htrace : WordTrace (prefixWord ++ tailWord_3946581) baseStart_3946581 baseEnd_3946581 := by
    simpa [prefixWord, tailWord_3946581, baseEnd_3946581] using wordTrace_append hprefix tailTrace_3946581
  have hstable : (prefixWord ++ tailWord_3946581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946581).length < 2 ^ (prefixWord ++ tailWord_3946581).sum := by decide
  have hdescent : baseEnd_3946581 < baseStart_3946581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946673 : List Nat := [1, 2, 2, 5, 2, 1, 2, 3, 4]
def baseStart_3946673 : Nat := 118140960795 + 3946673 * 2 ^ 59
def prefixEnd_3946673 : Nat := 4983230072969 + 3 ^ 40 * 3946673 * 2
def baseEnd_3946673 : Nat := 450342274471587190541575

theorem tailTrace_3946673 : CollatzResearch.WordTrace tailWord_3946673 prefixEnd_3946673 450342274471587190541575 := by
  unfold tailWord_3946673
  simp only [CollatzResearch.WordTrace]
  refine ⟨143946990030885233930596673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95964660020590155953731115 143946990030885233930596673)
  ·
    refine ⟨107960242523163925447947505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143946990030885233930596673 107960242523163925447947505)
    ·
      refine ⟨80970181892372944085960629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107960242523163925447947505 80970181892372944085960629)
      ·
        refine ⟨7590954552409963508058809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80970181892372944085960629 7590954552409963508058809)
        ·
          refine ⟨5693215914307472631044107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7590954552409963508058809 5693215914307472631044107)
          ·
            refine ⟨8539823871461208946566161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693215914307472631044107 8539823871461208946566161)
            ·
              refine ⟨6404867903595906709924621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8539823871461208946566161 6404867903595906709924621)
              ·
                refine ⟨2401825463848465016221733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6404867903595906709924621 2401825463848465016221733)
                ·
                  refine ⟨450342274471587190541575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401825463848465016221733 450342274471587190541575)
                  ·
                    rfl

theorem cell22_3946673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 4].length) (baseStart_3946673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946673 prefixEnd_3946673 := by exact prefixLift 3946673
  have htrace : WordTrace (prefixWord ++ tailWord_3946673) baseStart_3946673 baseEnd_3946673 := by
    simpa [prefixWord, tailWord_3946673, baseEnd_3946673] using wordTrace_append hprefix tailTrace_3946673
  have hstable : (prefixWord ++ tailWord_3946673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946673).length < 2 ^ (prefixWord ++ tailWord_3946673).sum := by decide
  have hdescent : baseEnd_3946673 < baseStart_3946673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946684 : List Nat := [2, 2, 2, 3, 3, 1, 9]
def baseStart_3946684 : Nat := 118140960795 + 3946684 * 2 ^ 59
def prefixEnd_3946684 : Nat := 4983230072969 + 3 ^ 40 * 3946684 * 2
def baseEnd_3946684 : Nat := 50038169960724489244433

theorem tailTrace_3946684 : CollatzResearch.WordTrace tailWord_3946684 prefixEnd_3946684 50038169960724489244433 := by
  unfold tailWord_3946684
  simp only [CollatzResearch.WordTrace]
  refine ⟨71973695616922691404623553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95964927489230255206164737 71973695616922691404623553)
  ·
    refine ⟨53980271712692018553467665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71973695616922691404623553 53980271712692018553467665)
    ·
      refine ⟨40485203784519013915100749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53980271712692018553467665 40485203784519013915100749)
      ·
        refine ⟨15181951419194630218162781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40485203784519013915100749 15181951419194630218162781)
        ·
          refine ⟨5693231782197986331811043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15181951419194630218162781 5693231782197986331811043)
          ·
            refine ⟨8539847673296979497716565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693231782197986331811043 8539847673296979497716565)
            ·
              refine ⟨50038169960724489244433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8539847673296979497716565 50038169960724489244433)
              ·
                rfl

theorem cell22_3946684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 9].length) (baseStart_3946684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946684 prefixEnd_3946684 := by exact prefixLift 3946684
  have htrace : WordTrace (prefixWord ++ tailWord_3946684) baseStart_3946684 baseEnd_3946684 := by
    simpa [prefixWord, tailWord_3946684, baseEnd_3946684] using wordTrace_append hprefix tailTrace_3946684
  have hstable : (prefixWord ++ tailWord_3946684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946684).length < 2 ^ (prefixWord ++ tailWord_3946684).sum := by decide
  have hdescent : baseEnd_3946684 < baseStart_3946684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946688 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 2, 3]
def baseStart_3946688 : Nat := 118140960795 + 3946688 * 2 ^ 59
def prefixEnd_3946688 : Nat := 4983230072969 + 3 ^ 40 * 3946688 * 2
def baseEnd_3946688 : Nat := 1351031958221306532499679

theorem tailTrace_3946688 : CollatzResearch.WordTrace tailWord_3946688 prefixEnd_3946688 1351031958221306532499679 := by
  unfold tailWord_3946688
  simp only [CollatzResearch.WordTrace]
  refine ⟨71973768562915445746196359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95965024750553927661595145 71973768562915445746196359)
  ·
    refine ⟨107960652844373168619294539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71973768562915445746196359 107960652844373168619294539)
    ·
      refine ⟨161940979266559752928941809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107960652844373168619294539 161940979266559752928941809)
      ·
        refine ⟨121455734449919814696706357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161940979266559752928941809 121455734449919814696706357)
        ·
          refine ⟨11386475104679982627816221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121455734449919814696706357 11386475104679982627816221)
          ·
            refine ⟨4269928164254993485431083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11386475104679982627816221 4269928164254993485431083)
            ·
              refine ⟨6404892246382490228146625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269928164254993485431083 6404892246382490228146625)
              ·
                refine ⟨4803669184786867671109969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6404892246382490228146625 4803669184786867671109969)
                ·
                  refine ⟨3602751888590150753332477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4803669184786867671109969 3602751888590150753332477)
                  ·
                    refine ⟨1351031958221306532499679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3602751888590150753332477 1351031958221306532499679)
                    ·
                      rfl

theorem cell22_3946688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2, 3].length) (baseStart_3946688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946688 prefixEnd_3946688 := by exact prefixLift 3946688
  have htrace : WordTrace (prefixWord ++ tailWord_3946688) baseStart_3946688 baseEnd_3946688 := by
    simpa [prefixWord, tailWord_3946688, baseEnd_3946688] using wordTrace_append hprefix tailTrace_3946688
  have hstable : (prefixWord ++ tailWord_3946688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946688).length < 2 ^ (prefixWord ++ tailWord_3946688).sum := by decide
  have hdescent : baseEnd_3946688 < baseStart_3946688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946690 : List Nat := [3, 5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3946690 : Nat := 118140960795 + 3946690 * 2 ^ 59
def prefixEnd_3946690 : Nat := 4983230072969 + 3 ^ 40 * 3946690 * 2
def baseEnd_3946690 : Nat := 450344214287393064649891

theorem tailTrace_3946690 : CollatzResearch.WordTrace tailWord_3946690 prefixEnd_3946690 450344214287393064649891 := by
  unfold tailWord_3946690
  simp only [CollatzResearch.WordTrace]
  refine ⟨35986902517955911458491381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95965073381215763889310349 35986902517955911458491381)
  ·
    refine ⟨3373772111058366699233567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35986902517955911458491381 3373772111058366699233567)
    ·
      refine ⟨5060658166587550048850351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3373772111058366699233567 5060658166587550048850351)
      ·
        refine ⟨7590987249881325073275527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5060658166587550048850351 7590987249881325073275527)
        ·
          refine ⟨11386480874821987609913291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7590987249881325073275527 11386480874821987609913291)
          ·
            refine ⟨17079721312232981414869937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11386480874821987609913291 17079721312232981414869937)
            ·
              refine ⟨12809790984174736061152453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17079721312232981414869937 12809790984174736061152453)
              ·
                refine ⟨2401835809532763011466085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12809790984174736061152453 2401835809532763011466085)
                ·
                  refine ⟨450344214287393064649891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401835809532763011466085 450344214287393064649891)
                  ·
                    rfl

theorem cell22_3946690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3946690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946690 prefixEnd_3946690 := by exact prefixLift 3946690
  have htrace : WordTrace (prefixWord ++ tailWord_3946690) baseStart_3946690 baseEnd_3946690 := by
    simpa [prefixWord, tailWord_3946690, baseEnd_3946690] using wordTrace_append hprefix tailTrace_3946690
  have hstable : (prefixWord ++ tailWord_3946690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946690).length < 2 ^ (prefixWord ++ tailWord_3946690).sum := by decide
  have hdescent : baseEnd_3946690 < baseStart_3946690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946697 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_3946697 : Nat := 118140960795 + 3946697 * 2 ^ 59
def prefixEnd_3946697 : Nat := 4983230072969 + 3 ^ 40 * 3946697 * 2
def baseEnd_3946697 : Nat := 1351035039105233509024651

theorem tailTrace_3946697 : CollatzResearch.WordTrace tailWord_3946697 prefixEnd_3946697 1351035039105233509024651 := by
  unfold tailWord_3946697
  simp only [CollatzResearch.WordTrace]
  refine ⟨143947865382798286029470345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95965243588532190686313563 143947865382798286029470345)
  ·
    refine ⟨107960899037098714522102759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143947865382798286029470345 107960899037098714522102759)
    ·
      refine ⟨161941348555648071783154139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107960899037098714522102759 161941348555648071783154139)
      ·
        refine ⟨242912022833472107674731209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161941348555648071783154139 242912022833472107674731209)
        ·
          refine ⟨182184017125104080756048407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242912022833472107674731209 182184017125104080756048407)
          ·
            refine ⟨273276025687656121134072611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182184017125104080756048407 273276025687656121134072611)
            ·
              refine ⟨409914038531484181701108917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273276025687656121134072611 409914038531484181701108917)
              ·
                refine ⟨38429441112326642034478961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409914038531484181701108917 38429441112326642034478961)
                ·
                  refine ⟨28822080834244981525859221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38429441112326642034478961 28822080834244981525859221)
                  ·
                    refine ⟨1351035039105233509024651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28822080834244981525859221 1351035039105233509024651)
                    ·
                      rfl

theorem cell22_3946697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_3946697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946697 prefixEnd_3946697 := by exact prefixLift 3946697
  have htrace : WordTrace (prefixWord ++ tailWord_3946697) baseStart_3946697 baseEnd_3946697 := by
    simpa [prefixWord, tailWord_3946697, baseEnd_3946697] using wordTrace_append hprefix tailTrace_3946697
  have hstable : (prefixWord ++ tailWord_3946697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946697).length < 2 ^ (prefixWord ++ tailWord_3946697).sum := by decide
  have hdescent : baseEnd_3946697 < baseStart_3946697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946808 : List Nat := [2, 1, 2, 1, 3, 1, 6, 2, 4]
def baseStart_3946808 : Nat := 118140960795 + 3946808 * 2 ^ 59
def prefixEnd_3946808 : Nat := 4983230072969 + 3 ^ 40 * 3946808 * 2
def baseEnd_3946808 : Nat := 450357678891222073166437

theorem tailTrace_3946808 : CollatzResearch.WordTrace tailWord_3946808 prefixEnd_3946808 450357678891222073166437 := by
  unfold tailWord_3946808
  simp only [CollatzResearch.WordTrace]
  refine ⟨71975956942698075993380539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95967942590264101324507385 71975956942698075993380539)
  ·
    refine ⟨107963935414047113990070809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71975956942698075993380539 107963935414047113990070809)
    ·
      refine ⟨80972951560535335492553107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107963935414047113990070809 80972951560535335492553107)
      ·
        refine ⟨121459427340803003238829661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80972951560535335492553107 121459427340803003238829661)
        ·
          refine ⟨45547285252801126214561123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121459427340803003238829661 45547285252801126214561123)
          ·
            refine ⟨68320927879201689321841685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45547285252801126214561123 68320927879201689321841685)
            ·
              refine ⟨3202543494337579186961329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68320927879201689321841685 3202543494337579186961329)
              ·
                refine ⟨2401907620753184390220997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202543494337579186961329 2401907620753184390220997)
                ·
                  refine ⟨450357678891222073166437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401907620753184390220997 450357678891222073166437)
                  ·
                    rfl

theorem cell22_3946808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 4].length) (baseStart_3946808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946808 prefixEnd_3946808 := by exact prefixLift 3946808
  have htrace : WordTrace (prefixWord ++ tailWord_3946808) baseStart_3946808 baseEnd_3946808 := by
    simpa [prefixWord, tailWord_3946808, baseEnd_3946808] using wordTrace_append hprefix tailTrace_3946808
  have hstable : (prefixWord ++ tailWord_3946808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946808).length < 2 ^ (prefixWord ++ tailWord_3946808).sum := by decide
  have hdescent : baseEnd_3946808 < baseStart_3946808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946819 : List Nat := [1, 1, 1, 3, 1, 3, 5, 7]
def baseStart_3946819 : Nat := 118140960795 + 3946819 * 2 ^ 59
def prefixEnd_3946819 : Nat := 4983230072969 + 3 ^ 40 * 3946819 * 2
def baseEnd_3946819 : Nat := 150119644688718428608253

theorem tailTrace_3946819 : CollatzResearch.WordTrace tailWord_3946819 prefixEnd_3946819 150119644688718428608253 := by
  unfold tailWord_3946819
  simp only [CollatzResearch.WordTrace]
  refine ⟨143952315088356300865411511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95968210058904200576941007 143952315088356300865411511)
  ·
    refine ⟨215928472632534451298117267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143952315088356300865411511 215928472632534451298117267)
    ·
      refine ⟨323892708948801676947175901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215928472632534451298117267 323892708948801676947175901)
      ·
        refine ⟨121459765855800628855190963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323892708948801676947175901 121459765855800628855190963)
        ·
          refine ⟨182189648783700943282786445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121459765855800628855190963 182189648783700943282786445)
          ·
            refine ⟨68321118293887853731044917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182189648783700943282786445 68321118293887853731044917)
            ·
              refine ⟨6405104840051986287285461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68321118293887853731044917 6405104840051986287285461)
              ·
                refine ⟨150119644688718428608253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6405104840051986287285461 150119644688718428608253)
                ·
                  rfl

theorem cell22_3946819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 7].length) (baseStart_3946819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946819 prefixEnd_3946819 := by exact prefixLift 3946819
  have htrace : WordTrace (prefixWord ++ tailWord_3946819) baseStart_3946819 baseEnd_3946819 := by
    simpa [prefixWord, tailWord_3946819, baseEnd_3946819] using wordTrace_append hprefix tailTrace_3946819
  have hstable : (prefixWord ++ tailWord_3946819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946819).length < 2 ^ (prefixWord ++ tailWord_3946819).sum := by decide
  have hdescent : baseEnd_3946819 < baseStart_3946819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946844 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3946844 : Nat := 118140960795 + 3946844 * 2 ^ 59
def prefixEnd_3946844 : Nat := 4983230072969 + 3 ^ 40 * 3946844 * 2
def baseEnd_3946844 : Nat := 1351085360209374125599201

theorem tailTrace_3946844 : CollatzResearch.WordTrace tailWord_3946844 prefixEnd_3946844 1351085360209374125599201 := by
  unfold tailWord_3946844
  simp only [CollatzResearch.WordTrace]
  refine ⟨71976613456632865067535793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95968817942177153423381057 71976613456632865067535793)
  ·
    refine ⟨53982460092474648800651845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71976613456632865067535793 53982460092474648800651845)
    ·
      refine ⟨10121711267338996650122221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53982460092474648800651845 10121711267338996650122221)
      ·
        refine ⟨3795641725252123743795833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10121711267338996650122221 3795641725252123743795833)
        ·
          refine ⟨2846731293939092807846875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3795641725252123743795833 2846731293939092807846875)
          ·
            refine ⟨4270096940908639211770313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846731293939092807846875 4270096940908639211770313)
            ·
              refine ⟨3202572705681479408827735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270096940908639211770313 3202572705681479408827735)
              ·
                refine ⟨4803859058522219113241603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202572705681479408827735 4803859058522219113241603)
                ·
                  refine ⟨7205788587783328669862405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803859058522219113241603 7205788587783328669862405)
                  ·
                    refine ⟨1351085360209374125599201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7205788587783328669862405 1351085360209374125599201)
                    ·
                      rfl

theorem cell22_3946844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3946844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946844 prefixEnd_3946844 := by exact prefixLift 3946844
  have htrace : WordTrace (prefixWord ++ tailWord_3946844) baseStart_3946844 baseEnd_3946844 := by
    simpa [prefixWord, tailWord_3946844, baseEnd_3946844] using wordTrace_append hprefix tailTrace_3946844
  have hstable : (prefixWord ++ tailWord_3946844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946844).length < 2 ^ (prefixWord ++ tailWord_3946844).sum := by decide
  have hdescent : baseEnd_3946844 < baseStart_3946844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946851 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 5, 3]
def baseStart_3946851 : Nat := 118140960795 + 3946851 * 2 ^ 59
def prefixEnd_3946851 : Nat := 4983230072969 + 3 ^ 40 * 3946851 * 2
def baseEnd_3946851 : Nat := 1351087756452428440674179

theorem tailTrace_3946851 : CollatzResearch.WordTrace tailWord_3946851 prefixEnd_3946851 1351087756452428440674179 := by
  unfold tailWord_3946851
  simp only [CollatzResearch.WordTrace]
  refine ⟨143953482224240370330576407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95968988149493580220384271 143953482224240370330576407)
  ·
    refine ⟨215930223336360555495864611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143953482224240370330576407 215930223336360555495864611)
    ·
      refine ⟨323895335004540833243796917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215930223336360555495864611 323895335004540833243796917)
      ·
        refine ⟨30365187656675703116605961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323895335004540833243796917 30365187656675703116605961)
        ·
          refine ⟨22773890742506777337454471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30365187656675703116605961 22773890742506777337454471)
          ·
            refine ⟨34160836113760166006181707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22773890742506777337454471 34160836113760166006181707)
            ·
              refine ⟨51241254170640249009272561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34160836113760166006181707 51241254170640249009272561)
              ·
                refine ⟨38430940627980186756954421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51241254170640249009272561 38430940627980186756954421)
                ·
                  refine ⟨3602900683873142508464477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38430940627980186756954421 3602900683873142508464477)
                  ·
                    refine ⟨1351087756452428440674179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3602900683873142508464477 1351087756452428440674179)
                    ·
                      rfl

theorem cell22_3946851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 3].length) (baseStart_3946851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946851 prefixEnd_3946851 := by exact prefixLift 3946851
  have htrace : WordTrace (prefixWord ++ tailWord_3946851) baseStart_3946851 baseEnd_3946851 := by
    simpa [prefixWord, tailWord_3946851, baseEnd_3946851] using wordTrace_append hprefix tailTrace_3946851
  have hstable : (prefixWord ++ tailWord_3946851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946851).length < 2 ^ (prefixWord ++ tailWord_3946851).sum := by decide
  have hdescent : baseEnd_3946851 < baseStart_3946851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946932 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 5]
def baseStart_3946932 : Nat := 118140960795 + 3946932 * 2 ^ 59
def prefixEnd_3946932 : Nat := 4983230072969 + 3 ^ 40 * 3946932 * 2
def baseEnd_3946932 : Nat := 450371828135923743132977

theorem tailTrace_3946932 : CollatzResearch.WordTrace tailWord_3946932 prefixEnd_3946932 450371828135923743132977 := by
  unfold tailWord_3946932
  simp only [CollatzResearch.WordTrace]
  refine ⟨71978218268473460582137525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95970957691297947442850033 71978218268473460582137525)
  ·
    refine ⟨6747957962669386929575393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71978218268473460582137525 6747957962669386929575393)
    ·
      refine ⟨5060968472002040197181545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6747957962669386929575393 5060968472002040197181545)
      ·
        refine ⟨3795726354001530147886159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5060968472002040197181545 3795726354001530147886159)
        ·
          refine ⟨5693589531002295221829239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795726354001530147886159 5693589531002295221829239)
          ·
            refine ⟨8540384296503442832743859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693589531002295221829239 8540384296503442832743859)
            ·
              refine ⟨12810576444755164249115789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8540384296503442832743859 12810576444755164249115789)
              ·
                refine ⟨4803966166783186593418421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12810576444755164249115789 4803966166783186593418421)
                ·
                  refine ⟨450371828135923743132977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4803966166783186593418421 450371828135923743132977)
                  ·
                    rfl

theorem cell22_3946932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_3946932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946932 prefixEnd_3946932 := by exact prefixLift 3946932
  have htrace : WordTrace (prefixWord ++ tailWord_3946932) baseStart_3946932 baseEnd_3946932 := by
    simpa [prefixWord, tailWord_3946932, baseEnd_3946932] using wordTrace_append hprefix tailTrace_3946932
  have hstable : (prefixWord ++ tailWord_3946932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946932).length < 2 ^ (prefixWord ++ tailWord_3946932).sum := by decide
  have hdescent : baseEnd_3946932 < baseStart_3946932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946973 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3946973 : Nat := 118140960795 + 3946973 * 2 ^ 59
def prefixEnd_3946973 : Nat := 4983230072969 + 3 ^ 40 * 3946973 * 2
def baseEnd_3946973 : Nat := 1351129519545660789123805

theorem tailTrace_3946973 : CollatzResearch.WordTrace tailWord_3946973 prefixEnd_3946973 1351129519545660789123805 := by
  unfold tailWord_3946973
  simp only [CollatzResearch.WordTrace]
  refine ⟨143957931929798385166517573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95971954619865590111011715 143957931929798385166517573)
  ·
    refine ⟨26992112236837197218722045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143957931929798385166517573 26992112236837197218722045)
    ·
      refine ⟨10122042088813948957020767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26992112236837197218722045 10122042088813948957020767)
      ·
        refine ⟨15183063133220923435531151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10122042088813948957020767 15183063133220923435531151)
        ·
          refine ⟨22774594699831385153296727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15183063133220923435531151 22774594699831385153296727)
          ·
            refine ⟨34161892049747077729945091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22774594699831385153296727 34161892049747077729945091)
            ·
              refine ⟨51242838074620616594917637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34161892049747077729945091 51242838074620616594917637)
              ·
                refine ⟨9608032138991365611547057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51242838074620616594917637 9608032138991365611547057)
                ·
                  refine ⟨7206024104243524208660293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9608032138991365611547057 7206024104243524208660293)
                  ·
                    refine ⟨1351129519545660789123805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7206024104243524208660293 1351129519545660789123805)
                    ·
                      rfl

theorem cell22_3946973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3946973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946973 prefixEnd_3946973 := by exact prefixLift 3946973
  have htrace : WordTrace (prefixWord ++ tailWord_3946973) baseStart_3946973 baseEnd_3946973 := by
    simpa [prefixWord, tailWord_3946973, baseEnd_3946973] using wordTrace_append hprefix tailTrace_3946973
  have hstable : (prefixWord ++ tailWord_3946973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946973).length < 2 ^ (prefixWord ++ tailWord_3946973).sum := by decide
  have hdescent : baseEnd_3946973 < baseStart_3946973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946975 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 2, 3]
def baseStart_3946975 : Nat := 118140960795 + 3946975 * 2 ^ 59
def prefixEnd_3946975 : Nat := 4983230072969 + 3 ^ 40 * 3946975 * 2
def baseEnd_3946975 : Nat := 1351130204186533450573799

theorem tailTrace_3946975 : CollatzResearch.WordTrace tailWord_3946975 prefixEnd_3946975 1351130204186533450573799 := by
  unfold tailWord_3946975
  simp only [CollatzResearch.WordTrace]
  refine ⟨143958004875791139508090379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95972003250527426338726919 143958004875791139508090379)
  ·
    refine ⟨215937007313686709262135569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143958004875791139508090379 215937007313686709262135569)
    ·
      refine ⟨161952755485265031946601677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215937007313686709262135569 161952755485265031946601677)
      ·
        refine ⟨60732283306974386979975629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161952755485265031946601677 60732283306974386979975629)
        ·
          refine ⟨22774606240115395117490861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60732283306974386979975629 22774606240115395117490861)
          ·
            refine ⟨8540477340043273169059073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22774606240115395117490861 8540477340043273169059073)
            ·
              refine ⟨6405358005032454876794305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8540477340043273169059073 6405358005032454876794305)
              ·
                refine ⟨4804018503774341157595729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6405358005032454876794305 4804018503774341157595729)
                ·
                  refine ⟨3603013877830755868196797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4804018503774341157595729 3603013877830755868196797)
                  ·
                    refine ⟨1351130204186533450573799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3603013877830755868196797 1351130204186533450573799)
                    ·
                      rfl

theorem cell22_3946975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 3].length) (baseStart_3946975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3946975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3946975 prefixEnd_3946975 := by exact prefixLift 3946975
  have htrace : WordTrace (prefixWord ++ tailWord_3946975) baseStart_3946975 baseEnd_3946975 := by
    simpa [prefixWord, tailWord_3946975, baseEnd_3946975] using wordTrace_append hprefix tailTrace_3946975
  have hstable : (prefixWord ++ tailWord_3946975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946975).length < 2 ^ (prefixWord ++ tailWord_3946975).sum := by decide
  have hdescent : baseEnd_3946975 < baseStart_3946975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947016 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 7]
def baseStart_3947016 : Nat := 118140960795 + 3947016 * 2 ^ 59
def prefixEnd_3947016 : Nat := 4983230072969 + 3 ^ 40 * 3947016 * 2
def baseEnd_3947016 : Nat := 450381413108141003432891

theorem tailTrace_3947016 : CollatzResearch.WordTrace tailWord_3947016 prefixEnd_3947016 450381413108141003432891 := by
  unfold tailWord_3947016
  simp only [CollatzResearch.WordTrace]
  refine ⟨71979750134321301755166451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95973000179095069006888601 71979750134321301755166451)
  ·
    refine ⟨107969625201481952632749677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71979750134321301755166451 107969625201481952632749677)
    ·
      refine ⟨40488609450555732237281129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107969625201481952632749677 40488609450555732237281129)
      ·
        refine ⟨30366457087916799177960847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40488609450555732237281129 30366457087916799177960847)
        ·
          refine ⟨45549685631875198766941271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30366457087916799177960847 45549685631875198766941271)
          ·
            refine ⟨68324528447812798150411907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45549685631875198766941271 68324528447812798150411907)
            ·
              refine ⟨102486792671719197225617861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68324528447812798150411907 102486792671719197225617861)
              ·
                refine ⟨19216273625947349479803349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102486792671719197225617861 19216273625947349479803349)
                ·
                  refine ⟨450381413108141003432891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19216273625947349479803349 450381413108141003432891)
                  ·
                    rfl

theorem cell22_3947016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_3947016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947016 prefixEnd_3947016 := by exact prefixLift 3947016
  have htrace : WordTrace (prefixWord ++ tailWord_3947016) baseStart_3947016 baseEnd_3947016 := by
    simpa [prefixWord, tailWord_3947016, baseEnd_3947016] using wordTrace_append hprefix tailTrace_3947016
  have hstable : (prefixWord ++ tailWord_3947016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947016).length < 2 ^ (prefixWord ++ tailWord_3947016).sum := by decide
  have hdescent : baseEnd_3947016 < baseStart_3947016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947037 : List Nat := [1, 4, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3947037 : Nat := 118140960795 + 3947037 * 2 ^ 59
def prefixEnd_3947037 : Nat := 4983230072969 + 3 ^ 40 * 3947037 * 2
def baseEnd_3947037 : Nat := 1351151428053585955523609

theorem tailTrace_3947037 : CollatzResearch.WordTrace tailWord_3947037 prefixEnd_3947037 1351151428053585955523609 := by
  unfold tailWord_3947037
  simp only [CollatzResearch.WordTrace]
  refine ⟨143960266201566524096847365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95973510801044349397898243 143960266201566524096847365)
  ·
    refine ⟨26992549912793723268158881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143960266201566524096847365 26992549912793723268158881)
    ·
      refine ⟨20244412434595292451119161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26992549912793723268158881 20244412434595292451119161)
      ·
        refine ⟨15183309325946469338339371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20244412434595292451119161 15183309325946469338339371)
        ·
          refine ⟨22774963988919704007509057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15183309325946469338339371 22774963988919704007509057)
          ·
            refine ⟨17081222991689778005631793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22774963988919704007509057 17081222991689778005631793)
            ·
              refine ⟨12810917243767333504223845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17081222991689778005631793 12810917243767333504223845)
              ·
                refine ⟨2402046983206375032041971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12810917243767333504223845 2402046983206375032041971)
                ·
                  refine ⟨3603070474809562548062957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402046983206375032041971 3603070474809562548062957)
                  ·
                    refine ⟨1351151428053585955523609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3603070474809562548062957 1351151428053585955523609)
                    ·
                      rfl

theorem cell22_3947037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3947037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947037 prefixEnd_3947037 := by exact prefixLift 3947037
  have htrace : WordTrace (prefixWord ++ tailWord_3947037) baseStart_3947037 baseEnd_3947037 := by
    simpa [prefixWord, tailWord_3947037, baseEnd_3947037] using wordTrace_append hprefix tailTrace_3947037
  have hstable : (prefixWord ++ tailWord_3947037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947037).length < 2 ^ (prefixWord ++ tailWord_3947037).sum := by decide
  have hdescent : baseEnd_3947037 < baseStart_3947037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947108 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_3947108 : Nat := 118140960795 + 3947108 * 2 ^ 59
def prefixEnd_3947108 : Nat := 4983230072969 + 3 ^ 40 * 3947108 * 2
def baseEnd_3947108 : Nat := 1351175732804565436998391

theorem tailTrace_3947108 : CollatzResearch.WordTrace tailWord_3947108 prefixEnd_3947108 1351175732804565436998391 := by
  unfold tailWord_3947108
  simp only [CollatzResearch.WordTrace]
  refine ⟨71981427892154651611340989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95975237189539535481787985 71981427892154651611340989)
  ·
    refine ⟨26993035459557994354252871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71981427892154651611340989 26993035459557994354252871)
    ·
      refine ⟨40489553189336991531379307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26993035459557994354252871 40489553189336991531379307)
      ·
        refine ⟨60734329784005487297068961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40489553189336991531379307 60734329784005487297068961)
        ·
          refine ⟨45550747338004115472801721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60734329784005487297068961 45550747338004115472801721)
          ·
            refine ⟨34163060503503086604601291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45550747338004115472801721 34163060503503086604601291)
            ·
              refine ⟨51244590755254629906901937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34163060503503086604601291 51244590755254629906901937)
              ·
                refine ⟨38433443066440972430176453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51244590755254629906901937 38433443066440972430176453)
                ·
                  refine ⟨7206270574957682330658085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38433443066440972430176453 7206270574957682330658085)
                  ·
                    refine ⟨1351175732804565436998391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7206270574957682330658085 1351175732804565436998391)
                    ·
                      rfl

theorem cell22_3947108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_3947108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947108 prefixEnd_3947108 := by exact prefixLift 3947108
  have htrace : WordTrace (prefixWord ++ tailWord_3947108) baseStart_3947108 baseEnd_3947108 := by
    simpa [prefixWord, tailWord_3947108, baseEnd_3947108] using wordTrace_append hprefix tailTrace_3947108
  have hstable : (prefixWord ++ tailWord_3947108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947108).length < 2 ^ (prefixWord ++ tailWord_3947108).sum := by decide
  have hdescent : baseEnd_3947108 < baseStart_3947108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947146 : List Nat := [3, 1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_3947146 : Nat := 118140960795 + 3947146 * 2 ^ 59
def prefixEnd_3947146 : Nat := 4983230072969 + 3 ^ 40 * 3947146 * 2
def baseEnd_3947146 : Nat := 450396246993715334849425

theorem tailTrace_3947146 : CollatzResearch.WordTrace tailWord_3947146 prefixEnd_3947146 450396246993715334849425 := by
  unfold tailWord_3947146
  simp only [CollatzResearch.WordTrace]
  refine ⟨35991060439542908928141323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95976161172114423808376861 35991060439542908928141323)
  ·
    refine ⟨53986590659314363392211985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35991060439542908928141323 53986590659314363392211985)
    ·
      refine ⟨40489942994485772544158989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53986590659314363392211985 40489942994485772544158989)
      ·
        refine ⟨15183728622932164704059621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40489942994485772544158989 15183728622932164704059621)
        ·
          refine ⟨2846949116799780882011179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15183728622932164704059621 2846949116799780882011179)
          ·
            refine ⟨4270423675199671323016769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846949116799780882011179 4270423675199671323016769)
            ·
              refine ⟨3202817756399753492262577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270423675199671323016769 3202817756399753492262577)
              ·
                refine ⟨2402113317299815119196933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202817756399753492262577 2402113317299815119196933)
                ·
                  refine ⟨450396246993715334849425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402113317299815119196933 450396246993715334849425)
                  ·
                    rfl

theorem cell22_3947146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_3947146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947146 prefixEnd_3947146 := by exact prefixLift 3947146
  have htrace : WordTrace (prefixWord ++ tailWord_3947146) baseStart_3947146 baseEnd_3947146 := by
    simpa [prefixWord, tailWord_3947146, baseEnd_3947146] using wordTrace_append hprefix tailTrace_3947146
  have hstable : (prefixWord ++ tailWord_3947146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947146).length < 2 ^ (prefixWord ++ tailWord_3947146).sum := by decide
  have hdescent : baseEnd_3947146 < baseStart_3947146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947189 : List Nat := [1, 3, 3, 3, 1, 1, 1, 5, 1, 3]
def baseStart_3947189 : Nat := 118140960795 + 3947189 * 2 ^ 59
def prefixEnd_3947189 : Nat := 4983230072969 + 3 ^ 40 * 3947189 * 2
def baseEnd_3947189 : Nat := 1351203460759908225723143

theorem tailTrace_3947189 : CollatzResearch.WordTrace tailWord_3947189 prefixEnd_3947189 1351203460759908225723143 := by
  unfold tailWord_3947189
  simp only [CollatzResearch.WordTrace]
  refine ⟨143965810097015854056380621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95977206731343902704253747 143965810097015854056380621)
  ·
    refine ⟨53987178786380945271142733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143965810097015854056380621 53987178786380945271142733)
    ·
      refine ⟨20245192044892854476678525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53987178786380945271142733 20245192044892854476678525)
      ·
        refine ⟨7591947016834820428754447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20245192044892854476678525 7591947016834820428754447)
        ·
          refine ⟨11387920525252230643131671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7591947016834820428754447 11387920525252230643131671)
          ·
            refine ⟨17081880787878345964697507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11387920525252230643131671 17081880787878345964697507)
            ·
              refine ⟨25622821181817518947046261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17081880787878345964697507 25622821181817518947046261)
              ·
                refine ⟨2402139485795392401285587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25622821181817518947046261 2402139485795392401285587)
                ·
                  refine ⟨3603209228693088601928381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402139485795392401285587 3603209228693088601928381)
                  ·
                    refine ⟨1351203460759908225723143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3603209228693088601928381 1351203460759908225723143)
                    ·
                      rfl

theorem cell22_3947189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_3947189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947189 prefixEnd_3947189 := by exact prefixLift 3947189
  have htrace : WordTrace (prefixWord ++ tailWord_3947189) baseStart_3947189 baseEnd_3947189 := by
    simpa [prefixWord, tailWord_3947189, baseEnd_3947189] using wordTrace_append hprefix tailTrace_3947189
  have hstable : (prefixWord ++ tailWord_3947189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947189).length < 2 ^ (prefixWord ++ tailWord_3947189).sum := by decide
  have hdescent : baseEnd_3947189 < baseStart_3947189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947245 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3947245 : Nat := 118140960795 + 3947245 * 2 ^ 59
def prefixEnd_3947245 : Nat := 4983230072969 + 3 ^ 40 * 3947245 * 2
def baseEnd_3947245 : Nat := 1351222630704342746322971

theorem tailTrace_3947245 : CollatzResearch.WordTrace tailWord_3947245 prefixEnd_3947245 1351222630704342746322971 := by
  unfold tailWord_3947245
  simp only [CollatzResearch.WordTrace]
  refine ⟨143967852584812975620419189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95978568389875317080279459 143967852584812975620419189)
  ·
    refine ⟨13496986179826216464414299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143967852584812975620419189 13496986179826216464414299)
    ·
      refine ⟨20245479269739324696621449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13496986179826216464414299 20245479269739324696621449)
      ·
        refine ⟨15184109452304493522466087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20245479269739324696621449 15184109452304493522466087)
        ·
          refine ⟨22776164178456740283699131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15184109452304493522466087 22776164178456740283699131)
          ·
            refine ⟨34164246267685110425548697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22776164178456740283699131 34164246267685110425548697)
            ·
              refine ⟨25623184700763832819161523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34164246267685110425548697 25623184700763832819161523)
              ·
                refine ⟨38434777051145749228742285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25623184700763832819161523 38434777051145749228742285)
                ·
                  refine ⟨14413041394179655960778357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38434777051145749228742285 14413041394179655960778357)
                  ·
                    refine ⟨1351222630704342746322971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14413041394179655960778357 1351222630704342746322971)
                    ·
                      rfl

theorem cell22_3947245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3947245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947245 prefixEnd_3947245 := by exact prefixLift 3947245
  have htrace : WordTrace (prefixWord ++ tailWord_3947245) baseStart_3947245 baseEnd_3947245 := by
    simpa [prefixWord, tailWord_3947245, baseEnd_3947245] using wordTrace_append hprefix tailTrace_3947245
  have hstable : (prefixWord ++ tailWord_3947245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947245).length < 2 ^ (prefixWord ++ tailWord_3947245).sum := by decide
  have hdescent : baseEnd_3947245 < baseStart_3947245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947247 : List Nat := [1, 1, 2, 1, 5, 2, 3, 3, 4]
def baseStart_3947247 : Nat := 118140960795 + 3947247 * 2 ^ 59
def prefixEnd_3947247 : Nat := 4983230072969 + 3 ^ 40 * 3947247 * 2
def baseEnd_3947247 : Nat := 450407771781738469257655

theorem tailTrace_3947247 : CollatzResearch.WordTrace tailWord_3947247 prefixEnd_3947247 450407771781738469257655 := by
  unfold tailWord_3947247
  simp only [CollatzResearch.WordTrace]
  refine ⟨143967925530805729961991995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95978617020537153307994663 143967925530805729961991995)
  ·
    refine ⟨215951888296208594942987993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143967925530805729961991995 215951888296208594942987993)
    ·
      refine ⟨161963916222156446207240995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215951888296208594942987993 161963916222156446207240995)
      ·
        refine ⟨242945874333234669310861493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161963916222156446207240995 242945874333234669310861493)
        ·
          refine ⟨22776175718740750247893265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242945874333234669310861493 22776175718740750247893265)
          ·
            refine ⟨17082131789055562685919949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22776175718740750247893265 17082131789055562685919949)
            ·
              refine ⟨6405799420895836007219981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17082131789055562685919949 6405799420895836007219981)
              ·
                refine ⟨2402174782835938502707493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6405799420895836007219981 2402174782835938502707493)
                ·
                  refine ⟨450407771781738469257655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402174782835938502707493 450407771781738469257655)
                  ·
                    rfl

theorem cell22_3947247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 4].length) (baseStart_3947247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947247 prefixEnd_3947247 := by exact prefixLift 3947247
  have htrace : WordTrace (prefixWord ++ tailWord_3947247) baseStart_3947247 baseEnd_3947247 := by
    simpa [prefixWord, tailWord_3947247, baseEnd_3947247] using wordTrace_append hprefix tailTrace_3947247
  have hstable : (prefixWord ++ tailWord_3947247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947247).length < 2 ^ (prefixWord ++ tailWord_3947247).sum := by decide
  have hdescent : baseEnd_3947247 < baseStart_3947247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947258 : List Nat := [3, 1, 1, 1, 1, 3, 12]
def baseStart_3947258 : Nat := 118140960795 + 3947258 * 2 ^ 59
def prefixEnd_3947258 : Nat := 4983230072969 + 3 ^ 40 * 3947258 * 2
def baseEnd_3947258 : Nat := 50045447439630186879553

theorem tailTrace_3947258 : CollatzResearch.WordTrace tailWord_3947258 prefixEnd_3947258 50045447439630186879553 := by
  unfold tailWord_3947258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35992081683441469710160607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95978884489177252560428285 35992081683441469710160607)
  ·
    refine ⟨53988122525162204565240911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35992081683441469710160607 53988122525162204565240911)
    ·
      refine ⟨80982183787743306847861367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53988122525162204565240911 80982183787743306847861367)
      ·
        refine ⟨121473275681614960271792051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80982183787743306847861367 121473275681614960271792051)
        ·
          refine ⟨182209913522422440407688077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121473275681614960271792051 182209913522422440407688077)
          ·
            refine ⟨68328717570908415152883029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182209913522422440407688077 68328717570908415152883029)
            ·
              refine ⟨50045447439630186879553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 68328717570908415152883029 50045447439630186879553)
              ·
                rfl

theorem cell22_3947258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 12].length) (baseStart_3947258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947258 prefixEnd_3947258 := by exact prefixLift 3947258
  have htrace : WordTrace (prefixWord ++ tailWord_3947258) baseStart_3947258 baseEnd_3947258 := by
    simpa [prefixWord, tailWord_3947258, baseEnd_3947258] using wordTrace_append hprefix tailTrace_3947258
  have hstable : (prefixWord ++ tailWord_3947258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947258).length < 2 ^ (prefixWord ++ tailWord_3947258).sum := by decide
  have hdescent : baseEnd_3947258 < baseStart_3947258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947260 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_3947260 : Nat := 118140960795 + 3947260 * 2 ^ 59
def prefixEnd_3947260 : Nat := 4983230072969 + 3 ^ 40 * 3947260 * 2
def baseEnd_3947260 : Nat := 1351227765510887707197925

theorem tailTrace_3947260 : CollatzResearch.WordTrace tailWord_3947260 prefixEnd_3947260 1351227765510887707197925 := by
  unfold tailWord_3947260
  simp only [CollatzResearch.WordTrace]
  refine ⟨71984199839879316591107617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95978933119839088788143489 71984199839879316591107617)
  ·
    refine ⟨53988149879909487443330713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71984199839879316591107617 53988149879909487443330713)
    ·
      refine ⟨40491112409932115582498035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53988149879909487443330713 40491112409932115582498035)
      ·
        refine ⟨60736668614898173373747053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40491112409932115582498035 60736668614898173373747053)
        ·
          refine ⟨22776250730586815015155145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60736668614898173373747053 22776250730586815015155145)
          ·
            refine ⟨17082188047940111261366359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22776250730586815015155145 17082188047940111261366359)
            ·
              refine ⟨25623282071910166892049539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17082188047940111261366359 25623282071910166892049539)
              ·
                refine ⟨38434923107865250338074309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25623282071910166892049539 38434923107865250338074309)
                ·
                  refine ⟨7206548082724734438388933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38434923107865250338074309 7206548082724734438388933)
                  ·
                    refine ⟨1351227765510887707197925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7206548082724734438388933 1351227765510887707197925)
                    ·
                      rfl

theorem cell22_3947260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_3947260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947260 prefixEnd_3947260 := by exact prefixLift 3947260
  have htrace : WordTrace (prefixWord ++ tailWord_3947260) baseStart_3947260 baseEnd_3947260 := by
    simpa [prefixWord, tailWord_3947260, baseEnd_3947260] using wordTrace_append hprefix tailTrace_3947260
  have hstable : (prefixWord ++ tailWord_3947260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947260).length < 2 ^ (prefixWord ++ tailWord_3947260).sum := by decide
  have hdescent : baseEnd_3947260 < baseStart_3947260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947309 : List Nat := [1, 5, 3, 2, 2, 9]
def baseStart_3947309 : Nat := 118140960795 + 3947309 * 2 ^ 59
def prefixEnd_3947309 : Nat := 4983230072969 + 3 ^ 40 * 3947309 * 2
def baseEnd_3947309 : Nat := 16682031348299603860775

theorem tailTrace_3947309 : CollatzResearch.WordTrace tailWord_3947309 prefixEnd_3947309 16682031348299603860775 := by
  unfold tailWord_3947309
  simp only [CollatzResearch.WordTrace]
  refine ⟨143970186856581114550748981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95980124571054076367165987 143970186856581114550748981)
  ·
    refine ⟨13497205017804479489132717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143970186856581114550748981 13497205017804479489132717)
    ·
      refine ⟨5061451881676679808424769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13497205017804479489132717 5061451881676679808424769)
      ·
        refine ⟨3796088911257509856318577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5061451881676679808424769 3796088911257509856318577)
        ·
          refine ⟨2847066683443132392238933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3796088911257509856318577 2847066683443132392238933)
          ·
            refine ⟨16682031348299603860775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2847066683443132392238933 16682031348299603860775)
            ·
              rfl

theorem cell22_3947309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 9].length) (baseStart_3947309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947309 prefixEnd_3947309 := by exact prefixLift 3947309
  have htrace : WordTrace (prefixWord ++ tailWord_3947309) baseStart_3947309 baseEnd_3947309 := by
    simpa [prefixWord, tailWord_3947309, baseEnd_3947309] using wordTrace_append hprefix tailTrace_3947309
  have hstable : (prefixWord ++ tailWord_3947309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947309).length < 2 ^ (prefixWord ++ tailWord_3947309).sum := by decide
  have hdescent : baseEnd_3947309 < baseStart_3947309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947341 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3947341 : Nat := 118140960795 + 3947341 * 2 ^ 59
def prefixEnd_3947341 : Nat := 4983230072969 + 3 ^ 40 * 3947341 * 2
def baseEnd_3947341 : Nat := 1351255493466230495922677

theorem tailTrace_3947341 : CollatzResearch.WordTrace tailWord_3947341 prefixEnd_3947341 1351255493466230495922677 := by
  unfold tailWord_3947341
  simp only [CollatzResearch.WordTrace]
  refine ⟨143971353992465184015913877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95980902661643456010609251 143971353992465184015913877)
  ·
    refine ⟨6748657218396805500745963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143971353992465184015913877 6748657218396805500745963)
    ·
      refine ⟨10122985827595208251118945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748657218396805500745963 10122985827595208251118945)
      ·
        refine ⟨7592239370696406188339209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10122985827595208251118945 7592239370696406188339209)
        ·
          refine ⟨5694179528022304641254407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7592239370696406188339209 5694179528022304641254407)
          ·
            refine ⟨8541269292033456961881611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694179528022304641254407 8541269292033456961881611)
            ·
              refine ⟨12811903938050185442822417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541269292033456961881611 12811903938050185442822417)
              ·
                refine ⟨9608927953537639082116813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12811903938050185442822417 9608927953537639082116813)
                ·
                  refine ⟨3603347982576614655793805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9608927953537639082116813 3603347982576614655793805)
                  ·
                    refine ⟨1351255493466230495922677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3603347982576614655793805 1351255493466230495922677)
                    ·
                      rfl

theorem cell22_3947341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3947341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947341 prefixEnd_3947341 := by exact prefixLift 3947341
  have htrace : WordTrace (prefixWord ++ tailWord_3947341) baseStart_3947341 baseEnd_3947341 := by
    simpa [prefixWord, tailWord_3947341, baseEnd_3947341] using wordTrace_append hprefix tailTrace_3947341
  have hstable : (prefixWord ++ tailWord_3947341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947341).length < 2 ^ (prefixWord ++ tailWord_3947341).sum := by decide
  have hdescent : baseEnd_3947341 < baseStart_3947341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947395 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 3, 6]
def baseStart_3947395 : Nat := 118140960795 + 3947395 * 2 ^ 59
def prefixEnd_3947395 : Nat := 4983230072969 + 3 ^ 40 * 3947395 * 2
def baseEnd_3947395 : Nat := 1351273978769792355072511

theorem tailTrace_3947395 : CollatzResearch.WordTrace tailWord_3947395 prefixEnd_3947395 1351273978769792355072511 := by
  unfold tailWord_3947395
  simp only [CollatzResearch.WordTrace]
  refine ⟨143973323534269551238379639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95982215689513034158919759 143973323534269551238379639)
  ·
    refine ⟨215959985301404326857569459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143973323534269551238379639 215959985301404326857569459)
    ·
      refine ⟨323939977952106490286354189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215959985301404326857569459 323939977952106490286354189)
      ·
        refine ⟨121477491732039933857382821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323939977952106490286354189 121477491732039933857382821)
        ·
          refine ⟨22777029699757487598259279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121477491732039933857382821 22777029699757487598259279)
          ·
            refine ⟨34165544549636231397388919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22777029699757487598259279 34165544549636231397388919)
            ·
              refine ⟨51248316824454347096083379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34165544549636231397388919 51248316824454347096083379)
              ·
                refine ⟨76872475236681520644125069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51248316824454347096083379 76872475236681520644125069)
                ·
                  refine ⟨28827178213755570241546901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76872475236681520644125069 28827178213755570241546901)
                  ·
                    refine ⟨1351273978769792355072511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28827178213755570241546901 1351273978769792355072511)
                    ·
                      rfl

theorem cell22_3947395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_3947395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947395 prefixEnd_3947395 := by exact prefixLift 3947395
  have htrace : WordTrace (prefixWord ++ tailWord_3947395) baseStart_3947395 baseEnd_3947395 := by
    simpa [prefixWord, tailWord_3947395, baseEnd_3947395] using wordTrace_append hprefix tailTrace_3947395
  have hstable : (prefixWord ++ tailWord_3947395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947395).length < 2 ^ (prefixWord ++ tailWord_3947395).sum := by decide
  have hdescent : baseEnd_3947395 < baseStart_3947395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947397 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_3947397 : Nat := 118140960795 + 3947397 * 2 ^ 59
def prefixEnd_3947397 : Nat := 4983230072969 + 3 ^ 40 * 3947397 * 2
def baseEnd_3947397 : Nat := 1351274663410665016522505

theorem tailTrace_3947397 : CollatzResearch.WordTrace tailWord_3947397 prefixEnd_3947397 1351274663410665016522505 := by
  unfold tailWord_3947397
  simp only [CollatzResearch.WordTrace]
  refine ⟨143973396480262305579952445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95982264320174870386634963 143973396480262305579952445)
  ·
    refine ⟨53990023680098364592482167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143973396480262305579952445 53990023680098364592482167)
    ·
      refine ⟨80985035520147546888723251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53990023680098364592482167 80985035520147546888723251)
      ·
        refine ⟨121477553280221320333084877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80985035520147546888723251 121477553280221320333084877)
        ·
          refine ⟨45554082480082995124906829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121477553280221320333084877 45554082480082995124906829)
          ·
            refine ⟨17082780930031123171840061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45554082480082995124906829 17082780930031123171840061)
            ·
              refine ⟨6406042848761671189440023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17082780930031123171840061 6406042848761671189440023)
              ·
                refine ⟨9609064273142506784160035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6406042848761671189440023 9609064273142506784160035)
                ·
                  refine ⟨14413596409713760176240053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9609064273142506784160035 14413596409713760176240053)
                  ·
                    refine ⟨1351274663410665016522505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14413596409713760176240053 1351274663410665016522505)
                    ·
                      rfl

theorem cell22_3947397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_3947397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947397 prefixEnd_3947397 := by exact prefixLift 3947397
  have htrace : WordTrace (prefixWord ++ tailWord_3947397) baseStart_3947397 baseEnd_3947397 := by
    simpa [prefixWord, tailWord_3947397, baseEnd_3947397] using wordTrace_append hprefix tailTrace_3947397
  have hstable : (prefixWord ++ tailWord_3947397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947397).length < 2 ^ (prefixWord ++ tailWord_3947397).sum := by decide
  have hdescent : baseEnd_3947397 < baseStart_3947397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947412 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3947412 : Nat := 118140960795 + 3947412 * 2 ^ 59
def prefixEnd_3947412 : Nat := 4983230072969 + 3 ^ 40 * 3947412 * 2
def baseEnd_3947412 : Nat := 1351279798217209977397459

theorem tailTrace_3947412 : CollatzResearch.WordTrace tailWord_3947412 prefixEnd_3947412 1351279798217209977397459 := by
  unfold tailWord_3947412
  simp only [CollatzResearch.WordTrace]
  refine ⟨71986971787603981570874245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95982629050138642094498993 71986971787603981570874245)
  ·
    refine ⟨13497557210175746544538921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71986971787603981570874245 13497557210175746544538921)
    ·
      refine ⟨10123167907631809908404191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13497557210175746544538921 10123167907631809908404191)
      ·
        refine ⟨15184751861447714862606287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10123167907631809908404191 15184751861447714862606287)
        ·
          refine ⟨22777127792171572293909431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15184751861447714862606287 22777127792171572293909431)
          ·
            refine ⟨34165691688257358440864147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22777127792171572293909431 34165691688257358440864147)
            ·
              refine ⟨51248537532386037661296221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34165691688257358440864147 51248537532386037661296221)
              ·
                refine ⟨19218201574644764122986083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51248537532386037661296221 19218201574644764122986083)
                ·
                  refine ⟨28827302361967146184479125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19218201574644764122986083 28827302361967146184479125)
                  ·
                    refine ⟨1351279798217209977397459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28827302361967146184479125 1351279798217209977397459)
                    ·
                      rfl

theorem cell22_3947412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3947412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947412 prefixEnd_3947412 := by exact prefixLift 3947412
  have htrace : WordTrace (prefixWord ++ tailWord_3947412) baseStart_3947412 baseEnd_3947412 := by
    simpa [prefixWord, tailWord_3947412, baseEnd_3947412] using wordTrace_append hprefix tailTrace_3947412
  have hstable : (prefixWord ++ tailWord_3947412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947412).length < 2 ^ (prefixWord ++ tailWord_3947412).sum := by decide
  have hdescent : baseEnd_3947412 < baseStart_3947412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947444 : List Nat := [2, 5, 2, 1, 1, 1, 1, 9]
def baseStart_3947444 : Nat := 118140960795 + 3947444 * 2 ^ 59
def prefixEnd_3947444 : Nat := 4983230072969 + 3 ^ 40 * 3947444 * 2
def baseEnd_3947444 : Nat := 150143416941241395621929

theorem tailTrace_3947444 : CollatzResearch.WordTrace tailWord_3947444 prefixEnd_3947444 150143416941241395621929 := by
  unfold tailWord_3947444
  simp only [CollatzResearch.WordTrace]
  refine ⟨71987555355546016303456693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95983407140728021737942257 71987555355546016303456693)
  ·
    refine ⟨6748833314582439028449065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71987555355546016303456693 6748833314582439028449065)
    ·
      refine ⟨5061624985936829271336799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6748833314582439028449065 5061624985936829271336799)
      ·
        refine ⟨7592437478905243907005199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061624985936829271336799 7592437478905243907005199)
        ·
          refine ⟨11388656218357865860507799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7592437478905243907005199 11388656218357865860507799)
          ·
            refine ⟨17082984327536798790761699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11388656218357865860507799 17082984327536798790761699)
            ·
              refine ⟨25624476491305198186142549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17082984327536798790761699 25624476491305198186142549)
              ·
                refine ⟨150143416941241395621929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25624476491305198186142549 150143416941241395621929)
                ·
                  rfl

theorem cell22_3947444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 9].length) (baseStart_3947444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947444 prefixEnd_3947444 := by exact prefixLift 3947444
  have htrace : WordTrace (prefixWord ++ tailWord_3947444) baseStart_3947444 baseEnd_3947444 := by
    simpa [prefixWord, tailWord_3947444, baseEnd_3947444] using wordTrace_append hprefix tailTrace_3947444
  have hstable : (prefixWord ++ tailWord_3947444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947444).length < 2 ^ (prefixWord ++ tailWord_3947444).sum := by decide
  have hdescent : baseEnd_3947444 < baseStart_3947444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947455 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 9]
def baseStart_3947455 : Nat := 118140960795 + 3947455 * 2 ^ 59
def prefixEnd_3947455 : Nat := 4983230072969 + 3 ^ 40 * 3947455 * 2
def baseEnd_3947455 : Nat := 450431505998657399524109

theorem tailTrace_3947455 : CollatzResearch.WordTrace tailWord_3947455 prefixEnd_3947455 450431505998657399524109 := by
  unfold tailWord_3947455
  simp only [CollatzResearch.WordTrace]
  refine ⟨143975511914052181485563819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95983674609368120990375879 143975511914052181485563819)
  ·
    refine ⟨215963267871078272228345729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143975511914052181485563819 215963267871078272228345729)
    ·
      refine ⟨161972450903308704171259297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215963267871078272228345729 161972450903308704171259297)
      ·
        refine ⟨121479338177481528128444473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161972450903308704171259297 121479338177481528128444473)
        ·
          refine ⟨91109503633111146096333355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121479338177481528128444473 91109503633111146096333355)
          ·
            refine ⟨136664255449666719144500033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91109503633111146096333355 136664255449666719144500033)
            ·
              refine ⟨102498191587250039358375025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136664255449666719144500033 102498191587250039358375025)
              ·
                refine ⟨76873643690437529518781269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102498191587250039358375025 76873643690437529518781269)
                ·
                  refine ⟨450431505998657399524109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76873643690437529518781269 450431505998657399524109)
                  ·
                    rfl

theorem cell22_3947455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 9].length) (baseStart_3947455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947455 prefixEnd_3947455 := by exact prefixLift 3947455
  have htrace : WordTrace (prefixWord ++ tailWord_3947455) baseStart_3947455 baseEnd_3947455 := by
    simpa [prefixWord, tailWord_3947455, baseEnd_3947455] using wordTrace_append hprefix tailTrace_3947455
  have hstable : (prefixWord ++ tailWord_3947455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947455).length < 2 ^ (prefixWord ++ tailWord_3947455).sum := by decide
  have hdescent : baseEnd_3947455 < baseStart_3947455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947585 : List Nat := [1, 2, 5, 1, 4, 1, 1, 3, 4]
def baseStart_3947585 : Nat := 118140960795 + 3947585 * 2 ^ 59
def prefixEnd_3947585 : Nat := 4983230072969 + 3 ^ 40 * 3947585 * 2
def baseEnd_3947585 : Nat := 450446339884231730940643

theorem tailTrace_3947585 : CollatzResearch.WordTrace tailWord_3947585 prefixEnd_3947585 450446339884231730940643 := by
  unfold tailWord_3947585
  simp only [CollatzResearch.WordTrace]
  refine ⟨143980253403581213687796209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95986835602387475791864139 143980253403581213687796209)
  ·
    refine ⟨107985190052685910265847157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143980253403581213687796209 107985190052685910265847157)
    ·
      refine ⟨10123611567439304087423171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107985190052685910265847157 10123611567439304087423171)
      ·
        refine ⟨15185417351158956131134757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10123611567439304087423171 15185417351158956131134757)
        ·
          refine ⟨2847265753342304274587767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15185417351158956131134757 2847265753342304274587767)
          ·
            refine ⟨4270898630013456411881651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847265753342304274587767 4270898630013456411881651)
            ·
              refine ⟨6406347945020184617822477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4270898630013456411881651 6406347945020184617822477)
              ·
                refine ⟨2402380479382569231683429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6406347945020184617822477 2402380479382569231683429)
                ·
                  refine ⟨450446339884231730940643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402380479382569231683429 450446339884231730940643)
                  ·
                    rfl

theorem cell22_3947585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 4].length) (baseStart_3947585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947585 prefixEnd_3947585 := by exact prefixLift 3947585
  have htrace : WordTrace (prefixWord ++ tailWord_3947585) baseStart_3947585 baseEnd_3947585 := by
    simpa [prefixWord, tailWord_3947585, baseEnd_3947585] using wordTrace_append hprefix tailTrace_3947585
  have hstable : (prefixWord ++ tailWord_3947585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947585).length < 2 ^ (prefixWord ++ tailWord_3947585).sum := by decide
  have hdescent : baseEnd_3947585 < baseStart_3947585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947594 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 5, 3]
def baseStart_3947594 : Nat := 118140960795 + 3947594 * 2 ^ 59
def prefixEnd_3947594 : Nat := 4983230072969 + 3 ^ 40 * 3947594 * 2
def baseEnd_3947594 : Nat := 1351342100536622169346901

theorem tailTrace_3947594 : CollatzResearch.WordTrace tailWord_3947594 prefixEnd_3947594 1351342100536622169346901 := by
  unfold tailWord_3947594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35995145415137152056218459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95987054440365738816582557 35995145415137152056218459)
  ·
    refine ⟨53992718122705728084327689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35995145415137152056218459 53992718122705728084327689)
    ·
      refine ⟨40494538592029296063245767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53992718122705728084327689 40494538592029296063245767)
      ·
        refine ⟨60741807888043944094868651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40494538592029296063245767 60741807888043944094868651)
        ·
          refine ⟨91112711832065916142302977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60741807888043944094868651 91112711832065916142302977)
          ·
            refine ⟨68334533874049437106727233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91112711832065916142302977 68334533874049437106727233)
            ·
              refine ⟨51250900405537077830045425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68334533874049437106727233 51250900405537077830045425)
              ·
                refine ⟨38438175304152808372534069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51250900405537077830045425 38438175304152808372534069)
                ·
                  refine ⟨3603578934764325784925069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38438175304152808372534069 3603578934764325784925069)
                  ·
                    refine ⟨1351342100536622169346901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3603578934764325784925069 1351342100536622169346901)
                    ·
                      rfl

theorem cell22_3947594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_3947594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947594 prefixEnd_3947594 := by exact prefixLift 3947594
  have htrace : WordTrace (prefixWord ++ tailWord_3947594) baseStart_3947594 baseEnd_3947594 := by
    simpa [prefixWord, tailWord_3947594, baseEnd_3947594] using wordTrace_append hprefix tailTrace_3947594
  have hstable : (prefixWord ++ tailWord_3947594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947594).length < 2 ^ (prefixWord ++ tailWord_3947594).sum := by decide
  have hdescent : baseEnd_3947594 < baseStart_3947594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947662 : List Nat := [4, 1, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_3947662 : Nat := 118140960795 + 3947662 * 2 ^ 59
def prefixEnd_3947662 : Nat := 4983230072969 + 3 ^ 40 * 3947662 * 2
def baseEnd_3947662 : Nat := 1351365378326292658646693

theorem tailTrace_3947662 : CollatzResearch.WordTrace tailWord_3947662 prefixEnd_3947662 1351365378326292658646693 := by
  unfold tailWord_3947662
  simp only [CollatzResearch.WordTrace]
  refine ⟨17997882728037781979793655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95988707882868170558899493 17997882728037781979793655)
  ·
    refine ⟨26996824092056672969690483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17997882728037781979793655 26996824092056672969690483)
    ·
      refine ⟨40495236138085009454535725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26996824092056672969690483 40495236138085009454535725)
      ·
        refine ⟨15185713551781878545450897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40495236138085009454535725 15185713551781878545450897)
        ·
          refine ⟨11389285163836408909088173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15185713551781878545450897 11389285163836408909088173)
          ·
            refine ⟨4270981936438653340908065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11389285163836408909088173 4270981936438653340908065)
            ·
              refine ⟨3203236452328990005681049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270981936438653340908065 3203236452328990005681049)
              ·
                refine ⟨2402427339246742504260787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203236452328990005681049 2402427339246742504260787)
                ·
                  refine ⟨3603641008870113756391181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402427339246742504260787 3603641008870113756391181)
                  ·
                    refine ⟨1351365378326292658646693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3603641008870113756391181 1351365378326292658646693)
                    ·
                      rfl

theorem cell22_3947662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_3947662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947662 prefixEnd_3947662 := by exact prefixLift 3947662
  have htrace : WordTrace (prefixWord ++ tailWord_3947662) baseStart_3947662 baseEnd_3947662 := by
    simpa [prefixWord, tailWord_3947662, baseEnd_3947662] using wordTrace_append hprefix tailTrace_3947662
  have hstable : (prefixWord ++ tailWord_3947662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947662).length < 2 ^ (prefixWord ++ tailWord_3947662).sum := by decide
  have hdescent : baseEnd_3947662 < baseStart_3947662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947780 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_3947780 : Nat := 118140960795 + 3947780 * 2 ^ 59
def prefixEnd_3947780 : Nat := 4983230072969 + 3 ^ 40 * 3947780 * 2
def baseEnd_3947780 : Nat := 1351405772137779684196331

theorem tailTrace_3947780 : CollatzResearch.WordTrace tailWord_3947780 prefixEnd_3947780 1351405772137779684196331 := by
  unfold tailWord_3947780
  simp only [CollatzResearch.WordTrace]
  refine ⟨71993682818937380995572397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95991577091916507994096529 71993682818937380995572397)
  ·
    refine ⟨26997631057101517873339649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71993682818937380995572397 26997631057101517873339649)
    ·
      refine ⟨20248223292826138405004737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26997631057101517873339649 20248223292826138405004737)
      ·
        refine ⟨15186167469619603803753553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20248223292826138405004737 15186167469619603803753553)
        ·
          refine ⟨11389625602214702852815165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15186167469619603803753553 11389625602214702852815165)
          ·
            refine ⟨4271109600830513569805687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11389625602214702852815165 4271109600830513569805687)
            ·
              refine ⟨6406664401245770354708531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271109600830513569805687 6406664401245770354708531)
              ·
                refine ⟨9609996601868655532062797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6406664401245770354708531 9609996601868655532062797)
                ·
                  refine ⟨3603748725700745824523549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9609996601868655532062797 3603748725700745824523549)
                  ·
                    refine ⟨1351405772137779684196331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3603748725700745824523549 1351405772137779684196331)
                    ·
                      rfl

theorem cell22_3947780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_3947780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3947780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3947780 prefixEnd_3947780 := by exact prefixLift 3947780
  have htrace : WordTrace (prefixWord ++ tailWord_3947780) baseStart_3947780 baseEnd_3947780 := by
    simpa [prefixWord, tailWord_3947780, baseEnd_3947780] using wordTrace_append hprefix tailTrace_3947780
  have hstable : (prefixWord ++ tailWord_3947780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947780).length < 2 ^ (prefixWord ++ tailWord_3947780).sum := by decide
  have hdescent : baseEnd_3947780 < baseStart_3947780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948001 : List Nat := [1, 2, 3, 1, 2, 13]
def baseStart_3948001 : Nat := 118140960795 + 3948001 * 2 ^ 59
def prefixEnd_3948001 : Nat := 4983230072969 + 3 ^ 40 * 3948001 * 2
def baseEnd_3948001 : Nat := 16684955863632207091613

theorem tailTrace_3948001 : CollatzResearch.WordTrace tailWord_3948001 prefixEnd_3948001 16684955863632207091613 := by
  unfold tailWord_3948001
  simp only [CollatzResearch.WordTrace]
  refine ⟨143995426170074116734939857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95996950780049411156626571 143995426170074116734939857)
  ·
    refine ⟨107996569627555587551204893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143995426170074116734939857 107996569627555587551204893)
    ·
      refine ⟨40498713610333345331701835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107996569627555587551204893 40498713610333345331701835)
      ·
        refine ⟨60748070415500017997552753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40498713610333345331701835 60748070415500017997552753)
        ·
          refine ⟨45561052811625013498164565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60748070415500017997552753 45561052811625013498164565)
          ·
            refine ⟨16684955863632207091613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 45561052811625013498164565 16684955863632207091613)
            ·
              rfl

theorem cell22_3948001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 13].length) (baseStart_3948001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948001 prefixEnd_3948001 := by exact prefixLift 3948001
  have htrace : WordTrace (prefixWord ++ tailWord_3948001) baseStart_3948001 baseEnd_3948001 := by
    simpa [prefixWord, tailWord_3948001, baseEnd_3948001] using wordTrace_append hprefix tailTrace_3948001
  have hstable : (prefixWord ++ tailWord_3948001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948001).length < 2 ^ (prefixWord ++ tailWord_3948001).sum := by decide
  have hdescent : baseEnd_3948001 < baseStart_3948001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948007 : List Nat := [1, 1, 5, 2, 1, 2, 4, 2, 4]
def baseStart_3948007 : Nat := 118140960795 + 3948007 * 2 ^ 59
def prefixEnd_3948007 : Nat := 4983230072969 + 3 ^ 40 * 3948007 * 2
def baseEnd_3948007 : Nat := 450494492958942252923545

theorem tailTrace_3948007 : CollatzResearch.WordTrace tailWord_3948007 prefixEnd_3948007 450494492958942252923545 := by
  unfold tailWord_3948007
  simp only [CollatzResearch.WordTrace]
  refine ⟨143995645008052379759658275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95997096672034919839772183 143995645008052379759658275)
  ·
    refine ⟨215993467512078569639487413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143995645008052379759658275 215993467512078569639487413)
    ·
      refine ⟨20249387579257365903701945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215993467512078569639487413 20249387579257365903701945)
      ·
        refine ⟨15187040684443024427776459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20249387579257365903701945 15187040684443024427776459)
        ·
          refine ⟨22780561026664536641664689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15187040684443024427776459 22780561026664536641664689)
          ·
            refine ⟨17085420769998402481248517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22780561026664536641664689 17085420769998402481248517)
            ·
              refine ⟨3203516394374700465234097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17085420769998402481248517 3203516394374700465234097)
              ·
                refine ⟨2402637295781025348925573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203516394374700465234097 2402637295781025348925573)
                ·
                  refine ⟨450494492958942252923545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402637295781025348925573 450494492958942252923545)
                  ·
                    rfl

theorem cell22_3948007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 4].length) (baseStart_3948007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948007 prefixEnd_3948007 := by exact prefixLift 3948007
  have htrace : WordTrace (prefixWord ++ tailWord_3948007) baseStart_3948007 baseEnd_3948007 := by
    simpa [prefixWord, tailWord_3948007, baseEnd_3948007] using wordTrace_append hprefix tailTrace_3948007
  have hstable : (prefixWord ++ tailWord_3948007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948007).length < 2 ^ (prefixWord ++ tailWord_3948007).sum := by decide
  have hdescent : baseEnd_3948007 < baseStart_3948007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948022 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_3948022 : Nat := 118140960795 + 3948022 * 2 ^ 59
def prefixEnd_3948022 : Nat := 4983230072969 + 3 ^ 40 * 3948022 * 2
def baseEnd_3948022 : Nat := 1351488613683371719645589

theorem tailTrace_3948022 : CollatzResearch.WordTrace tailWord_3948022 prefixEnd_3948022 1351488613683371719645589 := by
  unfold tailWord_3948022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999762006437377332590895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95997461401998691547636213 8999762006437377332590895)
  ·
    refine ⟨13499643009656065998886343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8999762006437377332590895 13499643009656065998886343)
    ·
      refine ⟨20249464514484098998329515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13499643009656065998886343 20249464514484098998329515)
      ·
        refine ⟨30374196771726148497494273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20249464514484098998329515 30374196771726148497494273)
        ·
          refine ⟨22780647578794611373120705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30374196771726148497494273 22780647578794611373120705)
          ·
            refine ⟨17085485684095958529840529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22780647578794611373120705 17085485684095958529840529)
            ·
              refine ⟨12814114263071968897380397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17085485684095958529840529 12814114263071968897380397)
              ·
                refine ⟨4805292848651988336517649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12814114263071968897380397 4805292848651988336517649)
                ·
                  refine ⟨3603969636488991252388237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4805292848651988336517649 3603969636488991252388237)
                  ·
                    refine ⟨1351488613683371719645589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3603969636488991252388237 1351488613683371719645589)
                    ·
                      rfl

theorem cell22_3948022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_3948022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948022 prefixEnd_3948022 := by exact prefixLift 3948022
  have htrace : WordTrace (prefixWord ++ tailWord_3948022) baseStart_3948022 baseEnd_3948022 := by
    simpa [prefixWord, tailWord_3948022, baseEnd_3948022] using wordTrace_append hprefix tailTrace_3948022
  have hstable : (prefixWord ++ tailWord_3948022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948022).length < 2 ^ (prefixWord ++ tailWord_3948022).sum := by decide
  have hdescent : baseEnd_3948022 < baseStart_3948022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948067 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 3, 3]
def baseStart_3948067 : Nat := 118140960795 + 3948067 * 2 ^ 59
def prefixEnd_3948067 : Nat := 4983230072969 + 3 ^ 40 * 3948067 * 2
def baseEnd_3948067 : Nat := 1351504018103006602270451

theorem tailTrace_3948067 : CollatzResearch.WordTrace tailWord_3948067 prefixEnd_3948067 1351504018103006602270451 := by
  unfold tailWord_3948067
  simp only [CollatzResearch.WordTrace]
  refine ⟨143997833387835010006842455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95998555591890006671228303 143997833387835010006842455)
  ·
    refine ⟨215996750081752515010263683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143997833387835010006842455 215996750081752515010263683)
    ·
      refine ⟨323995125122628772515395525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215996750081752515010263683 323995125122628772515395525)
      ·
        refine ⟨60749085960492894846636661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323995125122628772515395525 60749085960492894846636661)
        ·
          refine ⟨5695226808796208891872187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60749085960492894846636661 5695226808796208891872187)
          ·
            refine ⟨8542840213194313337808281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5695226808796208891872187 8542840213194313337808281)
            ·
              refine ⟨6407130159895735003356211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8542840213194313337808281 6407130159895735003356211)
              ·
                refine ⟨9610695239843602505034317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6407130159895735003356211 9610695239843602505034317)
                ·
                  refine ⟨3604010714941350939387869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9610695239843602505034317 3604010714941350939387869)
                  ·
                    refine ⟨1351504018103006602270451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604010714941350939387869 1351504018103006602270451)
                    ·
                      rfl

theorem cell22_3948067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 3].length) (baseStart_3948067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948067 prefixEnd_3948067 := by exact prefixLift 3948067
  have htrace : WordTrace (prefixWord ++ tailWord_3948067) baseStart_3948067 baseEnd_3948067 := by
    simpa [prefixWord, tailWord_3948067, baseEnd_3948067] using wordTrace_append hprefix tailTrace_3948067
  have hstable : (prefixWord ++ tailWord_3948067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948067).length < 2 ^ (prefixWord ++ tailWord_3948067).sum := by decide
  have hdescent : baseEnd_3948067 < baseStart_3948067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948118 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3948118 : Nat := 118140960795 + 3948118 * 2 ^ 59
def prefixEnd_3948118 : Nat := 4983230072969 + 3 ^ 40 * 3948118 * 2
def baseEnd_3948118 : Nat := 1351521476445259469245295

theorem tailTrace_3948118 : CollatzResearch.WordTrace tailWord_3948118 prefixEnd_3948118 1351521476445259469245295 := by
  unfold tailWord_3948118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999980844415640357309313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95999795673766830477966005 8999980844415640357309313)
  ·
    refine ⟨6749985633311730267981985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8999980844415640357309313 6749985633311730267981985)
    ·
      refine ⟨5062489224983797700986489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6749985633311730267981985 5062489224983797700986489)
      ·
        refine ⟨3796866918737848275739867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5062489224983797700986489 3796866918737848275739867)
        ·
          refine ⟨5695300378106772413609801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3796866918737848275739867 5695300378106772413609801)
          ·
            refine ⟨4271475283580079310207351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5695300378106772413609801 4271475283580079310207351)
            ·
              refine ⟨6407212925370118965311027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271475283580079310207351 6407212925370118965311027)
              ·
                refine ⟨9610819388055178447966541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6407212925370118965311027 9610819388055178447966541)
                ·
                  refine ⟨3604057270520691917987453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9610819388055178447966541 3604057270520691917987453)
                  ·
                    refine ⟨1351521476445259469245295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604057270520691917987453 1351521476445259469245295)
                    ·
                      rfl

theorem cell22_3948118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3948118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948118 prefixEnd_3948118 := by exact prefixLift 3948118
  have htrace : WordTrace (prefixWord ++ tailWord_3948118) baseStart_3948118 baseEnd_3948118 := by
    simpa [prefixWord, tailWord_3948118, baseEnd_3948118] using wordTrace_append hprefix tailTrace_3948118
  have hstable : (prefixWord ++ tailWord_3948118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948118).length < 2 ^ (prefixWord ++ tailWord_3948118).sum := by decide
  have hdescent : baseEnd_3948118 < baseStart_3948118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948153 : List Nat := [1, 2, 1, 3, 3, 1, 1, 10]
def baseStart_3948153 : Nat := 118140960795 + 3948153 * 2 ^ 59
def prefixEnd_3948153 : Nat := 4983230072969 + 3 ^ 40 * 3948153 * 2
def baseEnd_3948153 : Nat := 150170384184503449402243

theorem tailTrace_3948153 : CollatzResearch.WordTrace tailWord_3948153 prefixEnd_3948153 150170384184503449402243 := by
  unfold tailWord_3948153
  simp only [CollatzResearch.WordTrace]
  refine ⟨144000970065523446694473113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96000646710348964462982075 144000970065523446694473113)
  ·
    refine ⟨108000727549142585020854835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144000970065523446694473113 108000727549142585020854835)
    ·
      refine ⟨162001091323713877531282253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108000727549142585020854835 162001091323713877531282253)
      ·
        refine ⟨60750409246392704074230845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162001091323713877531282253 60750409246392704074230845)
        ·
          refine ⟨22781403467397264027836567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60750409246392704074230845 22781403467397264027836567)
          ·
            refine ⟨34172105201095896041754851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22781403467397264027836567 34172105201095896041754851)
            ·
              refine ⟨51258157801643844062632277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34172105201095896041754851 51258157801643844062632277)
              ·
                refine ⟨150170384184503449402243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51258157801643844062632277 150170384184503449402243)
                ·
                  rfl

theorem cell22_3948153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 10].length) (baseStart_3948153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948153 prefixEnd_3948153 := by exact prefixLift 3948153
  have htrace : WordTrace (prefixWord ++ tailWord_3948153) baseStart_3948153 baseEnd_3948153 := by
    simpa [prefixWord, tailWord_3948153, baseEnd_3948153] using wordTrace_append hprefix tailTrace_3948153
  have hstable : (prefixWord ++ tailWord_3948153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948153).length < 2 ^ (prefixWord ++ tailWord_3948153).sum := by decide
  have hdescent : baseEnd_3948153 < baseStart_3948153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948155 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 2, 4]
def baseStart_3948155 : Nat := 118140960795 + 3948155 * 2 ^ 59
def prefixEnd_3948155 : Nat := 4983230072969 + 3 ^ 40 * 3948155 * 2
def baseEnd_3948155 : Nat := 1351534142301403706070181

theorem tailTrace_3948155 : CollatzResearch.WordTrace tailWord_3948155 prefixEnd_3948155 1351534142301403706070181 := by
  unfold tailWord_3948155
  simp only [CollatzResearch.WordTrace]
  refine ⟨144001043011516201036045919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96000695341010800690697279 144001043011516201036045919)
  ·
    refine ⟨216001564517274301554068879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144001043011516201036045919 216001564517274301554068879)
    ·
      refine ⟨324002346775911452331103319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216001564517274301554068879 324002346775911452331103319)
      ·
        refine ⟨486003520163867178496654979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324002346775911452331103319 486003520163867178496654979)
        ·
          refine ⟨729005280245800767744982469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486003520163867178496654979 729005280245800767744982469)
          ·
            refine ⟨136688490046087643952184213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 729005280245800767744982469 136688490046087643952184213)
            ·
              refine ⟨6407272970910358310258635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136688490046087643952184213 6407272970910358310258635)
              ·
                refine ⟨9610909456365537465387953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6407272970910358310258635 9610909456365537465387953)
                ·
                  refine ⟨7208182092274153099040965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9610909456365537465387953 7208182092274153099040965)
                  ·
                    refine ⟨1351534142301403706070181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7208182092274153099040965 1351534142301403706070181)
                    ·
                      rfl

theorem cell22_3948155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 4].length) (baseStart_3948155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948155 prefixEnd_3948155 := by exact prefixLift 3948155
  have htrace : WordTrace (prefixWord ++ tailWord_3948155) baseStart_3948155 baseEnd_3948155 := by
    simpa [prefixWord, tailWord_3948155, baseEnd_3948155] using wordTrace_append hprefix tailTrace_3948155
  have hstable : (prefixWord ++ tailWord_3948155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948155).length < 2 ^ (prefixWord ++ tailWord_3948155).sum := by decide
  have hdescent : baseEnd_3948155 < baseStart_3948155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948174 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_3948174 : Nat := 118140960795 + 3948174 * 2 ^ 59
def prefixEnd_3948174 : Nat := 4983230072969 + 3 ^ 40 * 3948174 * 2
def baseEnd_3948174 : Nat := 1351540646389693989845123

theorem tailTrace_3948174 : CollatzResearch.WordTrace tailWord_3948174 prefixEnd_3948174 1351540646389693989845123 := by
  unfold tailWord_3948174
  simp only [CollatzResearch.WordTrace]
  refine ⟨18000216999805920910123447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96001157332298244853991717 18000216999805920910123447)
  ·
    refine ⟨27000325499708881365185171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18000216999805920910123447 27000325499708881365185171)
    ·
      refine ⟨40500488249563322047777757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27000325499708881365185171 40500488249563322047777757)
      ·
        refine ⟨15187683093586245767916659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40500488249563322047777757 15187683093586245767916659)
        ·
          refine ⟨22781524640379368651874989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15187683093586245767916659 22781524640379368651874989)
          ·
            refine ⟨8543071740142263244453121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22781524640379368651874989 8543071740142263244453121)
            ·
              refine ⟨6407303805106697433339841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8543071740142263244453121 6407303805106697433339841)
              ·
                refine ⟨4805477853830023075004881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6407303805106697433339841 4805477853830023075004881)
                ·
                  refine ⟨3604108390372517306253661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4805477853830023075004881 3604108390372517306253661)
                  ·
                    refine ⟨1351540646389693989845123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604108390372517306253661 1351540646389693989845123)
                    ·
                      rfl

theorem cell22_3948174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_3948174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948174 prefixEnd_3948174 := by exact prefixLift 3948174
  have htrace : WordTrace (prefixWord ++ tailWord_3948174) baseStart_3948174 baseEnd_3948174 := by
    simpa [prefixWord, tailWord_3948174, baseEnd_3948174] using wordTrace_append hprefix tailTrace_3948174
  have hstable : (prefixWord ++ tailWord_3948174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948174).length < 2 ^ (prefixWord ++ tailWord_3948174).sum := by decide
  have hdescent : baseEnd_3948174 < baseStart_3948174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948206 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3948206 : Nat := 118140960795 + 3948206 * 2 ^ 59
def prefixEnd_3948206 : Nat := 4983230072969 + 3 ^ 40 * 3948206 * 2
def baseEnd_3948206 : Nat := 1351551600643656573045025

theorem tailTrace_3948206 : CollatzResearch.WordTrace tailWord_3948206 prefixEnd_3948206 1351551600643656573045025 := by
  unfold tailWord_3948206
  simp only [CollatzResearch.WordTrace]
  refine ⟨18000362891791429593269059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96001935422887624497434981 18000362891791429593269059)
  ·
    refine ⟨27000544337687144389903589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18000362891791429593269059 27000544337687144389903589)
    ·
      refine ⟨5062602063316339573106923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27000544337687144389903589 5062602063316339573106923)
      ·
        refine ⟨7593903094974509359660385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5062602063316339573106923 7593903094974509359660385)
        ·
          refine ⟨5695427321230882019745289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7593903094974509359660385 5695427321230882019745289)
          ·
            refine ⟨4271570490923161514808967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5695427321230882019745289 4271570490923161514808967)
            ·
              refine ⟨6407355736384742272213451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271570490923161514808967 6407355736384742272213451)
              ·
                refine ⟨9611033604577113408320177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6407355736384742272213451 9611033604577113408320177)
                ·
                  refine ⟨7208275203432835056240133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9611033604577113408320177 7208275203432835056240133)
                  ·
                    refine ⟨1351551600643656573045025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7208275203432835056240133 1351551600643656573045025)
                    ·
                      rfl

theorem cell22_3948206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3948206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948206 prefixEnd_3948206 := by exact prefixLift 3948206
  have htrace : WordTrace (prefixWord ++ tailWord_3948206) baseStart_3948206 baseEnd_3948206 := by
    simpa [prefixWord, tailWord_3948206, baseEnd_3948206] using wordTrace_append hprefix tailTrace_3948206
  have hstable : (prefixWord ++ tailWord_3948206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948206).length < 2 ^ (prefixWord ++ tailWord_3948206).sum := by decide
  have hdescent : baseEnd_3948206 < baseStart_3948206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948260 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 6]
def baseStart_3948260 : Nat := 118140960795 + 3948260 * 2 ^ 59
def prefixEnd_3948260 : Nat := 4983230072969 + 3 ^ 40 * 3948260 * 2
def baseEnd_3948260 : Nat := 450523361982406144064953

theorem tailTrace_3948260 : CollatzResearch.WordTrace tailWord_3948260 prefixEnd_3948260 450523361982406144064953 := by
  unfold tailWord_3948260
  simp only [CollatzResearch.WordTrace]
  refine ⟨72002436338067901984309117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96003248450757202645745489 72002436338067901984309117)
  ·
    refine ⟨27000913626775463244115919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72002436338067901984309117 27000913626775463244115919)
    ·
      refine ⟨40501370440163194866173879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27000913626775463244115919 40501370440163194866173879)
      ·
        refine ⟨60752055660244792299260819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40501370440163194866173879 60752055660244792299260819)
        ·
          refine ⟨91128083490367188448891229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60752055660244792299260819 91128083490367188448891229)
          ·
            refine ⟨34173031308887695668334211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91128083490367188448891229 34173031308887695668334211)
            ·
              refine ⟨51259546963331543502501317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34173031308887695668334211 51259546963331543502501317)
              ·
                refine ⟨9611165055624664406718997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51259546963331543502501317 9611165055624664406718997)
                ·
                  refine ⟨450523361982406144064953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9611165055624664406718997 450523361982406144064953)
                  ·
                    rfl

theorem cell22_3948260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_3948260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948260 prefixEnd_3948260 := by exact prefixLift 3948260
  have htrace : WordTrace (prefixWord ++ tailWord_3948260) baseStart_3948260 baseEnd_3948260 := by
    simpa [prefixWord, tailWord_3948260, baseEnd_3948260] using wordTrace_append hprefix tailTrace_3948260
  have hstable : (prefixWord ++ tailWord_3948260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948260).length < 2 ^ (prefixWord ++ tailWord_3948260).sum := by decide
  have hdescent : baseEnd_3948260 < baseStart_3948260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948275 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 1, 5]
def baseStart_3948275 : Nat := 118140960795 + 3948275 * 2 ^ 59
def prefixEnd_3948275 : Nat := 4983230072969 + 3 ^ 40 * 3948275 * 2
def baseEnd_3948275 : Nat := 1351575220753763393069813

theorem tailTrace_3948275 : CollatzResearch.WordTrace tailWord_3948275 prefixEnd_3948275 1351575220753763393069813 := by
  unfold tailWord_3948275
  simp only [CollatzResearch.WordTrace]
  refine ⟨144005419771081461530414279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96003613180720974353609519 144005419771081461530414279)
  ·
    refine ⟨216008129656622192295621419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144005419771081461530414279 216008129656622192295621419)
    ·
      refine ⟨324012194484933288443432129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216008129656622192295621419 324012194484933288443432129)
      ·
        refine ⟨243009145863699966332574097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324012194484933288443432129 243009145863699966332574097)
        ·
          refine ⟨182256859397774974749430573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243009145863699966332574097 182256859397774974749430573)
          ·
            refine ⟨68346322274165615531036465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182256859397774974749430573 68346322274165615531036465)
            ·
              refine ⟨51259741705624211648277349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68346322274165615531036465 51259741705624211648277349)
              ·
                refine ⟨9611201569804539684052003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51259741705624211648277349 9611201569804539684052003)
                ·
                  refine ⟨14416802354706809526078005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9611201569804539684052003 14416802354706809526078005)
                  ·
                    refine ⟨1351575220753763393069813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14416802354706809526078005 1351575220753763393069813)
                    ·
                      rfl

theorem cell22_3948275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 5].length) (baseStart_3948275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948275 prefixEnd_3948275 := by exact prefixLift 3948275
  have htrace : WordTrace (prefixWord ++ tailWord_3948275) baseStart_3948275 baseEnd_3948275 := by
    simpa [prefixWord, tailWord_3948275, baseEnd_3948275] using wordTrace_append hprefix tailTrace_3948275
  have hstable : (prefixWord ++ tailWord_3948275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948275).length < 2 ^ (prefixWord ++ tailWord_3948275).sum := by decide
  have hdescent : baseEnd_3948275 < baseStart_3948275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948309 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 2, 3]
def baseStart_3948309 : Nat := 118140960795 + 3948309 * 2 ^ 59
def prefixEnd_3948309 : Nat := 4983230072969 + 3 ^ 40 * 3948309 * 2
def baseEnd_3948309 : Nat := 1351586859648598637719709

theorem tailTrace_3948309 : CollatzResearch.WordTrace tailWord_3948309 prefixEnd_3948309 1351586859648598637719709 := by
  unfold tailWord_3948309
  simp only [CollatzResearch.WordTrace]
  refine ⟨144006659852958285337151981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96004439901972190224767987 144006659852958285337151981)
  ·
    refine ⟨54002497444859357001431993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144006659852958285337151981 54002497444859357001431993)
    ·
      refine ⟨40501873083644517751073995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54002497444859357001431993 40501873083644517751073995)
      ·
        refine ⟨60752809625466776626610993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40501873083644517751073995 60752809625466776626610993)
        ·
          refine ⟨45564607219100082469958245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60752809625466776626610993 45564607219100082469958245)
          ·
            refine ⟨8543363853581265463117171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45564607219100082469958245 8543363853581265463117171)
            ·
              refine ⟨12815045780371898194675757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8543363853581265463117171 12815045780371898194675757)
              ·
                refine ⟨4805642167639461823003409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12815045780371898194675757 4805642167639461823003409)
                ·
                  refine ⟨3604231625729596367252557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4805642167639461823003409 3604231625729596367252557)
                  ·
                    refine ⟨1351586859648598637719709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604231625729596367252557 1351586859648598637719709)
                    ·
                      rfl

theorem cell22_3948309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_3948309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948309 prefixEnd_3948309 := by exact prefixLift 3948309
  have htrace : WordTrace (prefixWord ++ tailWord_3948309) baseStart_3948309 baseEnd_3948309 := by
    simpa [prefixWord, tailWord_3948309, baseEnd_3948309] using wordTrace_append hprefix tailTrace_3948309
  have hstable : (prefixWord ++ tailWord_3948309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948309).length < 2 ^ (prefixWord ++ tailWord_3948309).sum := by decide
  have hdescent : baseEnd_3948309 < baseStart_3948309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948324 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_3948324 : Nat := 118140960795 + 3948324 * 2 ^ 59
def prefixEnd_3948324 : Nat := 4983230072969 + 3 ^ 40 * 3948324 * 2
def baseEnd_3948324 : Nat := 1351591994455143598594663

theorem tailTrace_3948324 : CollatzResearch.WordTrace tailWord_3948324 prefixEnd_3948324 1351591994455143598594663 := by
  unfold tailWord_3948324
  simp only [CollatzResearch.WordTrace]
  refine ⟨72003603473951971449474013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96004804631935961932632017 72003603473951971449474013)
  ·
    refine ⟨27001351302731989293552755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72003603473951971449474013 27001351302731989293552755)
    ·
      refine ⟨40502026954097983940329133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27001351302731989293552755 40502026954097983940329133)
      ·
        refine ⟨15188260107786743977623425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40502026954097983940329133 15188260107786743977623425)
        ·
          refine ⟨11391195080840057983217569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15188260107786743977623425 11391195080840057983217569)
          ·
            refine ⟨8543396310630043487413177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11391195080840057983217569 8543396310630043487413177)
            ·
              refine ⟨6407547232972532615559883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8543396310630043487413177 6407547232972532615559883)
              ·
                refine ⟨9611320849458798923339825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6407547232972532615559883 9611320849458798923339825)
                ·
                  refine ⟨7208490637094099192504869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9611320849458798923339825 7208490637094099192504869)
                  ·
                    refine ⟨1351591994455143598594663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7208490637094099192504869 1351591994455143598594663)
                    ·
                      rfl

theorem cell22_3948324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_3948324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948324 prefixEnd_3948324 := by exact prefixLift 3948324
  have htrace : WordTrace (prefixWord ++ tailWord_3948324) baseStart_3948324 baseEnd_3948324 := by
    simpa [prefixWord, tailWord_3948324, baseEnd_3948324] using wordTrace_append hprefix tailTrace_3948324
  have hstable : (prefixWord ++ tailWord_3948324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948324).length < 2 ^ (prefixWord ++ tailWord_3948324).sum := by decide
  have hdescent : baseEnd_3948324 < baseStart_3948324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948345 : List Nat := [1, 2, 1, 7, 2, 1, 2, 2, 4]
def baseStart_3948345 : Nat := 118140960795 + 3948345 * 2 ^ 59
def prefixEnd_3948345 : Nat := 4983230072969 + 3 ^ 40 * 3948345 * 2
def baseEnd_3948345 : Nat := 450533061061435514606533

theorem tailTrace_3948345 : CollatzResearch.WordTrace tailWord_3948345 prefixEnd_3948345 450533061061435514606533 := by
  unfold tailWord_3948345
  simp only [CollatzResearch.WordTrace]
  refine ⟨144007972880827863485462489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96005315253885242323641659 144007972880827863485462489)
  ·
    refine ⟨108005979660620897614096867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144007972880827863485462489 108005979660620897614096867)
    ·
      refine ⟨162008969490931346421145301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108005979660620897614096867 162008969490931346421145301)
      ·
        refine ⟨3797085222443703431745593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 162008969490931346421145301 3797085222443703431745593)
        ·
          refine ⟨2847813916832777573809195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3797085222443703431745593 2847813916832777573809195)
          ·
            refine ⟨4271720875249166360713793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847813916832777573809195 4271720875249166360713793)
            ·
              refine ⟨3203790656436874770535345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271720875249166360713793 3203790656436874770535345)
              ·
                refine ⟨2402842992327656077901509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203790656436874770535345 2402842992327656077901509)
                ·
                  refine ⟨450533061061435514606533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402842992327656077901509 450533061061435514606533)
                  ·
                    rfl

theorem cell22_3948345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 4].length) (baseStart_3948345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948345 prefixEnd_3948345 := by exact prefixLift 3948345
  have htrace : WordTrace (prefixWord ++ tailWord_3948345) baseStart_3948345 baseEnd_3948345 := by
    simpa [prefixWord, tailWord_3948345, baseEnd_3948345] using wordTrace_append hprefix tailTrace_3948345
  have hstable : (prefixWord ++ tailWord_3948345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948345).length < 2 ^ (prefixWord ++ tailWord_3948345).sum := by decide
  have hdescent : baseEnd_3948345 < baseStart_3948345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948388 : List Nat := [2, 3, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_3948388 : Nat := 118140960795 + 3948388 * 2 ^ 59
def prefixEnd_3948388 : Nat := 4983230072969 + 3 ^ 40 * 3948388 * 2
def baseEnd_3948388 : Nat := 1351613902963068764994467

theorem tailTrace_3948388 : CollatzResearch.WordTrace tailWord_3948388 prefixEnd_3948388 1351613902963068764994467 := by
  unfold tailWord_3948388
  simp only [CollatzResearch.WordTrace]
  refine ⟨72004770609836040914638909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96006360813114721219518545 72004770609836040914638909)
  ·
    refine ⟨27001788978688515342989591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72004770609836040914638909 27001788978688515342989591)
    ·
      refine ⟨40502683468032773014484387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27001788978688515342989591 40502683468032773014484387)
      ·
        refine ⟨60754025202049159521726581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40502683468032773014484387 60754025202049159521726581)
        ·
          refine ⟨5695689862692108705161867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60754025202049159521726581 5695689862692108705161867)
          ·
            refine ⟨8543534794038163057742801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5695689862692108705161867 8543534794038163057742801)
            ·
              refine ⟨6407651095528622293307101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8543534794038163057742801 6407651095528622293307101)
              ·
                refine ⟨2402869160823233359990163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6407651095528622293307101 2402869160823233359990163)
                ·
                  refine ⟨3604303741234850039985245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402869160823233359990163 3604303741234850039985245)
                  ·
                    refine ⟨1351613902963068764994467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604303741234850039985245 1351613902963068764994467)
                    ·
                      rfl

theorem cell22_3948388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_3948388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948388 prefixEnd_3948388 := by exact prefixLift 3948388
  have htrace : WordTrace (prefixWord ++ tailWord_3948388) baseStart_3948388 baseEnd_3948388 := by
    simpa [prefixWord, tailWord_3948388, baseEnd_3948388] using wordTrace_append hprefix tailTrace_3948388
  have hstable : (prefixWord ++ tailWord_3948388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948388).length < 2 ^ (prefixWord ++ tailWord_3948388).sum := by decide
  have hdescent : baseEnd_3948388 < baseStart_3948388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948395 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 10]
def baseStart_3948395 : Nat := 118140960795 + 3948395 * 2 ^ 59
def prefixEnd_3948395 : Nat := 4983230072969 + 3 ^ 40 * 3948395 * 2
def baseEnd_3948395 : Nat := 450538766402041026689815

theorem tailTrace_3948395 : CollatzResearch.WordTrace tailWord_3948395 prefixEnd_3948395 450538766402041026689815 := by
  unfold tailWord_3948395
  simp only [CollatzResearch.WordTrace]
  refine ⟨144009796530646722024782639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96006531020431148016521759 144009796530646722024782639)
  ·
    refine ⟨216014694795970083037173959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144009796530646722024782639 216014694795970083037173959)
    ·
      refine ⟨324022042193955124555760939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216014694795970083037173959 324022042193955124555760939)
      ·
        refine ⟨486033063290932686833641409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324022042193955124555760939 486033063290932686833641409)
        ·
          refine ⟨364524797468199515125231057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486033063290932686833641409 364524797468199515125231057)
          ·
            refine ⟨273393598101149636343923293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364524797468199515125231057 273393598101149636343923293)
            ·
              refine ⟨102522599287931113628971235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273393598101149636343923293 102522599287931113628971235)
              ·
                refine ⟨153783898931896670443456853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102522599287931113628971235 153783898931896670443456853)
                ·
                  refine ⟨450538766402041026689815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 153783898931896670443456853 450538766402041026689815)
                  ·
                    rfl

theorem cell22_3948395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 10].length) (baseStart_3948395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948395 prefixEnd_3948395 := by exact prefixLift 3948395
  have htrace : WordTrace (prefixWord ++ tailWord_3948395) baseStart_3948395 baseEnd_3948395 := by
    simpa [prefixWord, tailWord_3948395, baseEnd_3948395] using wordTrace_append hprefix tailTrace_3948395
  have hstable : (prefixWord ++ tailWord_3948395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948395).length < 2 ^ (prefixWord ++ tailWord_3948395).sum := by decide
  have hdescent : baseEnd_3948395 < baseStart_3948395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948478 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_3948478 : Nat := 118140960795 + 3948478 * 2 ^ 59
def prefixEnd_3948478 : Nat := 4983230072969 + 3 ^ 40 * 3948478 * 2
def baseEnd_3948478 : Nat := 1351644711802338530244191

theorem tailTrace_3948478 : CollatzResearch.WordTrace tailWord_3948478 prefixEnd_3948478 1351644711802338530244191 := by
  unfold tailWord_3948478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18001602973668253400006761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96008549192897351466702725 18001602973668253400006761)
  ·
    refine ⟨13501202230251190050005071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18001602973668253400006761 13501202230251190050005071)
    ·
      refine ⟨20251803345376785075007607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13501202230251190050005071 20251803345376785075007607)
      ·
        refine ⟨30377705018065177612511411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20251803345376785075007607 30377705018065177612511411)
        ·
          refine ⟨45566557527097766418767117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30377705018065177612511411 45566557527097766418767117)
          ·
            refine ⟨17087459072661662407037669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45566557527097766418767117 17087459072661662407037669)
            ·
              refine ⟨3203898576124061701319563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17087459072661662407037669 3203898576124061701319563)
              ·
                refine ⟨4805847864186092551979345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203898576124061701319563 4805847864186092551979345)
                ·
                  refine ⟨3604385898139569413984509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4805847864186092551979345 3604385898139569413984509)
                  ·
                    refine ⟨1351644711802338530244191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604385898139569413984509 1351644711802338530244191)
                    ·
                      rfl

theorem cell22_3948478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_3948478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948478 prefixEnd_3948478 := by exact prefixLift 3948478
  have htrace : WordTrace (prefixWord ++ tailWord_3948478) baseStart_3948478 baseEnd_3948478 := by
    simpa [prefixWord, tailWord_3948478, baseEnd_3948478] using wordTrace_append hprefix tailTrace_3948478
  have hstable : (prefixWord ++ tailWord_3948478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948478).length < 2 ^ (prefixWord ++ tailWord_3948478).sum := by decide
  have hdescent : baseEnd_3948478 < baseStart_3948478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948508 : List Nat := [2, 2, 6, 1, 2, 9]
def baseStart_3948508 : Nat := 118140960795 + 3948508 * 2 ^ 59
def prefixEnd_3948508 : Nat := 4983230072969 + 3 ^ 40 * 3948508 * 2
def baseEnd_3948508 : Nat := 16687098535992943851779

theorem tailTrace_3948508 : CollatzResearch.WordTrace tailWord_3948508 prefixEnd_3948508 16687098535992943851779 := by
  unfold tailWord_3948508
  simp only [CollatzResearch.WordTrace]
  refine ⟨72006958989618671161823089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96009278652824894882430785 72006958989618671161823089)
  ·
    refine ⟨54005219242214003371367317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72006958989618671161823089 54005219242214003371367317)
    ·
      refine ⟨2531494651978781408032843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54005219242214003371367317 2531494651978781408032843)
      ·
        refine ⟨3797241977968172112049265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531494651978781408032843 3797241977968172112049265)
        ·
          refine ⟨2847931483476129084036949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3797241977968172112049265 2847931483476129084036949)
          ·
            refine ⟨16687098535992943851779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2847931483476129084036949 16687098535992943851779)
            ·
              rfl

theorem cell22_3948508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 9].length) (baseStart_3948508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948508 prefixEnd_3948508 := by exact prefixLift 3948508
  have htrace : WordTrace (prefixWord ++ tailWord_3948508) baseStart_3948508 baseEnd_3948508 := by
    simpa [prefixWord, tailWord_3948508, baseEnd_3948508] using wordTrace_append hprefix tailTrace_3948508
  have hstable : (prefixWord ++ tailWord_3948508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948508).length < 2 ^ (prefixWord ++ tailWord_3948508).sum := by decide
  have hdescent : baseEnd_3948508 < baseStart_3948508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948549 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_3948549 : Nat := 118140960795 + 3948549 * 2 ^ 59
def prefixEnd_3948549 : Nat := 4983230072969 + 3 ^ 40 * 3948549 * 2
def baseEnd_3948549 : Nat := 1351669016553318011718973

theorem tailTrace_3948549 : CollatzResearch.WordTrace tailWord_3948549 prefixEnd_3948549 1351669016553318011718973 := by
  unfold tailWord_3948549
  simp only [CollatzResearch.WordTrace]
  refine ⟨144015413372088806325888701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96010275581392537550592467 144015413372088806325888701)
  ·
    refine ⟨54005780014533302372208263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144015413372088806325888701 54005780014533302372208263)
    ·
      refine ⟨81008670021799953558312395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54005780014533302372208263 81008670021799953558312395)
      ·
        refine ⟨121513005032699930337468593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81008670021799953558312395 121513005032699930337468593)
        ·
          refine ⟨91134753774524947753101445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121513005032699930337468593 91134753774524947753101445)
          ·
            refine ⟨17087766332723427703706521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91134753774524947753101445 17087766332723427703706521)
            ·
              refine ⟨12815824749542570777779891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17087766332723427703706521 12815824749542570777779891)
              ·
                refine ⟨19223737124313856166669837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12815824749542570777779891 19223737124313856166669837)
                ·
                  refine ⟨7208901421617696062501189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19223737124313856166669837 7208901421617696062501189)
                  ·
                    refine ⟨1351669016553318011718973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7208901421617696062501189 1351669016553318011718973)
                    ·
                      rfl

theorem cell22_3948549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_3948549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948549 prefixEnd_3948549 := by exact prefixLift 3948549
  have htrace : WordTrace (prefixWord ++ tailWord_3948549) baseStart_3948549 baseEnd_3948549 := by
    simpa [prefixWord, tailWord_3948549, baseEnd_3948549] using wordTrace_append hprefix tailTrace_3948549
  have hstable : (prefixWord ++ tailWord_3948549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948549).length < 2 ^ (prefixWord ++ tailWord_3948549).sum := by decide
  have hdescent : baseEnd_3948549 < baseStart_3948549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948581 : List Nat := [1, 3, 1, 2, 2, 3, 2, 4, 4]
def baseStart_3948581 : Nat := 118140960795 + 3948581 * 2 ^ 59
def prefixEnd_3948581 : Nat := 4983230072969 + 3 ^ 40 * 3948581 * 2
def baseEnd_3948581 : Nat := 450559990269093531639625

theorem tailTrace_3948581 : CollatzResearch.WordTrace tailWord_3948581 prefixEnd_3948581 450559990269093531639625 := by
  unfold tailWord_3948581
  simp only [CollatzResearch.WordTrace]
  refine ⟨144016580507972875791053597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96011053671981917194035731 144016580507972875791053597)
  ·
    refine ⟨54006217690489828421645099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144016580507972875791053597 54006217690489828421645099)
    ·
      refine ⟨81009326535734742632467649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54006217690489828421645099 81009326535734742632467649)
      ·
        refine ⟨60756994901801056974350737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81009326535734742632467649 60756994901801056974350737)
        ·
          refine ⟨45567746176350792730763053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60756994901801056974350737 45567746176350792730763053)
          ·
            refine ⟨17087904816131547274036145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45567746176350792730763053 17087904816131547274036145)
            ·
              refine ⟨12815928612098660455527109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17087904816131547274036145 12815928612098660455527109)
              ·
                refine ⟨2402986614768498835411333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12815928612098660455527109 2402986614768498835411333)
                ·
                  refine ⟨450559990269093531639625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402986614768498835411333 450559990269093531639625)
                  ·
                    rfl

theorem cell22_3948581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_3948581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948581 prefixEnd_3948581 := by exact prefixLift 3948581
  have htrace : WordTrace (prefixWord ++ tailWord_3948581) baseStart_3948581 baseEnd_3948581 := by
    simpa [prefixWord, tailWord_3948581, baseEnd_3948581] using wordTrace_append hprefix tailTrace_3948581
  have hstable : (prefixWord ++ tailWord_3948581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948581).length < 2 ^ (prefixWord ++ tailWord_3948581).sum := by decide
  have hdescent : baseEnd_3948581 < baseStart_3948581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948594 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_3948594 : Nat := 118140960795 + 3948594 * 2 ^ 59
def prefixEnd_3948594 : Nat := 4983230072969 + 3 ^ 40 * 3948594 * 2
def baseEnd_3948594 : Nat := 1351684420972952894343835

theorem tailTrace_3948594 : CollatzResearch.WordTrace tailWord_3948594 prefixEnd_3948594 1351684420972952894343835 := by
  unfold tailWord_3948594
  simp only [CollatzResearch.WordTrace]
  refine ⟨36004263664231444752819209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96011369771283852674184557 36004263664231444752819209)
  ·
    refine ⟨27003197748173583564614407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36004263664231444752819209 27003197748173583564614407)
    ·
      refine ⟨40504796622260375346921611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27003197748173583564614407 40504796622260375346921611)
      ·
        refine ⟨60757194933390563020382417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40504796622260375346921611 60757194933390563020382417)
        ·
          refine ⟨45567896200042922265286813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60757194933390563020382417 45567896200042922265286813)
          ·
            refine ⟨17087961075016095849482555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45567896200042922265286813 17087961075016095849482555)
            ·
              refine ⟨25631941612524143774223833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17087961075016095849482555 25631941612524143774223833)
              ·
                refine ⟨19223956209393107830667875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25631941612524143774223833 19223956209393107830667875)
                ·
                  refine ⟨28835934314089661746001813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19223956209393107830667875 28835934314089661746001813)
                  ·
                    refine ⟨1351684420972952894343835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28835934314089661746001813 1351684420972952894343835)
                    ·
                      rfl

theorem cell22_3948594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_3948594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948594 prefixEnd_3948594 := by exact prefixLift 3948594
  have htrace : WordTrace (prefixWord ++ tailWord_3948594) baseStart_3948594 baseEnd_3948594 := by
    simpa [prefixWord, tailWord_3948594, baseEnd_3948594] using wordTrace_append hprefix tailTrace_3948594
  have hstable : (prefixWord ++ tailWord_3948594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948594).length < 2 ^ (prefixWord ++ tailWord_3948594).sum := by decide
  have hdescent : baseEnd_3948594 < baseStart_3948594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948626 : List Nat := [3, 2, 2, 1, 4, 2, 8]
def baseStart_3948626 : Nat := 118140960795 + 3948626 * 2 ^ 59
def prefixEnd_3948626 : Nat := 4983230072969 + 3 ^ 40 * 3948626 * 2
def baseEnd_3948626 : Nat := 50062791675070943612731

theorem tailTrace_3948626 : CollatzResearch.WordTrace tailWord_3948626 prefixEnd_3948626 50062791675070943612731 := by
  unfold tailWord_3948626
  simp only [CollatzResearch.WordTrace]
  refine ⟨36004555448202462119110433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96012147861873232317627821 36004555448202462119110433)
  ·
    refine ⟨27003416586151846589332825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36004555448202462119110433 27003416586151846589332825)
    ·
      refine ⟨20252562439613884941999619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27003416586151846589332825 20252562439613884941999619)
      ·
        refine ⟨30378843659420827412999429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20252562439613884941999619 30378843659420827412999429)
        ·
          refine ⟨5696033186141405139937393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30378843659420827412999429 5696033186141405139937393)
          ·
            refine ⟨4272024889606053854953045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5696033186141405139937393 4272024889606053854953045)
            ·
              refine ⟨50062791675070943612731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4272024889606053854953045 50062791675070943612731)
              ·
                rfl

theorem cell22_3948626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 8].length) (baseStart_3948626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948626 prefixEnd_3948626 := by exact prefixLift 3948626
  have htrace : WordTrace (prefixWord ++ tailWord_3948626) baseStart_3948626 baseEnd_3948626 := by
    simpa [prefixWord, tailWord_3948626, baseEnd_3948626] using wordTrace_append hprefix tailTrace_3948626
  have hstable : (prefixWord ++ tailWord_3948626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948626).length < 2 ^ (prefixWord ++ tailWord_3948626).sum := by decide
  have hdescent : baseEnd_3948626 < baseStart_3948626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948630 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3948630 : Nat := 118140960795 + 3948630 * 2 ^ 59
def prefixEnd_3948630 : Nat := 4983230072969 + 3 ^ 40 * 3948630 * 2
def baseEnd_3948630 : Nat := 1351696744508660800443725

theorem tailTrace_3948630 : CollatzResearch.WordTrace tailWord_3948630 prefixEnd_3948630 1351696744508660800443725 := by
  unfold tailWord_3948630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9001147980299709822474209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96012245123196904773058229 9001147980299709822474209)
  ·
    refine ⟨6750860985224782366855657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9001147980299709822474209 6750860985224782366855657)
    ·
      refine ⟨5063145738918586775141743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6750860985224782366855657 5063145738918586775141743)
      ·
        refine ⟨7594718608377880162712615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063145738918586775141743 7594718608377880162712615)
        ·
          refine ⟨11392077912566820244068923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7594718608377880162712615 11392077912566820244068923)
          ·
            refine ⟨17088116868850230366103385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11392077912566820244068923 17088116868850230366103385)
            ·
              refine ⟨12816087651637672774577539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17088116868850230366103385 12816087651637672774577539)
              ·
                refine ⟨19224131477456509161866309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12816087651637672774577539 19224131477456509161866309)
                ·
                  refine ⟨3604524652023095467849933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19224131477456509161866309 3604524652023095467849933)
                  ·
                    refine ⟨1351696744508660800443725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604524652023095467849933 1351696744508660800443725)
                    ·
                      rfl

theorem cell22_3948630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3948630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948630 prefixEnd_3948630 := by exact prefixLift 3948630
  have htrace : WordTrace (prefixWord ++ tailWord_3948630) baseStart_3948630 baseEnd_3948630 := by
    simpa [prefixWord, tailWord_3948630, baseEnd_3948630] using wordTrace_append hprefix tailTrace_3948630
  have hstable : (prefixWord ++ tailWord_3948630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948630).length < 2 ^ (prefixWord ++ tailWord_3948630).sum := by decide
  have hdescent : baseEnd_3948630 < baseStart_3948630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948694 : List Nat := [5, 3, 2, 1, 1, 2, 1, 7]
def baseStart_3948694 : Nat := 118140960795 + 3948694 * 2 ^ 59
def prefixEnd_3948694 : Nat := 4983230072969 + 3 ^ 40 * 3948694 * 2
def baseEnd_3948694 : Nat := 150190961446287329649281

theorem tailTrace_3948694 : CollatzResearch.WordTrace tailWord_3948694 prefixEnd_3948694 150190961446287329649281 := by
  unfold tailWord_3948694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9001293872285218505619821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96013801304375664059944757 9001293872285218505619821)
  ·
    refine ⟨3375485202106956939607433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9001293872285218505619821 3375485202106956939607433)
    ·
      refine ⟨2531613901580217704705575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3375485202106956939607433 2531613901580217704705575)
      ·
        refine ⟨3797420852370326557058363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531613901580217704705575 3797420852370326557058363)
        ·
          refine ⟨5696131278555489835587545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3797420852370326557058363 5696131278555489835587545)
          ·
            refine ⟨4272098458916617376690659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5696131278555489835587545 4272098458916617376690659)
            ·
              refine ⟨6408147688374926065035989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272098458916617376690659 6408147688374926065035989)
              ·
                refine ⟨150190961446287329649281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6408147688374926065035989 150190961446287329649281)
                ·
                  rfl

theorem cell22_3948694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_3948694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948694 prefixEnd_3948694 := by exact prefixLift 3948694
  have htrace : WordTrace (prefixWord ++ tailWord_3948694) baseStart_3948694 baseEnd_3948694 := by
    simpa [prefixWord, tailWord_3948694, baseEnd_3948694] using wordTrace_append hprefix tailTrace_3948694
  have hstable : (prefixWord ++ tailWord_3948694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948694).length < 2 ^ (prefixWord ++ tailWord_3948694).sum := by decide
  have hdescent : baseEnd_3948694 < baseStart_3948694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948701 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3948701 : Nat := 118140960795 + 3948701 * 2 ^ 59
def prefixEnd_3948701 : Nat := 4983230072969 + 3 ^ 40 * 3948701 * 2
def baseEnd_3948701 : Nat := 1351721049259640281918507

theorem tailTrace_3948701 : CollatzResearch.WordTrace tailWord_3948701 prefixEnd_3948701 1351721049259640281918507 := by
  unfold tailWord_3948701
  simp only [CollatzResearch.WordTrace]
  refine ⟨144020957267538136285421957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96013971511692090856947971 144020957267538136285421957)
  ·
    refine ⟨27003929487663400553516617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144020957267538136285421957 27003929487663400553516617)
    ·
      refine ⟨20252947115747550415137463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27003929487663400553516617 20252947115747550415137463)
      ·
        refine ⟨30379420673621325622706195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20252947115747550415137463 30379420673621325622706195)
        ·
          refine ⟨45569131010431988434059293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30379420673621325622706195 45569131010431988434059293)
          ·
            refine ⟨17088424128911995662772235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45569131010431988434059293 17088424128911995662772235)
            ·
              refine ⟨25632636193367993494158353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17088424128911995662772235 25632636193367993494158353)
              ·
                refine ⟨19224477145025995120618765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25632636193367993494158353 19224477145025995120618765)
                ·
                  refine ⟨7209178929384748170232037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19224477145025995120618765 7209178929384748170232037)
                  ·
                    refine ⟨1351721049259640281918507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7209178929384748170232037 1351721049259640281918507)
                    ·
                      rfl

theorem cell22_3948701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3948701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948701 prefixEnd_3948701 := by exact prefixLift 3948701
  have htrace : WordTrace (prefixWord ++ tailWord_3948701) baseStart_3948701 baseEnd_3948701 := by
    simpa [prefixWord, tailWord_3948701, baseEnd_3948701] using wordTrace_append hprefix tailTrace_3948701
  have hstable : (prefixWord ++ tailWord_3948701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948701).length < 2 ^ (prefixWord ++ tailWord_3948701).sum := by decide
  have hdescent : baseEnd_3948701 < baseStart_3948701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948731 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 4, 3]
def baseStart_3948731 : Nat := 118140960795 + 3948731 * 2 ^ 59
def prefixEnd_3948731 : Nat := 4983230072969 + 3 ^ 40 * 3948731 * 2
def baseEnd_3948731 : Nat := 1351731318872730203668415

theorem tailTrace_3948731 : CollatzResearch.WordTrace tailWord_3948731 prefixEnd_3948731 1351731318872730203668415 := by
  unfold tailWord_3948731
  simp only [CollatzResearch.WordTrace]
  refine ⟨144022051457429451409014047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96014700971619634272676031 144022051457429451409014047)
  ·
    refine ⟨216033077186144177113521071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144022051457429451409014047 216033077186144177113521071)
    ·
      refine ⟨324049615779216265670281607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216033077186144177113521071 324049615779216265670281607)
      ·
        refine ⟨486074423668824398505422411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324049615779216265670281607 486074423668824398505422411)
        ·
          refine ⟨729111635503236597758133617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486074423668824398505422411 729111635503236597758133617)
          ·
            refine ⟨546833726627427448318600213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729111635503236597758133617 546833726627427448318600213)
            ·
              refine ⟨25632830935660661639934385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 546833726627427448318600213 25632830935660661639934385)
              ·
                refine ⟨19224623201745496229950789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25632830935660661639934385 19224623201745496229950789)
                ·
                  refine ⟨3604616850327280543115773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19224623201745496229950789 3604616850327280543115773)
                  ·
                    refine ⟨1351731318872730203668415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604616850327280543115773 1351731318872730203668415)
                    ·
                      rfl

theorem cell22_3948731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 3].length) (baseStart_3948731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948731 prefixEnd_3948731 := by exact prefixLift 3948731
  have htrace : WordTrace (prefixWord ++ tailWord_3948731) baseStart_3948731 baseEnd_3948731 := by
    simpa [prefixWord, tailWord_3948731, baseEnd_3948731] using wordTrace_append hprefix tailTrace_3948731
  have hstable : (prefixWord ++ tailWord_3948731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948731).length < 2 ^ (prefixWord ++ tailWord_3948731).sum := by decide
  have hdescent : baseEnd_3948731 < baseStart_3948731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948746 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_3948746 : Nat := 118140960795 + 3948746 * 2 ^ 59
def prefixEnd_3948746 : Nat := 4983230072969 + 3 ^ 40 * 3948746 * 2
def baseEnd_3948746 : Nat := 1351736453679275164543369

theorem tailTrace_3948746 : CollatzResearch.WordTrace tailWord_3948746 prefixEnd_3948746 1351736453679275164543369 := by
  unfold tailWord_3948746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36005649638093777242702523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96015065701583405980540061 36005649638093777242702523)
  ·
    refine ⟨54008474457140665864053785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36005649638093777242702523 54008474457140665864053785)
    ·
      refine ⟨40506355842855499398040339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54008474457140665864053785 40506355842855499398040339)
      ·
        refine ⟨60759533764283249097060509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40506355842855499398040339 60759533764283249097060509)
        ·
          refine ⟨22784825161606218411397691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60759533764283249097060509 22784825161606218411397691)
          ·
            refine ⟨34177237742409327617096537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22784825161606218411397691 34177237742409327617096537)
            ·
              refine ⟨25632928306806995712822403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34177237742409327617096537 25632928306806995712822403)
              ·
                refine ⟨38449392460210493569233605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25632928306806995712822403 38449392460210493569233605)
                ·
                  refine ⟨7209261086289467544231301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38449392460210493569233605 7209261086289467544231301)
                  ·
                    refine ⟨1351736453679275164543369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7209261086289467544231301 1351736453679275164543369)
                    ·
                      rfl

theorem cell22_3948746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_3948746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948746 prefixEnd_3948746 := by exact prefixLift 3948746
  have htrace : WordTrace (prefixWord ++ tailWord_3948746) baseStart_3948746 baseEnd_3948746 := by
    simpa [prefixWord, tailWord_3948746, baseEnd_3948746] using wordTrace_append hprefix tailTrace_3948746
  have hstable : (prefixWord ++ tailWord_3948746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948746).length < 2 ^ (prefixWord ++ tailWord_3948746).sum := by decide
  have hdescent : baseEnd_3948746 < baseStart_3948746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948765 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3948765 : Nat := 118140960795 + 3948765 * 2 ^ 59
def prefixEnd_3948765 : Nat := 4983230072969 + 3 ^ 40 * 3948765 * 2
def baseEnd_3948765 : Nat := 1351742957767565448318311

theorem tailTrace_3948765 : CollatzResearch.WordTrace tailWord_3948765 prefixEnd_3948765 1351742957767565448318311 := by
  unfold tailWord_3948765
  simp only [CollatzResearch.WordTrace]
  refine ⟨144023291539306275215751749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96015527692870850143834499 144023291539306275215751749)
  ·
    refine ⟨27004367163619926602953453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144023291539306275215751749 27004367163619926602953453)
    ·
      refine ⟨10126637686357472476107545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27004367163619926602953453 10126637686357472476107545)
      ·
        refine ⟨7594978264768104357080659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10126637686357472476107545 7594978264768104357080659)
        ·
          refine ⟨11392467397152156535620989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7594978264768104357080659 11392467397152156535620989)
          ·
            refine ⟨4272175273932058700857871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11392467397152156535620989 4272175273932058700857871)
            ·
              refine ⟨6408262910898088051286807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272175273932058700857871 6408262910898088051286807)
              ·
                refine ⟨9612394366347132076930211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408262910898088051286807 9612394366347132076930211)
                ·
                  refine ⟨14418591549520698115395317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9612394366347132076930211 14418591549520698115395317)
                  ·
                    refine ⟨1351742957767565448318311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14418591549520698115395317 1351742957767565448318311)
                    ·
                      rfl

theorem cell22_3948765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3948765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948765 prefixEnd_3948765 := by exact prefixLift 3948765
  have htrace : WordTrace (prefixWord ++ tailWord_3948765) baseStart_3948765 baseEnd_3948765 := by
    simpa [prefixWord, tailWord_3948765, baseEnd_3948765] using wordTrace_append hprefix tailTrace_3948765
  have hstable : (prefixWord ++ tailWord_3948765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948765).length < 2 ^ (prefixWord ++ tailWord_3948765).sum := by decide
  have hdescent : baseEnd_3948765 < baseStart_3948765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948810 : List Nat := [3, 1, 2, 2, 1, 1, 2, 6, 1, 3]
def baseStart_3948810 : Nat := 118140960795 + 3948810 * 2 ^ 59
def prefixEnd_3948810 : Nat := 4983230072969 + 3 ^ 40 * 3948810 * 2
def baseEnd_3948810 : Nat := 1351758362187200330943173

theorem tailTrace_3948810 : CollatzResearch.WordTrace tailWord_3948810 prefixEnd_3948810 1351758362187200330943173 := by
  unfold tailWord_3948810
  simp only [CollatzResearch.WordTrace]
  refine ⟨36006233206035811975284971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96016621882762165267426589 36006233206035811975284971)
  ·
    refine ⟨54009349809053717962927457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36006233206035811975284971 54009349809053717962927457)
    ·
      refine ⟨40507012356790288472195593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54009349809053717962927457 40507012356790288472195593)
      ·
        refine ⟨30380259267592716354146695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40507012356790288472195593 30380259267592716354146695)
        ·
          refine ⟨45570388901389074531220043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30380259267592716354146695 45570388901389074531220043)
          ·
            refine ⟨68355583352083611796830065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45570388901389074531220043 68355583352083611796830065)
            ·
              refine ⟨51266687514062708847622549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68355583352083611796830065 51266687514062708847622549)
              ·
                refine ⟨2403125977221689477232307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51266687514062708847622549 2403125977221689477232307)
                ·
                  refine ⟨3604688965832534215848461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403125977221689477232307 3604688965832534215848461)
                  ·
                    refine ⟨1351758362187200330943173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604688965832534215848461 1351758362187200330943173)
                    ·
                      rfl

theorem cell22_3948810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_3948810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948810 prefixEnd_3948810 := by exact prefixLift 3948810
  have htrace : WordTrace (prefixWord ++ tailWord_3948810) baseStart_3948810 baseEnd_3948810 := by
    simpa [prefixWord, tailWord_3948810, baseEnd_3948810] using wordTrace_append hprefix tailTrace_3948810
  have hstable : (prefixWord ++ tailWord_3948810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948810).length < 2 ^ (prefixWord ++ tailWord_3948810).sum := by decide
  have hdescent : baseEnd_3948810 < baseStart_3948810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948821 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_3948821 : Nat := 118140960795 + 3948821 * 2 ^ 59
def prefixEnd_3948821 : Nat := 4983230072969 + 3 ^ 40 * 3948821 * 2
def baseEnd_3948821 : Nat := 1351762127711999968918139

theorem tailTrace_3948821 : CollatzResearch.WordTrace tailWord_3948821 prefixEnd_3948821 1351762127711999968918139 := by
  unfold tailWord_3948821
  simp only [CollatzResearch.WordTrace]
  refine ⟨144025334027103396779790317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96016889351402264519860211 144025334027103396779790317)
  ·
    refine ⟨54009500260163773792421369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144025334027103396779790317 54009500260163773792421369)
    ·
      refine ⟨40507125195122830344316027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54009500260163773792421369 40507125195122830344316027)
      ·
        refine ⟨60760687792684245516474041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40507125195122830344316027 60760687792684245516474041)
        ·
          refine ⟨45570515844513184137355531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60760687792684245516474041 45570515844513184137355531)
          ·
            refine ⟨68355773766769776206033297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45570515844513184137355531 68355773766769776206033297)
            ·
              refine ⟨51266830325077332154524973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68355773766769776206033297 51266830325077332154524973)
              ·
                refine ⟨19225061371903999557946865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51266830325077332154524973 19225061371903999557946865)
                ·
                  refine ⟨14418796028927999668460149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19225061371903999557946865 14418796028927999668460149)
                  ·
                    refine ⟨1351762127711999968918139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14418796028927999668460149 1351762127711999968918139)
                    ·
                      rfl

theorem cell22_3948821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_3948821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948821 prefixEnd_3948821 := by exact prefixLift 3948821
  have htrace : WordTrace (prefixWord ++ tailWord_3948821) baseStart_3948821 baseEnd_3948821 := by
    simpa [prefixWord, tailWord_3948821, baseEnd_3948821] using wordTrace_append hprefix tailTrace_3948821
  have hstable : (prefixWord ++ tailWord_3948821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948821).length < 2 ^ (prefixWord ++ tailWord_3948821).sum := by decide
  have hdescent : baseEnd_3948821 < baseStart_3948821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948823 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 5]
def baseStart_3948823 : Nat := 118140960795 + 3948823 * 2 ^ 59
def prefixEnd_3948823 : Nat := 4983230072969 + 3 ^ 40 * 3948823 * 2
def baseEnd_3948823 : Nat := 450587604117624210122711

theorem tailTrace_3948823 : CollatzResearch.WordTrace tailWord_3948823 prefixEnd_3948823 450587604117624210122711 := by
  unfold tailWord_3948823
  simp only [CollatzResearch.WordTrace]
  refine ⟨144025406973096151121363123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96016937982064100747575415 144025406973096151121363123)
  ·
    refine ⟨216038110459644226682044685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144025406973096151121363123 216038110459644226682044685)
    ·
      refine ⟨81014291422366585005766757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216038110459644226682044685 81014291422366585005766757)
      ·
        refine ⟨15190179641693734688581267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81014291422366585005766757 15190179641693734688581267)
        ·
          refine ⟨22785269462540602032871901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15190179641693734688581267 22785269462540602032871901)
          ·
            refine ⟨8544476048452725762326963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22785269462540602032871901 8544476048452725762326963)
            ·
              refine ⟨12816714072679088643490445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8544476048452725762326963 12816714072679088643490445)
              ·
                refine ⟨4806267777254658241308917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12816714072679088643490445 4806267777254658241308917)
                ·
                  refine ⟨450587604117624210122711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4806267777254658241308917 450587604117624210122711)
                  ·
                    rfl

theorem cell22_3948823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 5].length) (baseStart_3948823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948823 prefixEnd_3948823 := by exact prefixLift 3948823
  have htrace : WordTrace (prefixWord ++ tailWord_3948823) baseStart_3948823 baseEnd_3948823 := by
    simpa [prefixWord, tailWord_3948823, baseEnd_3948823] using wordTrace_append hprefix tailTrace_3948823
  have hstable : (prefixWord ++ tailWord_3948823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948823).length < 2 ^ (prefixWord ++ tailWord_3948823).sum := by decide
  have hdescent : baseEnd_3948823 < baseStart_3948823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948917 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3948917 : Nat := 118140960795 + 3948917 * 2 ^ 59
def prefixEnd_3948917 : Nat := 4983230072969 + 3 ^ 40 * 3948917 * 2
def baseEnd_3948917 : Nat := 1351794990473887718517845

theorem tailTrace_3948917 : CollatzResearch.WordTrace tailWord_3948917 prefixEnd_3948917 1351794990473887718517845 := by
  unfold tailWord_3948917
  simp only [CollatzResearch.WordTrace]
  refine ⟨144028835434755605175285005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96019223623170403450190003 144028835434755605175285005)
  ·
    refine ⟨54010813288033351940731877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144028835434755605175285005 54010813288033351940731877)
    ·
      refine ⟨10127027491506253488887227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54010813288033351940731877 10127027491506253488887227)
      ·
        refine ⟨15190541237259380233330841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10127027491506253488887227 15190541237259380233330841)
        ·
          refine ⟨11392905927944535174998131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15190541237259380233330841 11392905927944535174998131)
          ·
            refine ⟨17089358891916802762497197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11392905927944535174998131 17089358891916802762497197)
            ·
              refine ⟨6408509584468801035936449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17089358891916802762497197 6408509584468801035936449)
              ·
                refine ⟨4806382188351600776952337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6408509584468801035936449 4806382188351600776952337)
                ·
                  refine ⟨3604786641263700582714253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4806382188351600776952337 3604786641263700582714253)
                  ·
                    refine ⟨1351794990473887718517845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604786641263700582714253 1351794990473887718517845)
                    ·
                      rfl

theorem cell22_3948917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3948917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3948917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3948917 prefixEnd_3948917 := by exact prefixLift 3948917
  have htrace : WordTrace (prefixWord ++ tailWord_3948917) baseStart_3948917 baseEnd_3948917 := by
    simpa [prefixWord, tailWord_3948917, baseEnd_3948917] using wordTrace_append hprefix tailTrace_3948917
  have hstable : (prefixWord ++ tailWord_3948917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948917).length < 2 ^ (prefixWord ++ tailWord_3948917).sum := by decide
  have hdescent : baseEnd_3948917 < baseStart_3948917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949033 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_3949033 : Nat := 118140960795 + 3949033 * 2 ^ 59
def prefixEnd_3949033 : Nat := 4983230072969 + 3 ^ 40 * 3949033 * 2
def baseEnd_3949033 : Nat := 1351834699644502082617489

theorem tailTrace_3949033 : CollatzResearch.WordTrace tailWord_3949033 prefixEnd_3949033 1351834699644502082617489 := by
  unfold tailWord_3949033
  simp only [CollatzResearch.WordTrace]
  refine ⟨144033066302335356986507753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96022044201556904657671835 144033066302335356986507753)
  ·
    refine ⟨108024799726751517739880815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144033066302335356986507753 108024799726751517739880815)
    ·
      refine ⟨162037199590127276609821223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108024799726751517739880815 162037199590127276609821223)
      ·
        refine ⟨243055799385190914914731835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162037199590127276609821223 243055799385190914914731835)
        ·
          refine ⟨364583699077786372372097753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243055799385190914914731835 364583699077786372372097753)
          ·
            refine ⟨273437774308339779279073315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364583699077786372372097753 273437774308339779279073315)
            ·
              refine ⟨410156661462509668918609973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273437774308339779279073315 410156661462509668918609973)
              ·
                refine ⟨38452187012110281461119685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410156661462509668918609973 38452187012110281461119685)
                ·
                  refine ⟨7209785064770677773959941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38452187012110281461119685 7209785064770677773959941)
                  ·
                    refine ⟨1351834699644502082617489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7209785064770677773959941 1351834699644502082617489)
                    ·
                      rfl

theorem cell22_3949033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_3949033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949033 prefixEnd_3949033 := by exact prefixLift 3949033
  have htrace : WordTrace (prefixWord ++ tailWord_3949033) baseStart_3949033 baseEnd_3949033 := by
    simpa [prefixWord, tailWord_3949033, baseEnd_3949033] using wordTrace_append hprefix tailTrace_3949033
  have hstable : (prefixWord ++ tailWord_3949033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949033).length < 2 ^ (prefixWord ++ tailWord_3949033).sum := by decide
  have hdescent : baseEnd_3949033 < baseStart_3949033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949067 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 2, 4]
def baseStart_3949067 : Nat := 118140960795 + 3949067 * 2 ^ 59
def prefixEnd_3949067 : Nat := 4983230072969 + 3 ^ 40 * 3949067 * 2
def baseEnd_3949067 : Nat := 1351846338539337327267385

theorem tailTrace_3949067 : CollatzResearch.WordTrace tailWord_3949067 prefixEnd_3949067 1351846338539337327267385 := by
  unfold tailWord_3949067
  simp only [CollatzResearch.WordTrace]
  refine ⟨144034306384212180793245455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96022870922808120528830303 144034306384212180793245455)
  ·
    refine ⟨216051459576318271189868183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144034306384212180793245455 216051459576318271189868183)
    ·
      refine ⟨324077189364477406784802275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216051459576318271189868183 324077189364477406784802275)
      ·
        refine ⟨486115784046716110177203413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324077189364477406784802275 486115784046716110177203413)
        ·
          refine ⟨11393338688594908832278205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 486115784046716110177203413 11393338688594908832278205)
          ·
            refine ⟨4272502008223090812104327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11393338688594908832278205 4272502008223090812104327)
            ·
              refine ⟨6408753012334636218156491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272502008223090812104327 6408753012334636218156491)
              ·
                refine ⟨9613129518501954327234737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408753012334636218156491 9613129518501954327234737)
                ·
                  refine ⟨7209847138876465745426053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9613129518501954327234737 7209847138876465745426053)
                  ·
                    refine ⟨1351846338539337327267385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7209847138876465745426053 1351846338539337327267385)
                    ·
                      rfl

theorem cell22_3949067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 4].length) (baseStart_3949067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949067 prefixEnd_3949067 := by exact prefixLift 3949067
  have htrace : WordTrace (prefixWord ++ tailWord_3949067) baseStart_3949067 baseEnd_3949067 := by
    simpa [prefixWord, tailWord_3949067, baseEnd_3949067] using wordTrace_append hprefix tailTrace_3949067
  have hstable : (prefixWord ++ tailWord_3949067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949067).length < 2 ^ (prefixWord ++ tailWord_3949067).sum := by decide
  have hdescent : baseEnd_3949067 < baseStart_3949067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949069 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3949069 : Nat := 118140960795 + 3949069 * 2 ^ 59
def prefixEnd_3949069 : Nat := 4983230072969 + 3 ^ 40 * 3949069 * 2
def baseEnd_3949069 : Nat := 1351847023180209988717379

theorem tailTrace_3949069 : CollatzResearch.WordTrace tailWord_3949069 prefixEnd_3949069 1351847023180209988717379 := by
  unfold tailWord_3949069
  simp only [CollatzResearch.WordTrace]
  refine ⟨144034379330204935134818261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96022919553469956756545507 144034379330204935134818261)
  ·
    refine ⟨3375805765551678167222303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 144034379330204935134818261 3375805765551678167222303)
    ·
      refine ⟨5063708648327517250833455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375805765551678167222303 5063708648327517250833455)
      ·
        refine ⟨7595562972491275876250183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063708648327517250833455 7595562972491275876250183)
        ·
          refine ⟨11393344458736913814375275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7595562972491275876250183 11393344458736913814375275)
          ·
            refine ⟨17090016688105370721562913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11393344458736913814375275 17090016688105370721562913)
            ·
              refine ⟨12817512516079028041172185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17090016688105370721562913 12817512516079028041172185)
              ·
                refine ⟨9613134387059271030879139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12817512516079028041172185 9613134387059271030879139)
                ·
                  refine ⟨14419701580588906546318709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9613134387059271030879139 14419701580588906546318709)
                  ·
                    refine ⟨1351847023180209988717379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14419701580588906546318709 1351847023180209988717379)
                    ·
                      rfl

theorem cell22_3949069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3949069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949069 prefixEnd_3949069 := by exact prefixLift 3949069
  have htrace : WordTrace (prefixWord ++ tailWord_3949069) baseStart_3949069 baseEnd_3949069 := by
    simpa [prefixWord, tailWord_3949069, baseEnd_3949069] using wordTrace_append hprefix tailTrace_3949069
  have hstable : (prefixWord ++ tailWord_3949069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949069).length < 2 ^ (prefixWord ++ tailWord_3949069).sum := by decide
  have hdescent : baseEnd_3949069 < baseStart_3949069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949123 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 2, 8]
def baseStart_3949123 : Nat := 118140960795 + 3949123 * 2 ^ 59
def prefixEnd_3949123 : Nat := 4983230072969 + 3 ^ 40 * 3949123 * 2
def baseEnd_3949123 : Nat := 1351865508483771847867213

theorem tailTrace_3949123 : CollatzResearch.WordTrace tailWord_3949123 prefixEnd_3949123 1351865508483771847867213 := by
  unfold tailWord_3949123
  simp only [CollatzResearch.WordTrace]
  refine ⟨144036348872009302357284023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96024232581339534904856015 144036348872009302357284023)
  ·
    refine ⟨216054523308013953535926035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144036348872009302357284023 216054523308013953535926035)
    ·
      refine ⟨324081784962020930303889053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216054523308013953535926035 324081784962020930303889053)
      ·
        refine ⟨121530669360757848863958395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324081784962020930303889053 121530669360757848863958395)
        ·
          refine ⟨182296004041136773295937593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121530669360757848863958395 182296004041136773295937593)
          ·
            refine ⟨136722003030852579971953195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182296004041136773295937593 136722003030852579971953195)
            ·
              refine ⟨205083004546278869957929793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136722003030852579971953195 205083004546278869957929793)
              ·
                refine ⟨153812253409709152468447345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205083004546278869957929793 153812253409709152468447345)
                ·
                  refine ⟨115359190057281864351335509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153812253409709152468447345 115359190057281864351335509)
                  ·
                    refine ⟨1351865508483771847867213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115359190057281864351335509 1351865508483771847867213)
                    ·
                      rfl

theorem cell22_3949123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_3949123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949123 prefixEnd_3949123 := by exact prefixLift 3949123
  have htrace : WordTrace (prefixWord ++ tailWord_3949123) baseStart_3949123 baseEnd_3949123 := by
    simpa [prefixWord, tailWord_3949123, baseEnd_3949123] using wordTrace_append hprefix tailTrace_3949123
  have hstable : (prefixWord ++ tailWord_3949123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949123).length < 2 ^ (prefixWord ++ tailWord_3949123).sum := by decide
  have hdescent : baseEnd_3949123 < baseStart_3949123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949148 : List Nat := [2, 2, 4, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3949148 : Nat := 118140960795 + 3949148 * 2 ^ 59
def prefixEnd_3949148 : Nat := 4983230072969 + 3 ^ 40 * 3949148 * 2
def baseEnd_3949148 : Nat := 1351874066494680115992137

theorem tailTrace_3949148 : CollatzResearch.WordTrace tailWord_3949148 prefixEnd_3949148 1351874066494680115992137 := by
  unfold tailWord_3949148
  simp only [CollatzResearch.WordTrace]
  refine ⟨72018630348459365813472049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96024840464612487751296065 72018630348459365813472049)
  ·
    refine ⟨54013972761344524360104037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72018630348459365813472049 54013972761344524360104037)
    ·
      refine ⟨10127619892752098317519507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54013972761344524360104037 10127619892752098317519507)
      ·
        refine ⟨15191429839128147476279261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10127619892752098317519507 15191429839128147476279261)
        ·
          refine ⟨5696786189673055303604723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15191429839128147476279261 5696786189673055303604723)
          ·
            refine ⟨8545179284509582955407085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696786189673055303604723 8545179284509582955407085)
            ·
              refine ⟨3204442231691093608277657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8545179284509582955407085 3204442231691093608277657)
              ·
                refine ⟨2403331673768320206208243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3204442231691093608277657 2403331673768320206208243)
                ·
                  refine ⟨3604997510652480309312365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403331673768320206208243 3604997510652480309312365)
                  ·
                    refine ⟨1351874066494680115992137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604997510652480309312365 1351874066494680115992137)
                    ·
                      rfl

theorem cell22_3949148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3949148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949148 prefixEnd_3949148 := by exact prefixLift 3949148
  have htrace : WordTrace (prefixWord ++ tailWord_3949148) baseStart_3949148 baseEnd_3949148 := by
    simpa [prefixWord, tailWord_3949148, baseEnd_3949148] using wordTrace_append hprefix tailTrace_3949148
  have hstable : (prefixWord ++ tailWord_3949148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949148).length < 2 ^ (prefixWord ++ tailWord_3949148).sum := by decide
  have hdescent : baseEnd_3949148 < baseStart_3949148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949174 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_3949174 : Nat := 118140960795 + 3949174 * 2 ^ 59
def prefixEnd_3949174 : Nat := 4983230072969 + 3 ^ 40 * 3949174 * 2
def baseEnd_3949174 : Nat := 1351882966826024714842057

theorem tailTrace_3949174 : CollatzResearch.WordTrace tailWord_3949174 prefixEnd_3949174 1351882966826024714842057 := by
  unfold tailWord_3949174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9002388062176533629211911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96025472663216358711593717 9002388062176533629211911)
  ·
    refine ⟨13503582093264800443817867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9002388062176533629211911 13503582093264800443817867)
    ·
      refine ⟨20255373139897200665726801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13503582093264800443817867 20255373139897200665726801)
      ·
        refine ⟨15191529854922900499295101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20255373139897200665726801 15191529854922900499295101)
        ·
          refine ⟨5696823695596087687235663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15191529854922900499295101 5696823695596087687235663)
          ·
            refine ⟨8545235543394131530853495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696823695596087687235663 8545235543394131530853495)
            ·
              refine ⟨12817853315091197296280243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8545235543394131530853495 12817853315091197296280243)
              ·
                refine ⟨19226779972636795944420365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12817853315091197296280243 19226779972636795944420365)
                ·
                  refine ⟨7210042489738798479157637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19226779972636795944420365 7210042489738798479157637)
                  ·
                    refine ⟨1351882966826024714842057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7210042489738798479157637 1351882966826024714842057)
                    ·
                      rfl

theorem cell22_3949174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_3949174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949174 prefixEnd_3949174 := by exact prefixLift 3949174
  have htrace : WordTrace (prefixWord ++ tailWord_3949174) baseStart_3949174 baseEnd_3949174 := by
    simpa [prefixWord, tailWord_3949174, baseEnd_3949174] using wordTrace_append hprefix tailTrace_3949174
  have hstable : (prefixWord ++ tailWord_3949174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949174).length < 2 ^ (prefixWord ++ tailWord_3949174).sum := by decide
  have hdescent : baseEnd_3949174 < baseStart_3949174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949262 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_3949262 : Nat := 118140960795 + 3949262 * 2 ^ 59
def prefixEnd_3949262 : Nat := 4983230072969 + 3 ^ 40 * 3949262 * 2
def baseEnd_3949262 : Nat := 450637697008140606213929

theorem tailTrace_3949262 : CollatzResearch.WordTrace tailWord_3949262 prefixEnd_3949262 450637697008140606213929 := by
  unfold tailWord_3949262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18005177327313216137074255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96027612412337152731062693 18005177327313216137074255)
  ·
    refine ⟨27007765990969824205611383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18005177327313216137074255 27007765990969824205611383)
    ·
      refine ⟨40511648986454736308417075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27007765990969824205611383 40511648986454736308417075)
      ·
        refine ⟨60767473479682104462625613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40511648986454736308417075 60767473479682104462625613)
        ·
          refine ⟨22787802554880789173484605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60767473479682104462625613 22787802554880789173484605)
          ·
            refine ⟨8545425958080295940056727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22787802554880789173484605 8545425958080295940056727)
            ·
              refine ⟨12818138937120443910085091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8545425958080295940056727 12818138937120443910085091)
              ·
                refine ⟨19227208405680665865127637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12818138937120443910085091 19227208405680665865127637)
                ·
                  refine ⟨450637697008140606213929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19227208405680665865127637 450637697008140606213929)
                  ·
                    rfl

theorem cell22_3949262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_3949262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949262 prefixEnd_3949262 := by exact prefixLift 3949262
  have htrace : WordTrace (prefixWord ++ tailWord_3949262) baseStart_3949262 baseEnd_3949262 := by
    simpa [prefixWord, tailWord_3949262, baseEnd_3949262] using wordTrace_append hprefix tailTrace_3949262
  have hstable : (prefixWord ++ tailWord_3949262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949262).length < 2 ^ (prefixWord ++ tailWord_3949262).sum := by decide
  have hdescent : baseEnd_3949262 < baseStart_3949262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949266 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_3949266 : Nat := 118140960795 + 3949266 * 2 ^ 59
def prefixEnd_3949266 : Nat := 4983230072969 + 3 ^ 40 * 3949266 * 2
def baseEnd_3949266 : Nat := 1351914460306167141541775

theorem tailTrace_3949266 : CollatzResearch.WordTrace tailWord_3949266 prefixEnd_3949266 1351914460306167141541775 := by
  unfold tailWord_3949266
  simp only [CollatzResearch.WordTrace]
  refine ⟨36010391127622809444934913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96027709673660825186493101 36010391127622809444934913)
  ·
    refine ⟨27007793345717107083701185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36010391127622809444934913 27007793345717107083701185)
    ·
      refine ⟨20255845009287830312775889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27007793345717107083701185 20255845009287830312775889)
      ·
        refine ⟨15191883756965872734581917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20255845009287830312775889 15191883756965872734581917)
        ·
          refine ⟨5696956408862202275468219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15191883756965872734581917 5696956408862202275468219)
          ·
            refine ⟨8545434613293303413202329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696956408862202275468219 8545434613293303413202329)
            ·
              refine ⟨6409075959969977559901747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8545434613293303413202329 6409075959969977559901747)
              ·
                refine ⟨9613613939954966339852621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6409075959969977559901747 9613613939954966339852621)
                ·
                  refine ⟨3605105227483112377444733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9613613939954966339852621 3605105227483112377444733)
                  ·
                    refine ⟨1351914460306167141541775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3605105227483112377444733 1351914460306167141541775)
                    ·
                      rfl

theorem cell22_3949266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_3949266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949266 prefixEnd_3949266 := by exact prefixLift 3949266
  have htrace : WordTrace (prefixWord ++ tailWord_3949266) baseStart_3949266 baseEnd_3949266 := by
    simpa [prefixWord, tailWord_3949266, baseEnd_3949266] using wordTrace_append hprefix tailTrace_3949266
  have hstable : (prefixWord ++ tailWord_3949266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949266).length < 2 ^ (prefixWord ++ tailWord_3949266).sum := by decide
  have hdescent : baseEnd_3949266 < baseStart_3949266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949279 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 5]
def baseStart_3949279 : Nat := 118140960795 + 3949279 * 2 ^ 59
def prefixEnd_3949279 : Nat := 4983230072969 + 3 ^ 40 * 3949279 * 2
def baseEnd_3949279 : Nat := 450639636823946480322245

theorem tailTrace_3949279 : CollatzResearch.WordTrace tailWord_3949279 prefixEnd_3949279 450639636823946480322245 := by
  unfold tailWord_3949279
  simp only [CollatzResearch.WordTrace]
  refine ⟨144042038659444140999962891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96028025772962760666641927 144042038659444140999962891)
  ·
    refine ⟨216063057989166211499944337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144042038659444140999962891 216063057989166211499944337)
    ·
      refine ⟨162047293491874658624958253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216063057989166211499944337 162047293491874658624958253)
      ·
        refine ⟨60767735059452996984359345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162047293491874658624958253 60767735059452996984359345)
        ·
          refine ⟨45575801294589747738269509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60767735059452996984359345 45575801294589747738269509)
          ·
            refine ⟨8545462742735577700925533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45575801294589747738269509 8545462742735577700925533)
            ·
              refine ⟨3204548528525841637847075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8545462742735577700925533 3204548528525841637847075)
              ·
                refine ⟨4806822792788762456770613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204548528525841637847075 4806822792788762456770613)
                ·
                  refine ⟨450639636823946480322245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4806822792788762456770613 450639636823946480322245)
                  ·
                    rfl

theorem cell22_3949279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 5].length) (baseStart_3949279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949279 prefixEnd_3949279 := by exact prefixLift 3949279
  have htrace : WordTrace (prefixWord ++ tailWord_3949279) baseStart_3949279 baseEnd_3949279 := by
    simpa [prefixWord, tailWord_3949279, baseEnd_3949279] using wordTrace_append hprefix tailTrace_3949279
  have hstable : (prefixWord ++ tailWord_3949279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949279).length < 2 ^ (prefixWord ++ tailWord_3949279).sum := by decide
  have hdescent : baseEnd_3949279 < baseStart_3949279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949330 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_3949330 : Nat := 118140960795 + 3949330 * 2 ^ 59
def prefixEnd_3949330 : Nat := 4983230072969 + 3 ^ 40 * 3949330 * 2
def baseEnd_3949330 : Nat := 450645456271364102647193

theorem tailTrace_3949330 : CollatzResearch.WordTrace tailWord_3949330 prefixEnd_3949330 450645456271364102647193 := by
  unfold tailWord_3949330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36010974695564844177517361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96029265854839584473379629 36010974695564844177517361)
  ·
    refine ⟨27008231021673633133138021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36010974695564844177517361 27008231021673633133138021)
    ·
      refine ⟨5064043316563806212463379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27008231021673633133138021 5064043316563806212463379)
      ·
        refine ⟨7596064974845709318695069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064043316563806212463379 7596064974845709318695069)
        ·
          refine ⟨2848524365567140994510651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7596064974845709318695069 2848524365567140994510651)
          ·
            refine ⟨4272786548350711491765977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848524365567140994510651 4272786548350711491765977)
            ·
              refine ⟨3204589911263033618824483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4272786548350711491765977 3204589911263033618824483)
              ·
                refine ⟨4806884866894550428236725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204589911263033618824483 4806884866894550428236725)
                ·
                  refine ⟨450645456271364102647193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4806884866894550428236725 450645456271364102647193)
                  ·
                    rfl

theorem cell22_3949330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_3949330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949330 prefixEnd_3949330 := by exact prefixLift 3949330
  have htrace : WordTrace (prefixWord ++ tailWord_3949330) baseStart_3949330 baseEnd_3949330 := by
    simpa [prefixWord, tailWord_3949330, baseEnd_3949330] using wordTrace_append hprefix tailTrace_3949330
  have hstable : (prefixWord ++ tailWord_3949330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949330).length < 2 ^ (prefixWord ++ tailWord_3949330).sum := by decide
  have hdescent : baseEnd_3949330 < baseStart_3949330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949352 : List Nat := [2, 1, 5, 1, 1, 1, 1, 10]
def baseStart_3949352 : Nat := 118140960795 + 3949352 * 2 ^ 59
def prefixEnd_3949352 : Nat := 4983230072969 + 3 ^ 40 * 3949352 * 2
def baseEnd_3949352 : Nat := 150215988873743509321279

theorem tailTrace_3949352 : CollatzResearch.WordTrace tailWord_3949352 prefixEnd_3949352 150215988873743509321279 := by
  unfold tailWord_3949352
  simp only [CollatzResearch.WordTrace]
  refine ⟨72022350594089837233685155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96029800792119782978246873 72022350594089837233685155)
  ·
    refine ⟨108033525891134755850527733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72022350594089837233685155 108033525891134755850527733)
    ·
      refine ⟨10128143052293883360986975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108033525891134755850527733 10128143052293883360986975)
      ·
        refine ⟨15192214578440825041480463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10128143052293883360986975 15192214578440825041480463)
        ·
          refine ⟨22788321867661237562220695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15192214578440825041480463 22788321867661237562220695)
          ·
            refine ⟨34182482801491856343331043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22788321867661237562220695 34182482801491856343331043)
            ·
              refine ⟨51273724202237784514996565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34182482801491856343331043 51273724202237784514996565)
              ·
                refine ⟨150215988873743509321279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51273724202237784514996565 150215988873743509321279)
                ·
                  rfl

theorem cell22_3949352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 10].length) (baseStart_3949352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949352 prefixEnd_3949352 := by exact prefixLift 3949352
  have htrace : WordTrace (prefixWord ++ tailWord_3949352) baseStart_3949352 baseEnd_3949352 := by
    simpa [prefixWord, tailWord_3949352, baseEnd_3949352] using wordTrace_append hprefix tailTrace_3949352
  have hstable : (prefixWord ++ tailWord_3949352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949352).length < 2 ^ (prefixWord ++ tailWord_3949352).sum := by decide
  have hdescent : baseEnd_3949352 < baseStart_3949352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949373 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_3949373 : Nat := 118140960795 + 3949373 * 2 ^ 59
def prefixEnd_3949373 : Nat := 4983230072969 + 3 ^ 40 * 3949373 * 2
def baseEnd_3949373 : Nat := 1351951088592854529116447

theorem tailTrace_3949373 : CollatzResearch.WordTrace tailWord_3949373 prefixEnd_3949373 1351951088592854529116447 := by
  unfold tailWord_3949373
  simp only [CollatzResearch.WordTrace]
  refine ⟨144045467121103595053884773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96030311414069063369256515 144045467121103595053884773)
  ·
    refine ⟨27008525085206924072603395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144045467121103595053884773 27008525085206924072603395)
    ·
      refine ⟨40512787627810386108905093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27008525085206924072603395 40512787627810386108905093)
      ·
        refine ⟨7596147680214447395419705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40512787627810386108905093 7596147680214447395419705)
        ·
          refine ⟨5697110760160835546564779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7596147680214447395419705 5697110760160835546564779)
          ·
            refine ⟨8545666140241253319847169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5697110760160835546564779 8545666140241253319847169)
            ·
              refine ⟨6409249605180939989885377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8545666140241253319847169 6409249605180939989885377)
              ·
                refine ⟨4806937203885704992414033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6409249605180939989885377 4806937203885704992414033)
                ·
                  refine ⟨3605202902914278744310525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4806937203885704992414033 3605202902914278744310525)
                  ·
                    refine ⟨1351951088592854529116447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3605202902914278744310525 1351951088592854529116447)
                    ·
                      rfl

theorem cell22_3949373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_3949373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949373 prefixEnd_3949373 := by exact prefixLift 3949373
  have htrace : WordTrace (prefixWord ++ tailWord_3949373) baseStart_3949373 baseEnd_3949373 := by
    simpa [prefixWord, tailWord_3949373, baseEnd_3949373] using wordTrace_append hprefix tailTrace_3949373
  have hstable : (prefixWord ++ tailWord_3949373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949373).length < 2 ^ (prefixWord ++ tailWord_3949373).sum := by decide
  have hdescent : baseEnd_3949373 < baseStart_3949373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949384 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 3, 3]
def baseStart_3949384 : Nat := 118140960795 + 3949384 * 2 ^ 59
def prefixEnd_3949384 : Nat := 4983230072969 + 3 ^ 40 * 3949384 * 2
def baseEnd_3949384 : Nat := 1351954854117654167091413

theorem tailTrace_3949384 : CollatzResearch.WordTrace tailWord_3949384 prefixEnd_3949384 1351954854117654167091413 := by
  unfold tailWord_3949384
  simp only [CollatzResearch.WordTrace]
  refine ⟨72022934162031871966267603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96030578882709162621690137 72022934162031871966267603)
  ·
    refine ⟨108034401243047807949401405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72022934162031871966267603 108034401243047807949401405)
    ·
      refine ⟨40512900466142927981025527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108034401243047807949401405 40512900466142927981025527)
      ·
        refine ⟨60769350699214391971538291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40512900466142927981025527 60769350699214391971538291)
        ·
          refine ⟨91154026048821587957307437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60769350699214391971538291 91154026048821587957307437)
          ·
            refine ⟨34182759768308095483990289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91154026048821587957307437 34182759768308095483990289)
            ·
              refine ⟨25637069826231071612992717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34182759768308095483990289 25637069826231071612992717)
              ·
                refine ⟨9613901184836651854872269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25637069826231071612992717 9613901184836651854872269)
                ·
                  refine ⟨3605212944313744445577101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9613901184836651854872269 3605212944313744445577101)
                  ·
                    refine ⟨1351954854117654167091413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3605212944313744445577101 1351954854117654167091413)
                    ·
                      rfl

theorem cell22_3949384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_3949384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949384 prefixEnd_3949384 := by exact prefixLift 3949384
  have htrace : WordTrace (prefixWord ++ tailWord_3949384) baseStart_3949384 baseEnd_3949384 := by
    simpa [prefixWord, tailWord_3949384, baseEnd_3949384] using wordTrace_append hprefix tailTrace_3949384
  have hstable : (prefixWord ++ tailWord_3949384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949384).length < 2 ^ (prefixWord ++ tailWord_3949384).sum := by decide
  have hdescent : baseEnd_3949384 < baseStart_3949384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949429 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3949429 : Nat := 118140960795 + 3949429 * 2 ^ 59
def prefixEnd_3949429 : Nat := 4983230072969 + 3 ^ 40 * 3949429 * 2
def baseEnd_3949429 : Nat := 1351970258537289049716275

theorem tailTrace_3949429 : CollatzResearch.WordTrace tailWord_3949429 prefixEnd_3949429 1351970258537289049716275 := by
  unfold tailWord_3949429
  simp only [CollatzResearch.WordTrace]
  refine ⟨144047509608900716617923341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96031673072600477745282227 144047509608900716617923341)
  ·
    refine ⟨54017816103337768731721253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144047509608900716617923341 54017816103337768731721253)
    ·
      refine ⟨10128340519375831637197735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54017816103337768731721253 10128340519375831637197735)
      ·
        refine ⟨15192510779063747455796603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10128340519375831637197735 15192510779063747455796603)
        ·
          refine ⟨22788766168595621183694905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15192510779063747455796603 22788766168595621183694905)
          ·
            refine ⟨17091574626446715887771179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22788766168595621183694905 17091574626446715887771179)
            ·
              refine ⟨25637361939670073831656769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17091574626446715887771179 25637361939670073831656769)
              ·
                refine ⟨19228021454752555373742577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25637361939670073831656769 19228021454752555373742577)
                ·
                  refine ⟨14421016091064416530306933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19228021454752555373742577 14421016091064416530306933)
                  ·
                    refine ⟨1351970258537289049716275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14421016091064416530306933 1351970258537289049716275)
                    ·
                      rfl

theorem cell22_3949429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3949429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949429 prefixEnd_3949429 := by exact prefixLift 3949429
  have htrace : WordTrace (prefixWord ++ tailWord_3949429) baseStart_3949429 baseEnd_3949429 := by
    simpa [prefixWord, tailWord_3949429, baseEnd_3949429] using wordTrace_append hprefix tailTrace_3949429
  have hstable : (prefixWord ++ tailWord_3949429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949429).length < 2 ^ (prefixWord ++ tailWord_3949429).sum := by decide
  have hdescent : baseEnd_3949429 < baseStart_3949429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949461 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_3949461 : Nat := 118140960795 + 3949461 * 2 ^ 59
def prefixEnd_3949461 : Nat := 4983230072969 + 3 ^ 40 * 3949461 * 2
def baseEnd_3949461 : Nat := 1351981212791251632916177

theorem tailTrace_3949461 : CollatzResearch.WordTrace tailWord_3949461 prefixEnd_3949461 1351981212791251632916177 := by
  unfold tailWord_3949461
  simp only [CollatzResearch.WordTrace]
  refine ⟨144048676744784786083088237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96032451163189857388725491 144048676744784786083088237)
  ·
    refine ⟨54018253779294294781158089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144048676744784786083088237 54018253779294294781158089)
    ·
      refine ⟨40513690334470721085868567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54018253779294294781158089 40513690334470721085868567)
      ·
        refine ⟨60770535501706081628802851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40513690334470721085868567 60770535501706081628802851)
        ·
          refine ⟨91155803252559122443204277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60770535501706081628802851 91155803252559122443204277)
          ·
            refine ⟨8545856554927417729050401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91155803252559122443204277 8545856554927417729050401)
            ·
              refine ⟨6409392416195563296787801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8545856554927417729050401 6409392416195563296787801)
              ·
                refine ⟨4807044312146672472590851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6409392416195563296787801 4807044312146672472590851)
                ·
                  refine ⟨7210566468220008708886277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807044312146672472590851 7210566468220008708886277)
                  ·
                    refine ⟨1351981212791251632916177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7210566468220008708886277 1351981212791251632916177)
                    ·
                      rfl

theorem cell22_3949461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_3949461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949461 prefixEnd_3949461 := by exact prefixLift 3949461
  have htrace : WordTrace (prefixWord ++ tailWord_3949461) baseStart_3949461 baseEnd_3949461 := by
    simpa [prefixWord, tailWord_3949461, baseEnd_3949461] using wordTrace_append hprefix tailTrace_3949461
  have hstable : (prefixWord ++ tailWord_3949461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949461).length < 2 ^ (prefixWord ++ tailWord_3949461).sum := by decide
  have hdescent : baseEnd_3949461 < baseStart_3949461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949493 : List Nat := [1, 3, 3, 2, 1, 1, 5, 2, 4]
def baseStart_3949493 : Nat := 118140960795 + 3949493 * 2 ^ 59
def prefixEnd_3949493 : Nat := 4983230072969 + 3 ^ 40 * 3949493 * 2
def baseEnd_3949493 : Nat := 450664055681738072038693

theorem tailTrace_3949493 : CollatzResearch.WordTrace tailWord_3949493 prefixEnd_3949493 450664055681738072038693 := by
  unfold tailWord_3949493
  simp only [CollatzResearch.WordTrace]
  refine ⟨144049843880668855548253133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96033229253779237032168755 144049843880668855548253133)
  ·
    refine ⟨54018691455250820830594925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144049843880668855548253133 54018691455250820830594925)
    ·
      refine ⟨20257009295719057811473097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54018691455250820830594925 20257009295719057811473097)
      ·
        refine ⟨15192756971789293358604823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20257009295719057811473097 15192756971789293358604823)
        ·
          refine ⟨22789135457683940037907235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15192756971789293358604823 22789135457683940037907235)
          ·
            refine ⟨34183703186525910056860853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22789135457683940037907235 34183703186525910056860853)
            ·
              refine ⟨3204722173736804067830705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34183703186525910056860853 3204722173736804067830705)
              ·
                refine ⟨2403541630302603050873029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3204722173736804067830705 2403541630302603050873029)
                ·
                  refine ⟨450664055681738072038693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403541630302603050873029 450664055681738072038693)
                  ·
                    rfl

theorem cell22_3949493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_3949493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949493 prefixEnd_3949493 := by exact prefixLift 3949493
  have htrace : WordTrace (prefixWord ++ tailWord_3949493) baseStart_3949493 baseEnd_3949493 := by
    simpa [prefixWord, tailWord_3949493, baseEnd_3949493] using wordTrace_append hprefix tailTrace_3949493
  have hstable : (prefixWord ++ tailWord_3949493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949493).length < 2 ^ (prefixWord ++ tailWord_3949493).sum := by decide
  have hdescent : baseEnd_3949493 < baseStart_3949493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949504 : List Nat := [2, 1, 1, 2, 3, 4, 2, 7]
def baseStart_3949504 : Nat := 118140960795 + 3949504 * 2 ^ 59
def prefixEnd_3949504 : Nat := 4983230072969 + 3 ^ 40 * 3949504 * 2
def baseEnd_3949504 : Nat := 150221770285557094899005

theorem tailTrace_3949504 : CollatzResearch.WordTrace tailWord_3949504 prefixEnd_3949504 150221770285557094899005 := by
  unfold tailWord_3949504
  simp only [CollatzResearch.WordTrace]
  refine ⟨72025122541814502213451783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96033496722419336284602377 72025122541814502213451783)
  ·
    refine ⟨108037683812721753320177675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72025122541814502213451783 108037683812721753320177675)
    ·
      refine ⟨162056525719082629980266513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108037683812721753320177675 162056525719082629980266513)
      ·
        refine ⟨121542394289311972485199885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162056525719082629980266513 121542394289311972485199885)
        ·
          refine ⟨45578397858491989681949957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121542394289311972485199885 45578397858491989681949957)
          ·
            refine ⟨8545949598467248065365617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45578397858491989681949957 8545949598467248065365617)
            ·
              refine ⟨6409462198850436049024213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8545949598467248065365617 6409462198850436049024213)
              ·
                refine ⟨150221770285557094899005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6409462198850436049024213 150221770285557094899005)
                ·
                  rfl

theorem cell22_3949504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 7].length) (baseStart_3949504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949504 prefixEnd_3949504 := by exact prefixLift 3949504
  have htrace : WordTrace (prefixWord ++ tailWord_3949504) baseStart_3949504 baseEnd_3949504 := by
    simpa [prefixWord, tailWord_3949504, baseEnd_3949504] using wordTrace_append hprefix tailTrace_3949504
  have hstable : (prefixWord ++ tailWord_3949504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949504).length < 2 ^ (prefixWord ++ tailWord_3949504).sum := by decide
  have hdescent : baseEnd_3949504 < baseStart_3949504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949564 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_3949564 : Nat := 118140960795 + 3949564 * 2 ^ 59
def prefixEnd_3949564 : Nat := 4983230072969 + 3 ^ 40 * 3949564 * 2
def baseEnd_3949564 : Nat := 1352016471796193697590861

theorem tailTrace_3949564 : CollatzResearch.WordTrace tailWord_3949564 prefixEnd_3949564 1352016471796193697590861 := by
  unfold tailWord_3949564
  simp only [CollatzResearch.WordTrace]
  refine ⟨72026216731705817337043873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96034955642274423116058497 72026216731705817337043873)
  ·
    refine ⟨54019662548779363002782905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72026216731705817337043873 54019662548779363002782905)
    ·
      refine ⟨40514746911584522252087179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54019662548779363002782905 40514746911584522252087179)
      ·
        refine ⟨60772120367376783378130769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40514746911584522252087179 60772120367376783378130769)
        ·
          refine ⟨45579090275532587533598077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60772120367376783378130769 45579090275532587533598077)
          ·
            refine ⟨17092158853324720325099279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45579090275532587533598077 17092158853324720325099279)
            ·
              refine ⟨25638238279987080487648919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17092158853324720325099279 25638238279987080487648919)
              ·
                refine ⟨38457357419980620731473379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25638238279987080487648919 38457357419980620731473379)
                ·
                  refine ⟨57686036129970931097210069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38457357419980620731473379 57686036129970931097210069)
                  ·
                    refine ⟨1352016471796193697590861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57686036129970931097210069 1352016471796193697590861)
                    ·
                      rfl

theorem cell22_3949564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_3949564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949564 prefixEnd_3949564 := by exact prefixLift 3949564
  have htrace : WordTrace (prefixWord ++ tailWord_3949564) baseStart_3949564 baseEnd_3949564 := by
    simpa [prefixWord, tailWord_3949564, baseEnd_3949564] using wordTrace_append hprefix tailTrace_3949564
  have hstable : (prefixWord ++ tailWord_3949564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949564).length < 2 ^ (prefixWord ++ tailWord_3949564).sum := by decide
  have hdescent : baseEnd_3949564 < baseStart_3949564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949594 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_3949594 : Nat := 118140960795 + 3949594 * 2 ^ 59
def prefixEnd_3949594 : Nat := 4983230072969 + 3 ^ 40 * 3949594 * 2
def baseEnd_3949594 : Nat := 450675580469761206446923

theorem tailTrace_3949594 : CollatzResearch.WordTrace tailWord_3949594 prefixEnd_3949594 450675580469761206446923 := by
  unfold tailWord_3949594
  simp only [CollatzResearch.WordTrace]
  refine ⟨36013381913325737449419959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96035685102201966531786557 36013381913325737449419959)
  ·
    refine ⟨54020072869988606174129939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36013381913325737449419959 54020072869988606174129939)
    ·
      refine ⟨81030109304982909261194909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54020072869988606174129939 81030109304982909261194909)
      ·
        refine ⟨30386290989368590972948091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81030109304982909261194909 30386290989368590972948091)
        ·
          refine ⟨45579436484052886459422137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30386290989368590972948091 45579436484052886459422137)
          ·
            refine ⟨34184577363039664844566603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45579436484052886459422137 34184577363039664844566603)
            ·
              refine ⟨51276866044559497266849905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34184577363039664844566603 51276866044559497266849905)
              ·
                refine ⟨38457649533419622950137429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51276866044559497266849905 38457649533419622950137429)
                ·
                  refine ⟨450675580469761206446923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38457649533419622950137429 450675580469761206446923)
                  ·
                    rfl

theorem cell22_3949594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_3949594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949594 prefixEnd_3949594 := by exact prefixLift 3949594
  have htrace : WordTrace (prefixWord ++ tailWord_3949594) baseStart_3949594 baseEnd_3949594 := by
    simpa [prefixWord, tailWord_3949594, baseEnd_3949594] using wordTrace_append hprefix tailTrace_3949594
  have hstable : (prefixWord ++ tailWord_3949594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949594).length < 2 ^ (prefixWord ++ tailWord_3949594).sum := by decide
  have hdescent : baseEnd_3949594 < baseStart_3949594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949600 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 5]
def baseStart_3949600 : Nat := 118140960795 + 3949600 * 2 ^ 59
def prefixEnd_3949600 : Nat := 4983230072969 + 3 ^ 40 * 3949600 * 2
def baseEnd_3949600 : Nat := 450676265110633867896917

theorem tailTrace_3949600 : CollatzResearch.WordTrace tailWord_3949600 prefixEnd_3949600 450676265110633867896917 := by
  unfold tailWord_3949600
  simp only [CollatzResearch.WordTrace]
  refine ⟨72026873245640606411199127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96035830994187475214932169 72026873245640606411199127)
  ·
    refine ⟨108040309868460909616798691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72026873245640606411199127 108040309868460909616798691)
    ·
      refine ⟨162060464802691364425198037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108040309868460909616798691 162060464802691364425198037)
      ·
        refine ⟨3798292143813078853715579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 162060464802691364425198037 3798292143813078853715579)
        ·
          refine ⟨5697438215719618280573369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3798292143813078853715579 5697438215719618280573369)
          ·
            refine ⟨4273078661789713710430027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5697438215719618280573369 4273078661789713710430027)
            ·
              refine ⟨6409617992684570565645041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273078661789713710430027 6409617992684570565645041)
              ·
                refine ⟨4807213494513427924233781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6409617992684570565645041 4807213494513427924233781)
                ·
                  refine ⟨450676265110633867896917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4807213494513427924233781 450676265110633867896917)
                  ·
                    rfl

theorem cell22_3949600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 5].length) (baseStart_3949600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949600 prefixEnd_3949600 := by exact prefixLift 3949600
  have htrace : WordTrace (prefixWord ++ tailWord_3949600) baseStart_3949600 baseEnd_3949600 := by
    simpa [prefixWord, tailWord_3949600, baseEnd_3949600] using wordTrace_append hprefix tailTrace_3949600
  have hstable : (prefixWord ++ tailWord_3949600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949600).length < 2 ^ (prefixWord ++ tailWord_3949600).sum := by decide
  have hdescent : baseEnd_3949600 < baseStart_3949600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949611 : List Nat := [1, 1, 1, 1, 2, 1, 5, 6, 4]
def baseStart_3949611 : Nat := 118140960795 + 3949611 * 2 ^ 59
def prefixEnd_3949611 : Nat := 4983230072969 + 3 ^ 40 * 3949611 * 2
def baseEnd_3949611 : Nat := 450677520285567080555239

theorem tailTrace_3949611 : CollatzResearch.WordTrace tailWord_3949611 prefixEnd_3949611 450677520285567080555239 := by
  unfold tailWord_3949611
  simp only [CollatzResearch.WordTrace]
  refine ⟨144054147694241361701048687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96036098462827574467365791 144054147694241361701048687)
  ·
    refine ⟨216081221541362042551573031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144054147694241361701048687 216081221541362042551573031)
    ·
      refine ⟨324121832312043063827359547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216081221541362042551573031 324121832312043063827359547)
      ·
        refine ⟨486182748468064595741039321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324121832312043063827359547 486182748468064595741039321)
        ·
          refine ⟨364637061351048446805779491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486182748468064595741039321 364637061351048446805779491)
          ·
            refine ⟨546955592026572670208669237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364637061351048446805779491 546955592026572670208669237)
            ·
              refine ⟨51277086752491187832062741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 546955592026572670208669237 51277086752491187832062741)
              ·
                refine ⟨2403613441523024429627941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51277086752491187832062741 2403613441523024429627941)
                ·
                  refine ⟨450677520285567080555239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403613441523024429627941 450677520285567080555239)
                  ·
                    rfl

theorem cell22_3949611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 4].length) (baseStart_3949611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949611 prefixEnd_3949611 := by exact prefixLift 3949611
  have htrace : WordTrace (prefixWord ++ tailWord_3949611) baseStart_3949611 baseEnd_3949611 := by
    simpa [prefixWord, tailWord_3949611, baseEnd_3949611] using wordTrace_append hprefix tailTrace_3949611
  have hstable : (prefixWord ++ tailWord_3949611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949611).length < 2 ^ (prefixWord ++ tailWord_3949611).sum := by decide
  have hdescent : baseEnd_3949611 < baseStart_3949611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949626 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_3949626 : Nat := 118140960795 + 3949626 * 2 ^ 59
def prefixEnd_3949626 : Nat := 4983230072969 + 3 ^ 40 * 3949626 * 2
def baseEnd_3949626 : Nat := 1352037695663246202540671

theorem tailTrace_3949626 : CollatzResearch.WordTrace tailWord_3949626 prefixEnd_3949626 1352037695663246202540671 := by
  unfold tailWord_3949626
  simp only [CollatzResearch.WordTrace]
  refine ⟨36013673697296754815711183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96036463192791346175229821 36013673697296754815711183)
  ·
    refine ⟨54020510545945132223566775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36013673697296754815711183 54020510545945132223566775)
    ·
      refine ⟨81030765818917698335350163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54020510545945132223566775 81030765818917698335350163)
      ·
        refine ⟨121546148728376547503025245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81030765818917698335350163 121546148728376547503025245)
        ·
          refine ⟨45579805773141205313634467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121546148728376547503025245 45579805773141205313634467)
          ·
            refine ⟨68369708659711807970451701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45579805773141205313634467 68369708659711807970451701)
            ·
              refine ⟨6409660186847981997229847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68369708659711807970451701 6409660186847981997229847)
              ·
                refine ⟨9614490280271972995844771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6409660186847981997229847 9614490280271972995844771)
                ·
                  refine ⟨14421735420407959493767157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9614490280271972995844771 14421735420407959493767157)
                  ·
                    refine ⟨1352037695663246202540671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14421735420407959493767157 1352037695663246202540671)
                    ·
                      rfl

theorem cell22_3949626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_3949626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949626 prefixEnd_3949626 := by exact prefixLift 3949626
  have htrace : WordTrace (prefixWord ++ tailWord_3949626) baseStart_3949626 baseEnd_3949626 := by
    simpa [prefixWord, tailWord_3949626, baseEnd_3949626] using wordTrace_append hprefix tailTrace_3949626
  have hstable : (prefixWord ++ tailWord_3949626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949626).length < 2 ^ (prefixWord ++ tailWord_3949626).sum := by decide
  have hdescent : baseEnd_3949626 < baseStart_3949626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949630 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3949630 : Nat := 118140960795 + 3949630 * 2 ^ 59
def prefixEnd_3949630 : Nat := 4983230072969 + 3 ^ 40 * 3949630 * 2
def baseEnd_3949630 : Nat := 1352039064944991525440659

theorem tailTrace_3949630 : CollatzResearch.WordTrace tailWord_3949630 prefixEnd_3949630 1352039064944991525440659 := by
  unfold tailWord_3949630
  simp only [CollatzResearch.WordTrace]
  refine ⟨18006855085146565993248793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96036560454115018630660229 18006855085146565993248793)
  ·
    refine ⟨13505141313859924494936595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18006855085146565993248793 13505141313859924494936595)
    ·
      refine ⟨20257711970789886742404893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13505141313859924494936595 20257711970789886742404893)
      ·
        refine ⟨7596641989046207528401835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20257711970789886742404893 7596641989046207528401835)
        ·
          refine ⟨11394962983569311292602753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7596641989046207528401835 11394962983569311292602753)
          ·
            refine ⟨8546222237676983469452065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11394962983569311292602753 8546222237676983469452065)
            ·
              refine ⟨6409666678257737602089049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8546222237676983469452065 6409666678257737602089049)
              ·
                refine ⟨4807250008693303201566787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6409666678257737602089049 4807250008693303201566787)
                ·
                  refine ⟨7210875013039954802350181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807250008693303201566787 7210875013039954802350181)
                  ·
                    refine ⟨1352039064944991525440659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7210875013039954802350181 1352039064944991525440659)
                    ·
                      rfl

theorem cell22_3949630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3949630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949630 prefixEnd_3949630 := by exact prefixLift 3949630
  have htrace : WordTrace (prefixWord ++ tailWord_3949630) baseStart_3949630 baseEnd_3949630 := by
    simpa [prefixWord, tailWord_3949630, baseEnd_3949630] using wordTrace_append hprefix tailTrace_3949630
  have hstable : (prefixWord ++ tailWord_3949630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949630).length < 2 ^ (prefixWord ++ tailWord_3949630).sum := by decide
  have hdescent : baseEnd_3949630 < baseStart_3949630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949645 : List Nat := [1, 6, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3949645 : Nat := 118140960795 + 3949645 * 2 ^ 59
def prefixEnd_3949645 : Nat := 4983230072969 + 3 ^ 40 * 3949645 * 2
def baseEnd_3949645 : Nat := 450681399917178828771871

theorem tailTrace_3949645 : CollatzResearch.WordTrace tailWord_3949645 prefixEnd_3949645 450681399917178828771871 := by
  unfold tailWord_3949645
  simp only [CollatzResearch.WordTrace]
  refine ⟨144055387776118185507786389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96036925184078790338524259 144055387776118185507786389)
  ·
    refine ⟨6752596302005539945677487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144055387776118185507786389 6752596302005539945677487)
    ·
      refine ⟨10128894453008309918516231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6752596302005539945677487 10128894453008309918516231)
      ·
        refine ⟨15193341679512464877774347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10128894453008309918516231 15193341679512464877774347)
        ·
          refine ⟨22790012519268697316661521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15193341679512464877774347 22790012519268697316661521)
          ·
            refine ⟨17092509389451522987496141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22790012519268697316661521 17092509389451522987496141)
            ·
              refine ⟨6409691021044321120311053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17092509389451522987496141 6409691021044321120311053)
              ·
                refine ⟨2403634132891620420116645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6409691021044321120311053 2403634132891620420116645)
                ·
                  refine ⟨450681399917178828771871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403634132891620420116645 450681399917178828771871)
                  ·
                    rfl

theorem cell22_3949645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3949645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949645 prefixEnd_3949645 := by exact prefixLift 3949645
  have htrace : WordTrace (prefixWord ++ tailWord_3949645) baseStart_3949645 baseEnd_3949645 := by
    simpa [prefixWord, tailWord_3949645, baseEnd_3949645] using wordTrace_append hprefix tailTrace_3949645
  have hstable : (prefixWord ++ tailWord_3949645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949645).length < 2 ^ (prefixWord ++ tailWord_3949645).sum := by decide
  have hdescent : baseEnd_3949645 < baseStart_3949645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949662 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3949662 : Nat := 118140960795 + 3949662 * 2 ^ 59
def prefixEnd_3949662 : Nat := 4983230072969 + 3 ^ 40 * 3949662 * 2
def baseEnd_3949662 : Nat := 450683339732984702880187

theorem tailTrace_3949662 : CollatzResearch.WordTrace tailWord_3949662 prefixEnd_3949662 450683339732984702880187 := by
  unfold tailWord_3949662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18007000977132074676394405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96037338544704398274103493 18007000977132074676394405)
  ·
    refine ⟨3376312683212264001823951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18007000977132074676394405 3376312683212264001823951)
    ·
      refine ⟨5064469024818396002735927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3376312683212264001823951 5064469024818396002735927)
      ·
        refine ⟨7596703537227594004103891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064469024818396002735927 7596703537227594004103891)
        ·
          refine ⟨11395055305841391006155837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7596703537227594004103891 11395055305841391006155837)
          ·
            refine ⟨4273145739690521627308439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11395055305841391006155837 4273145739690521627308439)
            ·
              refine ⟨6409718609535782440962659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273145739690521627308439 6409718609535782440962659)
              ·
                refine ⟨9614577914303673661443989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6409718609535782440962659 9614577914303673661443989)
                ·
                  refine ⟨450683339732984702880187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9614577914303673661443989 450683339732984702880187)
                  ·
                    rfl

theorem cell22_3949662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3949662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949662 prefixEnd_3949662 := by exact prefixLift 3949662
  have htrace : WordTrace (prefixWord ++ tailWord_3949662) baseStart_3949662 baseEnd_3949662 := by
    simpa [prefixWord, tailWord_3949662, baseEnd_3949662] using wordTrace_append hprefix tailTrace_3949662
  have hstable : (prefixWord ++ tailWord_3949662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949662).length < 2 ^ (prefixWord ++ tailWord_3949662).sum := by decide
  have hdescent : baseEnd_3949662 < baseStart_3949662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949677 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_3949677 : Nat := 118140960795 + 3949677 * 2 ^ 59
def prefixEnd_3949677 : Nat := 4983230072969 + 3 ^ 40 * 3949677 * 2
def baseEnd_3949677 : Nat := 1352055154005499069515515

theorem tailTrace_3949677 : CollatzResearch.WordTrace tailWord_3949677 prefixEnd_3949677 1352055154005499069515515 := by
  unfold tailWord_3949677
  simp only [CollatzResearch.WordTrace]
  refine ⟨144056554912002254972951285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96037703274668169981967523 144056554912002254972951285)
  ·
    refine ⟨13505302023000211403714183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144056554912002254972951285 13505302023000211403714183)
    ·
      refine ⟨20257953034500317105571275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13505302023000211403714183 20257953034500317105571275)
      ·
        refine ⟨30386929551750475658356913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20257953034500317105571275 30386929551750475658356913)
        ·
          refine ⟨22790197163812856743767685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30386929551750475658356913 22790197163812856743767685)
          ·
            refine ⟨4273161968214910639456441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22790197163812856743767685 4273161968214910639456441)
            ·
              refine ⟨3204871476161182979592331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4273161968214910639456441 3204871476161182979592331)
              ·
                refine ⟨4807307214241774469388497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204871476161182979592331 4807307214241774469388497)
                ·
                  refine ⟨3605480410681330852041373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4807307214241774469388497 3605480410681330852041373)
                  ·
                    refine ⟨1352055154005499069515515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3605480410681330852041373 1352055154005499069515515)
                    ·
                      rfl

theorem cell22_3949677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_3949677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949677 prefixEnd_3949677 := by exact prefixLift 3949677
  have htrace : WordTrace (prefixWord ++ tailWord_3949677) baseStart_3949677 baseEnd_3949677 := by
    simpa [prefixWord, tailWord_3949677, baseEnd_3949677] using wordTrace_append hprefix tailTrace_3949677
  have hstable : (prefixWord ++ tailWord_3949677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949677).length < 2 ^ (prefixWord ++ tailWord_3949677).sum := by decide
  have hdescent : baseEnd_3949677 < baseStart_3949677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949722 : List Nat := [3, 1, 1, 5, 1, 2, 1, 4, 1, 3]
def baseStart_3949722 : Nat := 118140960795 + 3949722 * 2 ^ 59
def prefixEnd_3949722 : Nat := 4983230072969 + 3 ^ 40 * 3949722 * 2
def baseEnd_3949722 : Nat := 1352070558425133952140377

theorem tailTrace_3949722 : CollatzResearch.WordTrace tailWord_3949722 prefixEnd_3949722 1352070558425133952140377 := by
  unfold tailWord_3949722
  simp only [CollatzResearch.WordTrace]
  refine ⟨36014549049209806914584855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96038797464559485105559613 36014549049209806914584855)
  ·
    refine ⟨54021823573814710371877283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36014549049209806914584855 54021823573814710371877283)
    ·
      refine ⟨81032735360722065557815925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54021823573814710371877283 81032735360722065557815925)
      ·
        refine ⟨7596818940067693646045243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81032735360722065557815925 7596818940067693646045243)
        ·
          refine ⟨11395228410101540469067865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7596818940067693646045243 11395228410101540469067865)
          ·
            refine ⟨8546421307576155351800899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11395228410101540469067865 8546421307576155351800899)
            ·
              refine ⟨12819631961364233027701349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546421307576155351800899 12819631961364233027701349)
              ·
                refine ⟨2403680992755793692694003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12819631961364233027701349 2403680992755793692694003)
                ·
                  refine ⟨3605521489133690539041005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403680992755793692694003 3605521489133690539041005)
                  ·
                    refine ⟨1352070558425133952140377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3605521489133690539041005 1352070558425133952140377)
                    ·
                      rfl

theorem cell22_3949722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_3949722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949722 prefixEnd_3949722 := by exact prefixLift 3949722
  have htrace : WordTrace (prefixWord ++ tailWord_3949722) baseStart_3949722 baseEnd_3949722 := by
    simpa [prefixWord, tailWord_3949722, baseEnd_3949722] using wordTrace_append hprefix tailTrace_3949722
  have hstable : (prefixWord ++ tailWord_3949722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949722).length < 2 ^ (prefixWord ++ tailWord_3949722).sum := by decide
  have hdescent : baseEnd_3949722 < baseStart_3949722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949746 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_3949746 : Nat := 118140960795 + 3949746 * 2 ^ 59
def prefixEnd_3949746 : Nat := 4983230072969 + 3 ^ 40 * 3949746 * 2
def baseEnd_3949746 : Nat := 450692924705201963180101

theorem tailTrace_3949746 : CollatzResearch.WordTrace tailWord_3949746 prefixEnd_3949746 450692924705201963180101 := by
  unfold tailWord_3949746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36014767887188069939303273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96039381032501519838142061 36014767887188069939303273)
  ·
    refine ⟨27011075915391052454477455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36014767887188069939303273 27011075915391052454477455)
    ·
      refine ⟨40516613873086578681716183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27011075915391052454477455 40516613873086578681716183)
      ·
        refine ⟨60774920809629868022574275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40516613873086578681716183 60774920809629868022574275)
        ·
          refine ⟨91162381214444802033861413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60774920809629868022574275 91162381214444802033861413)
          ·
            refine ⟨17092946477708400381349015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91162381214444802033861413 17092946477708400381349015)
            ·
              refine ⟨25639419716562600572023523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17092946477708400381349015 25639419716562600572023523)
              ·
                refine ⟨38459129574843900858035285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25639419716562600572023523 38459129574843900858035285)
                ·
                  refine ⟨450692924705201963180101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38459129574843900858035285 450692924705201963180101)
                  ·
                    rfl

theorem cell22_3949746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_3949746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949746 prefixEnd_3949746 := by exact prefixLift 3949746
  have htrace : WordTrace (prefixWord ++ tailWord_3949746) baseStart_3949746 baseEnd_3949746 := by
    simpa [prefixWord, tailWord_3949746, baseEnd_3949746] using wordTrace_append hprefix tailTrace_3949746
  have hstable : (prefixWord ++ tailWord_3949746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949746).length < 2 ^ (prefixWord ++ tailWord_3949746).sum := by decide
  have hdescent : baseEnd_3949746 < baseStart_3949746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949821 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3949821 : Nat := 118140960795 + 3949821 * 2 ^ 59
def prefixEnd_3949821 : Nat := 4983230072969 + 3 ^ 40 * 3949821 * 2
def baseEnd_3949821 : Nat := 1352104448148330693915073

theorem tailTrace_3949821 : CollatzResearch.WordTrace tailWord_3949821 prefixEnd_3949821 1352104448148330693915073 := by
  unfold tailWord_3949821
  simp only [CollatzResearch.WordTrace]
  refine ⟨144061807023480567566193317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96041204682320378377462211 144061807023480567566193317)
  ·
    refine ⟨27011588816902606418661247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144061807023480567566193317 27011588816902606418661247)
    ·
      refine ⟨40517383225353909627991871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27011588816902606418661247 40517383225353909627991871)
      ·
        refine ⟨60776074838030864441987807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40517383225353909627991871 60776074838030864441987807)
        ·
          refine ⟨91164112257046296662981711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60776074838030864441987807 91164112257046296662981711)
          ·
            refine ⟨136746168385569444994472567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91164112257046296662981711 136746168385569444994472567)
            ·
              refine ⟨205119252578354167491708851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136746168385569444994472567 205119252578354167491708851)
              ·
                refine ⟨307678878867531251237563277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205119252578354167491708851 307678878867531251237563277)
                ·
                  refine ⟨115379579575324219214086229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307678878867531251237563277 115379579575324219214086229)
                  ·
                    refine ⟨1352104448148330693915073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115379579575324219214086229 1352104448148330693915073)
                    ·
                      rfl

theorem cell22_3949821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3949821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949821 prefixEnd_3949821 := by exact prefixLift 3949821
  have htrace : WordTrace (prefixWord ++ tailWord_3949821) baseStart_3949821 baseEnd_3949821 := by
    simpa [prefixWord, tailWord_3949821, baseEnd_3949821] using wordTrace_append hprefix tailTrace_3949821
  have hstable : (prefixWord ++ tailWord_3949821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949821).length < 2 ^ (prefixWord ++ tailWord_3949821).sum := by decide
  have hdescent : baseEnd_3949821 < baseStart_3949821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949842 : List Nat := [3, 2, 4, 2, 1, 1, 2, 7]
def baseStart_3949842 : Nat := 118140960795 + 3949842 * 2 ^ 59
def prefixEnd_3949842 : Nat := 4983230072969 + 3 ^ 40 * 3949842 * 2
def baseEnd_3949842 : Nat := 150234626319721515460001

theorem tailTrace_3949842 : CollatzResearch.WordTrace tailWord_3949842 prefixEnd_3949842 150234626319721515460001 := by
  unfold tailWord_3949842
  simp only [CollatzResearch.WordTrace]
  refine ⟨36015643239101122038176945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96041715304269658768471853 36015643239101122038176945)
  ·
    refine ⟨27011732429325841528632709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36015643239101122038176945 27011732429325841528632709)
    ·
      refine ⟨5064699830498595286618633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27011732429325841528632709 5064699830498595286618633)
      ·
        refine ⟨3798524872873946464963975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5064699830498595286618633 3798524872873946464963975)
        ·
          refine ⟨5697787309310919697445963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3798524872873946464963975 5697787309310919697445963)
          ·
            refine ⟨8546680963966379546168945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5697787309310919697445963 8546680963966379546168945)
            ·
              refine ⟨6410010722974784659626709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8546680963966379546168945 6410010722974784659626709)
              ·
                refine ⟨150234626319721515460001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6410010722974784659626709 150234626319721515460001)
                ·
                  rfl

theorem cell22_3949842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_3949842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949842 prefixEnd_3949842 := by exact prefixLift 3949842
  have htrace : WordTrace (prefixWord ++ tailWord_3949842) baseStart_3949842 baseEnd_3949842 := by
    simpa [prefixWord, tailWord_3949842, baseEnd_3949842] using wordTrace_append hprefix tailTrace_3949842
  have hstable : (prefixWord ++ tailWord_3949842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949842).length < 2 ^ (prefixWord ++ tailWord_3949842).sum := by decide
  have hdescent : baseEnd_3949842 < baseStart_3949842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949851 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 1, 7]
def baseStart_3949851 : Nat := 118140960795 + 3949851 * 2 ^ 59
def prefixEnd_3949851 : Nat := 4983230072969 + 3 ^ 40 * 3949851 * 2
def baseEnd_3949851 : Nat := 1352114717761420615664981

theorem tailTrace_3949851 : CollatzResearch.WordTrace tailWord_3949851 prefixEnd_3949851 1352114717761420615664981 := by
  unfold tailWord_3949851
  simp only [CollatzResearch.WordTrace]
  refine ⟨144062901213371882689785407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96041934142247921793190271 144062901213371882689785407)
  ·
    refine ⟨216094351820057824034678111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144062901213371882689785407 216094351820057824034678111)
    ·
      refine ⟨324141527730086736052017167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216094351820057824034678111 324141527730086736052017167)
      ·
        refine ⟨486212291595130104078025751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324141527730086736052017167 486212291595130104078025751)
        ·
          refine ⟨729318437392695156117038627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486212291595130104078025751 729318437392695156117038627)
          ·
            refine ⟨1093977656089042734175557941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729318437392695156117038627 1093977656089042734175557941)
            ·
              refine ⟨102560405258347756328958557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1093977656089042734175557941 102560405258347756328958557)
              ·
                refine ⟨38460151971880408623359459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102560405258347756328958557 38460151971880408623359459)
                ·
                  refine ⟨57690227957820612935039189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38460151971880408623359459 57690227957820612935039189)
                  ·
                    refine ⟨1352114717761420615664981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57690227957820612935039189 1352114717761420615664981)
                    ·
                      rfl

theorem cell22_3949851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_3949851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949851 prefixEnd_3949851 := by exact prefixLift 3949851
  have htrace : WordTrace (prefixWord ++ tailWord_3949851) baseStart_3949851 baseEnd_3949851 := by
    simpa [prefixWord, tailWord_3949851, baseEnd_3949851] using wordTrace_append hprefix tailTrace_3949851
  have hstable : (prefixWord ++ tailWord_3949851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949851).length < 2 ^ (prefixWord ++ tailWord_3949851).sum := by decide
  have hdescent : baseEnd_3949851 < baseStart_3949851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949913 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_3949913 : Nat := 118140960795 + 3949913 * 2 ^ 59
def prefixEnd_3949913 : Nat := 4983230072969 + 3 ^ 40 * 3949913 * 2
def baseEnd_3949913 : Nat := 1352135941628473120614791

theorem tailTrace_3949913 : CollatzResearch.WordTrace tailWord_3949913 prefixEnd_3949913 1352135941628473120614791 := by
  unfold tailWord_3949913
  simp only [CollatzResearch.WordTrace]
  refine ⟨144065162539147267278542393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96043441692764844852361595 144065162539147267278542393)
  ·
    refine ⟨108048871904360450458906795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144065162539147267278542393 108048871904360450458906795)
    ·
      refine ⟨162073307856540675688360193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108048871904360450458906795 162073307856540675688360193)
      ·
        refine ⟨121554980892405506766270145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162073307856540675688360193 121554980892405506766270145)
        ·
          refine ⟨91166235669304130074702609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121554980892405506766270145 91166235669304130074702609)
          ·
            refine ⟨68374676751978097556026957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91166235669304130074702609 68374676751978097556026957)
            ·
              refine ⟨25640503781991786583510109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68374676751978097556026957 25640503781991786583510109)
              ·
                refine ⟨9615188918246919968816291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25640503781991786583510109 9615188918246919968816291)
                ·
                  refine ⟨14422783377370379953224437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9615188918246919968816291 14422783377370379953224437)
                  ·
                    refine ⟨1352135941628473120614791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14422783377370379953224437 1352135941628473120614791)
                    ·
                      rfl

theorem cell22_3949913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_3949913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949913 prefixEnd_3949913 := by exact prefixLift 3949913
  have htrace : WordTrace (prefixWord ++ tailWord_3949913) baseStart_3949913 baseEnd_3949913 := by
    simpa [prefixWord, tailWord_3949913, baseEnd_3949913] using wordTrace_append hprefix tailTrace_3949913
  have hstable : (prefixWord ++ tailWord_3949913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949913).length < 2 ^ (prefixWord ++ tailWord_3949913).sum := by decide
  have hdescent : baseEnd_3949913 < baseStart_3949913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
