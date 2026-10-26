import V185TrunkScan23Chunk0696

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4120993 : List Nat := [1, 2, 3, 5, 2, 1, 2, 2, 1, 4]
def baseStart_4120993 : Nat := 118140960795 + 4120993 * 2 ^ 59
def prefixEnd_4120993 : Nat := 4983230072969 + 3 ^ 40 * 4120993 * 2
def baseEnd_4120993 : Nat := 705350060937966776545135

theorem tailTrace_4120993 : CollatzResearch.WordTrace tailWord_4120993 prefixEnd_4120993 705350060937966776545135 := by
  unfold tailWord_4120993
  simp only [CollatzResearch.WordTrace]
  refine ⟨150304962759353645416367633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100203308506235763610911755 150304962759353645416367633)
  ·
    refine ⟨112728722069515234062275725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150304962759353645416367633 112728722069515234062275725)
    ·
      refine ⟨42273270776068212773353397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112728722069515234062275725 42273270776068212773353397)
      ·
        refine ⟨3963119135256394947501881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42273270776068212773353397 3963119135256394947501881)
        ·
          refine ⟨2972339351442296210626411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3963119135256394947501881 2972339351442296210626411)
          ·
            refine ⟨4458509027163444315939617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972339351442296210626411 4458509027163444315939617)
            ·
              refine ⟨3343881770372583236954713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458509027163444315939617 3343881770372583236954713)
              ·
                refine ⟨2507911327779437427716035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343881770372583236954713 2507911327779437427716035)
                ·
                  refine ⟨3761866991669156141574053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507911327779437427716035 3761866991669156141574053)
                  ·
                    refine ⟨705350060937966776545135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3761866991669156141574053 705350060937966776545135)
                    ·
                      rfl

theorem cell23_4120993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_4120993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120993 prefixEnd_4120993 := by exact prefixLift 4120993
  have htrace : WordTrace (prefixWord ++ tailWord_4120993) baseStart_4120993 baseEnd_4120993 := by
    simpa [prefixWord, tailWord_4120993, baseEnd_4120993] using wordTrace_append hprefix tailTrace_4120993
  have hstable : (prefixWord ++ tailWord_4120993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120993).length < 2 ^ (prefixWord ++ tailWord_4120993).sum := by decide
  have hdescent : baseEnd_4120993 < baseStart_4120993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120999 : List Nat := [1, 1, 6, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_4120999 : Nat := 118140960795 + 4120999 * 2 ^ 59
def prefixEnd_4120999 : Nat := 4983230072969 + 3 ^ 40 * 4120999 * 2
def baseEnd_4120999 : Nat := 2116053263697827306160377

theorem tailTrace_4120999 : CollatzResearch.WordTrace tailWord_4120999 prefixEnd_4120999 2116053263697827306160377 := by
  unfold tailWord_4120999
  simp only [CollatzResearch.WordTrace]
  refine ⟨150305181597331908441086051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100203454398221272294057367 150305181597331908441086051)
  ·
    refine ⟨225457772395997862661629077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150305181597331908441086051 225457772395997862661629077)
    ·
      refine ⟨10568333081062399812263863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 225457772395997862661629077 10568333081062399812263863)
      ·
        refine ⟨15852499621593599718395795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10568333081062399812263863 15852499621593599718395795)
        ·
          refine ⟨23778749432390399577593693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15852499621593599718395795 23778749432390399577593693)
          ·
            refine ⟨8917031037146399841597635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23778749432390399577593693 8917031037146399841597635)
            ·
              refine ⟨13375546555719599762396453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8917031037146399841597635 13375546555719599762396453)
              ·
                refine ⟨2507914979197424955449335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13375546555719599762396453 2507914979197424955449335)
                ·
                  refine ⟨3761872468796137433174003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507914979197424955449335 3761872468796137433174003)
                  ·
                    refine ⟨5642808703194206149761005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3761872468796137433174003 5642808703194206149761005)
                    ·
                      refine ⟨2116053263697827306160377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5642808703194206149761005 2116053263697827306160377)
                      ·
                        rfl

theorem cell23_4120999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_4120999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120999 prefixEnd_4120999 := by exact prefixLift 4120999
  have htrace : WordTrace (prefixWord ++ tailWord_4120999) baseStart_4120999 baseEnd_4120999 := by
    simpa [prefixWord, tailWord_4120999, baseEnd_4120999] using wordTrace_append hprefix tailTrace_4120999
  have hstable : (prefixWord ++ tailWord_4120999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120999).length < 2 ^ (prefixWord ++ tailWord_4120999).sum := by decide
  have hdescent : baseEnd_4120999 < baseStart_4120999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121001 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_4121001 : Nat := 118140960795 + 4121001 * 2 ^ 59
def prefixEnd_4121001 : Nat := 4983230072969 + 3 ^ 40 * 4121001 * 2
def baseEnd_4121001 : Nat := 2116054290659136298335367

theorem tailTrace_4121001 : CollatzResearch.WordTrace tailWord_4121001 prefixEnd_4121001 2116054290659136298335367 := by
  unfold tailWord_4121001
  simp only [CollatzResearch.WordTrace]
  refine ⟨150305254543324662782658857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100203503028883108521772571 150305254543324662782658857)
  ·
    refine ⟨112728940907493497086994143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150305254543324662782658857 112728940907493497086994143)
    ·
      refine ⟨169093411361240245630491215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112728940907493497086994143 169093411361240245630491215)
      ·
        refine ⟨253640117041860368445736823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169093411361240245630491215 253640117041860368445736823)
        ·
          refine ⟨380460175562790552668605235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253640117041860368445736823 380460175562790552668605235)
          ·
            refine ⟨570690263344185829002907853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380460175562790552668605235 570690263344185829002907853)
            ·
              refine ⟨214008848754069685876090445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570690263344185829002907853 214008848754069685876090445)
              ·
                refine ⟨80253318282776132203533917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214008848754069685876090445 80253318282776132203533917)
                ·
                  refine ⟨30094994356041049576325219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80253318282776132203533917 30094994356041049576325219)
                  ·
                    refine ⟨45142491534061574364487829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30094994356041049576325219 45142491534061574364487829)
                    ·
                      refine ⟨2116054290659136298335367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45142491534061574364487829 2116054290659136298335367)
                      ·
                        rfl

theorem cell23_4121001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_4121001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121001 prefixEnd_4121001 := by exact prefixLift 4121001
  have htrace : WordTrace (prefixWord ++ tailWord_4121001) baseStart_4121001 baseEnd_4121001 := by
    simpa [prefixWord, tailWord_4121001, baseEnd_4121001] using wordTrace_append hprefix tailTrace_4121001
  have hstable : (prefixWord ++ tailWord_4121001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121001).length < 2 ^ (prefixWord ++ tailWord_4121001).sum := by decide
  have hdescent : baseEnd_4121001 < baseStart_4121001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121015 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 2, 4]
def baseStart_4121015 : Nat := 118140960795 + 4121015 * 2 ^ 59
def prefixEnd_4121015 : Nat := 4983230072969 + 3 ^ 40 * 4121015 * 2
def baseEnd_4121015 : Nat := 705353826462766414520101

theorem tailTrace_4121015 : CollatzResearch.WordTrace tailWord_4121015 prefixEnd_4121015 705353826462766414520101 := by
  unfold tailWord_4121015
  simp only [CollatzResearch.WordTrace]
  refine ⟨150305765165273943173668499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100203843443515962115778999 150305765165273943173668499)
  ·
    refine ⟨225458647747910914760502749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150305765165273943173668499 225458647747910914760502749)
    ·
      refine ⟨84546992905466593035188531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225458647747910914760502749 84546992905466593035188531)
      ·
        refine ⟨126820489358199889552782797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84546992905466593035188531 126820489358199889552782797)
        ·
          refine ⟨47557683509324958582293549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126820489358199889552782797 47557683509324958582293549)
          ·
            refine ⟨17834131315996859468360081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47557683509324958582293549 17834131315996859468360081)
            ·
              refine ⟨13375598486997644601270061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17834131315996859468360081 13375598486997644601270061)
              ·
                refine ⟨5015849432624116725476273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13375598486997644601270061 5015849432624116725476273)
                ·
                  refine ⟨3761887074468087544107205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5015849432624116725476273 3761887074468087544107205)
                  ·
                    refine ⟨705353826462766414520101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3761887074468087544107205 705353826462766414520101)
                    ·
                      rfl

theorem cell23_4121015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_4121015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121015 prefixEnd_4121015 := by exact prefixLift 4121015
  have htrace : WordTrace (prefixWord ++ tailWord_4121015) baseStart_4121015 baseEnd_4121015 := by
    simpa [prefixWord, tailWord_4121015, baseEnd_4121015] using wordTrace_append hprefix tailTrace_4121015
  have hstable : (prefixWord ++ tailWord_4121015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121015).length < 2 ^ (prefixWord ++ tailWord_4121015).sum := by decide
  have hdescent : baseEnd_4121015 < baseStart_4121015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121022 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_4121022 : Nat := 118140960795 + 4121022 * 2 ^ 59
def prefixEnd_4121022 : Nat := 4983230072969 + 3 ^ 40 * 4121022 * 2
def baseEnd_4121022 : Nat := 2116065073752880716172771

theorem tailTrace_4121022 : CollatzResearch.WordTrace tailWord_4121022 prefixEnd_4121022 2116065073752880716172771 := by
  unfold tailWord_4121022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18788252559531072921146665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100204013650832388912782213 18788252559531072921146665)
  ·
    refine ⟨14091189419648304690859999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18788252559531072921146665 14091189419648304690859999)
    ·
      refine ⟨21136784129472457036289999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14091189419648304690859999 21136784129472457036289999)
      ·
        refine ⟨31705176194208685554434999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21136784129472457036289999 31705176194208685554434999)
        ·
          refine ⟨47557764291313028331652499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31705176194208685554434999 47557764291313028331652499)
          ·
            refine ⟨71336646436969542497478749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47557764291313028331652499 71336646436969542497478749)
            ·
              refine ⟨26751242413863578436554531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71336646436969542497478749 26751242413863578436554531)
              ·
                refine ⟨40126863620795367654831797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26751242413863578436554531 40126863620795367654831797)
                ·
                  refine ⟨3761893464449565717640481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40126863620795367654831797 3761893464449565717640481)
                  ·
                    refine ⟨2821420098337174288230361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3761893464449565717640481 2821420098337174288230361)
                    ·
                      refine ⟨2116065073752880716172771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821420098337174288230361 2116065073752880716172771)
                      ·
                        rfl

theorem cell23_4121022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_4121022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121022 prefixEnd_4121022 := by exact prefixLift 4121022
  have htrace : WordTrace (prefixWord ++ tailWord_4121022) baseStart_4121022 baseEnd_4121022 := by
    simpa [prefixWord, tailWord_4121022, baseEnd_4121022] using wordTrace_append hprefix tailTrace_4121022
  have hstable : (prefixWord ++ tailWord_4121022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121022).length < 2 ^ (prefixWord ++ tailWord_4121022).sum := by decide
  have hdescent : baseEnd_4121022 < baseStart_4121022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121065 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 3, 3, 2]
def baseStart_4121065 : Nat := 118140960795 + 4121065 * 2 ^ 59
def prefixEnd_4121065 : Nat := 4983230072969 + 3 ^ 40 * 4121065 * 2
def baseEnd_4121065 : Nat := 2116087153421024047935073

theorem tailTrace_4121065 : CollatzResearch.WordTrace tailWord_4121065 prefixEnd_4121065 2116087153421024047935073 := by
  unfold tailWord_4121065
  simp only [CollatzResearch.WordTrace]
  refine ⟨150307588815092801712988649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100205059210061867808659099 150307588815092801712988649)
  ·
    refine ⟨112730691611319601284741487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150307588815092801712988649 112730691611319601284741487)
    ·
      refine ⟨169096037416979401927112231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112730691611319601284741487 169096037416979401927112231)
      ·
        refine ⟨253644056125469102890668347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169096037416979401927112231 253644056125469102890668347)
        ·
          refine ⟨380466084188203654336002521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253644056125469102890668347 380466084188203654336002521)
          ·
            refine ⟨285349563141152740752001891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380466084188203654336002521 285349563141152740752001891)
            ·
              refine ⟨428024344711729111128002837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285349563141152740752001891 428024344711729111128002837)
              ·
                refine ⟨20063641158362302084125133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 428024344711729111128002837 20063641158362302084125133)
                ·
                  refine ⟨7523865434385863281546925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20063641158362302084125133 7523865434385863281546925)
                  ·
                    refine ⟨2821449537894698730580097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7523865434385863281546925 2821449537894698730580097)
                    ·
                      refine ⟨2116087153421024047935073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821449537894698730580097 2116087153421024047935073)
                      ·
                        rfl

theorem cell23_4121065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 3, 2].length) (baseStart_4121065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121065 prefixEnd_4121065 := by exact prefixLift 4121065
  have htrace : WordTrace (prefixWord ++ tailWord_4121065) baseStart_4121065 baseEnd_4121065 := by
    simpa [prefixWord, tailWord_4121065, baseEnd_4121065] using wordTrace_append hprefix tailTrace_4121065
  have hstable : (prefixWord ++ tailWord_4121065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121065).length < 2 ^ (prefixWord ++ tailWord_4121065).sum := by decide
  have hdescent : baseEnd_4121065 < baseStart_4121065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121090 : List Nat := [3, 4, 1, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4121090 : Nat := 118140960795 + 4121090 * 2 ^ 59
def prefixEnd_4121090 : Nat := 4983230072969 + 3 ^ 40 * 4121090 * 2
def baseEnd_4121090 : Nat := 2116099990437386450122459

theorem tailTrace_4121090 : CollatzResearch.WordTrace tailWord_4121090 prefixEnd_4121090 2116099990437386450122459 := by
  unfold tailWord_4121090
  simp only [CollatzResearch.WordTrace]
  refine ⟨37577125160000557745662181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100205667093334820655099149 37577125160000557745662181)
  ·
    refine ⟨7045710967500104577311659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37577125160000557745662181 7045710967500104577311659)
    ·
      refine ⟨10568566451250156865967489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7045710967500104577311659 10568566451250156865967489)
      ·
        refine ⟨7926424838437617649475617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10568566451250156865967489 7926424838437617649475617)
        ·
          refine ⟨5944818628828213237106713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7926424838437617649475617 5944818628828213237106713)
          ·
            refine ⟨4458613971621159927830035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5944818628828213237106713 4458613971621159927830035)
            ·
              refine ⟨6687920957431739891745053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458613971621159927830035 6687920957431739891745053)
              ·
                refine ⟨2507970359036902459404395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6687920957431739891745053 2507970359036902459404395)
                ·
                  refine ⟨3761955538555353689106593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507970359036902459404395 3761955538555353689106593)
                  ·
                    refine ⟨2821466653916515266829945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3761955538555353689106593 2821466653916515266829945)
                    ·
                      refine ⟨2116099990437386450122459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821466653916515266829945 2116099990437386450122459)
                      ·
                        rfl

theorem cell23_4121090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4121090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121090 prefixEnd_4121090 := by exact prefixLift 4121090
  have htrace : WordTrace (prefixWord ++ tailWord_4121090) baseStart_4121090 baseEnd_4121090 := by
    simpa [prefixWord, tailWord_4121090, baseEnd_4121090] using wordTrace_append hprefix tailTrace_4121090
  have hstable : (prefixWord ++ tailWord_4121090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121090).length < 2 ^ (prefixWord ++ tailWord_4121090).sum := by decide
  have hdescent : baseEnd_4121090 < baseStart_4121090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121133 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4121133 : Nat := 118140960795 + 4121133 * 2 ^ 59
def prefixEnd_4121133 : Nat := 4983230072969 + 3 ^ 40 * 4121133 * 2
def baseEnd_4121133 : Nat := 2116122070105529781884761

theorem tailTrace_4121133 : CollatzResearch.WordTrace tailWord_4121133 prefixEnd_4121133 2116122070105529781884761 := by
  unfold tailWord_4121133
  simp only [CollatzResearch.WordTrace]
  refine ⟨150310068978846449326464053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100206712652564299550976035 150310068978846449326464053)
  ·
    refine ⟨14091568966766854624356005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150310068978846449326464053 14091568966766854624356005)
    ·
      refine ⟨2642169181268785242066751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14091568966766854624356005 2642169181268785242066751)
      ·
        refine ⟨3963253771903177863100127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2642169181268785242066751 3963253771903177863100127)
        ·
          refine ⟨5944880657854766794650191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963253771903177863100127 5944880657854766794650191)
          ·
            refine ⟨8917320986782150191975287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944880657854766794650191 8917320986782150191975287)
            ·
              refine ⟨13375981480173225287962931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8917320986782150191975287 13375981480173225287962931)
              ·
                refine ⟨20063972220259837931944397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13375981480173225287962931 20063972220259837931944397)
                ·
                  refine ⟨7523989582597439224479149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20063972220259837931944397 7523989582597439224479149)
                  ·
                    refine ⟨2821496093474039709179681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7523989582597439224479149 2821496093474039709179681)
                    ·
                      refine ⟨2116122070105529781884761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821496093474039709179681 2116122070105529781884761)
                      ·
                        rfl

theorem cell23_4121133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4121133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121133 prefixEnd_4121133 := by exact prefixLift 4121133
  have htrace : WordTrace (prefixWord ++ tailWord_4121133) baseStart_4121133 baseEnd_4121133 := by
    simpa [prefixWord, tailWord_4121133, baseEnd_4121133] using wordTrace_append hprefix tailTrace_4121133
  have hstable : (prefixWord ++ tailWord_4121133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121133).length < 2 ^ (prefixWord ++ tailWord_4121133).sum := by decide
  have hdescent : baseEnd_4121133 < baseStart_4121133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121155 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 4, 5, 2]
def baseStart_4121155 : Nat := 118140960795 + 4121155 * 2 ^ 59
def prefixEnd_4121155 : Nat := 4983230072969 + 3 ^ 40 * 4121155 * 2
def baseEnd_4121155 : Nat := 2116133366679928695809659

theorem tailTrace_4121155 : CollatzResearch.WordTrace tailWord_4121155 prefixEnd_4121155 2116133366679928695809659 := by
  unfold tailWord_4121155
  simp only [CollatzResearch.WordTrace]
  refine ⟨150310871384766747083764919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100207247589844498055843279 150310871384766747083764919)
  ·
    refine ⟨225466307077150120625647379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150310871384766747083764919 225466307077150120625647379)
    ·
      refine ⟨338199460615725180938471069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225466307077150120625647379 338199460615725180938471069)
      ·
        refine ⟨126824797730896942851926651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338199460615725180938471069 126824797730896942851926651)
        ·
          refine ⟨190237196596345414277889977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126824797730896942851926651 190237196596345414277889977)
          ·
            refine ⟨142677897447259060708417483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190237196596345414277889977 142677897447259060708417483)
            ·
              refine ⟨214016846170888591062626225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142677897447259060708417483 214016846170888591062626225)
              ·
                refine ⟨160512634628166443296969669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214016846170888591062626225 160512634628166443296969669)
                ·
                  refine ⟨30096118992781208118181813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160512634628166443296969669 30096118992781208118181813)
                  ·
                    refine ⟨2821511155573238261079545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30096118992781208118181813 2821511155573238261079545)
                    ·
                      refine ⟨2116133366679928695809659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821511155573238261079545 2116133366679928695809659)
                      ·
                        rfl

theorem cell23_4121155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_4121155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121155 prefixEnd_4121155 := by exact prefixLift 4121155
  have htrace : WordTrace (prefixWord ++ tailWord_4121155) baseStart_4121155 baseEnd_4121155 := by
    simpa [prefixWord, tailWord_4121155, baseEnd_4121155] using wordTrace_append hprefix tailTrace_4121155
  have hstable : (prefixWord ++ tailWord_4121155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121155).length < 2 ^ (prefixWord ++ tailWord_4121155).sum := by decide
  have hdescent : baseEnd_4121155 < baseStart_4121155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121169 : List Nat := [1, 2, 2, 1, 3, 5, 2, 2, 5]
def baseStart_4121169 : Nat := 118140960795 + 4121169 * 2 ^ 59
def prefixEnd_4121169 : Nat := 4983230072969 + 3 ^ 40 * 4121169 * 2
def baseEnd_4121169 : Nat := 235126728378787960114955

theorem tailTrace_4121169 : CollatzResearch.WordTrace tailWord_4121169 prefixEnd_4121169 235126728378787960114955 := by
  unfold tailWord_4121169
  simp only [CollatzResearch.WordTrace]
  refine ⟨150311382006716027474774561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100207588004477351649849707 150311382006716027474774561)
  ·
    refine ⟨112733536505037020606080921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150311382006716027474774561 112733536505037020606080921)
    ·
      refine ⟨84550152378777765454560691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112733536505037020606080921 84550152378777765454560691)
      ·
        refine ⟨126825228568166648181841037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84550152378777765454560691 126825228568166648181841037)
        ·
          refine ⟨47559460713062493068190389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126825228568166648181841037 47559460713062493068190389)
          ·
            refine ⟨4458699441849608725142849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47559460713062493068190389 4458699441849608725142849)
            ·
              refine ⟨3344024581387206543857137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458699441849608725142849 3344024581387206543857137)
              ·
                refine ⟨2508018436040404907892853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344024581387206543857137 2508018436040404907892853)
                ·
                  refine ⟨235126728378787960114955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2508018436040404907892853 235126728378787960114955)
                  ·
                    rfl

theorem cell23_4121169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 5].length) (baseStart_4121169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121169 prefixEnd_4121169 := by exact prefixLift 4121169
  have htrace : WordTrace (prefixWord ++ tailWord_4121169) baseStart_4121169 baseEnd_4121169 := by
    simpa [prefixWord, tailWord_4121169, baseEnd_4121169] using wordTrace_append hprefix tailTrace_4121169
  have hstable : (prefixWord ++ tailWord_4121169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121169).length < 2 ^ (prefixWord ++ tailWord_4121169).sum := by decide
  have hdescent : baseEnd_4121169 < baseStart_4121169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121172 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_4121172 : Nat := 118140960795 + 4121172 * 2 ^ 59
def prefixEnd_4121172 : Nat := 4983230072969 + 3 ^ 40 * 4121172 * 2
def baseEnd_4121172 : Nat := 2116142095851055129297081

theorem tailTrace_4121172 : CollatzResearch.WordTrace tailWord_4121172 prefixEnd_4121172 2116142095851055129297081 := by
  unfold tailWord_4121172
  simp only [CollatzResearch.WordTrace]
  refine ⟨75155745712852579493566885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100207660950470105991422513 75155745712852579493566885)
  ·
    refine ⟨14091702321159858655043791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75155745712852579493566885 14091702321159858655043791)
    ·
      refine ⟨21137553481739787982565687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14091702321159858655043791 21137553481739787982565687)
      ·
        refine ⟨31706330222609681973848531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21137553481739787982565687 31706330222609681973848531)
        ·
          refine ⟨47559495333914522960772797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31706330222609681973848531 47559495333914522960772797)
          ·
            refine ⟨17834810750217946110289799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47559495333914522960772797 17834810750217946110289799)
            ·
              refine ⟨26752216125326919165434699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17834810750217946110289799 26752216125326919165434699)
              ·
                refine ⟨40128324187990378748152049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26752216125326919165434699 40128324187990378748152049)
                ·
                  refine ⟨30096243140992784061114037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40128324187990378748152049 30096243140992784061114037)
                  ·
                    refine ⟨2821522794468073505729441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30096243140992784061114037 2821522794468073505729441)
                    ·
                      refine ⟨2116142095851055129297081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821522794468073505729441 2116142095851055129297081)
                      ·
                        rfl

theorem cell23_4121172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_4121172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121172 prefixEnd_4121172 := by exact prefixLift 4121172
  have htrace : WordTrace (prefixWord ++ tailWord_4121172) baseStart_4121172 baseEnd_4121172 := by
    simpa [prefixWord, tailWord_4121172, baseEnd_4121172] using wordTrace_append hprefix tailTrace_4121172
  have hstable : (prefixWord ++ tailWord_4121172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121172).length < 2 ^ (prefixWord ++ tailWord_4121172).sum := by decide
  have hdescent : baseEnd_4121172 < baseStart_4121172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121178 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_4121178 : Nat := 118140960795 + 4121178 * 2 ^ 59
def prefixEnd_4121178 : Nat := 4983230072969 + 3 ^ 40 * 4121178 * 2
def baseEnd_4121178 : Nat := 705381725578327368607351

theorem tailTrace_4121178 : CollatzResearch.WordTrace tailWord_4121178 prefixEnd_4121178 705381725578327368607351 := by
  unfold tailWord_4121178
  simp only [CollatzResearch.WordTrace]
  refine ⟨37577927565920855502963047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100207806842455614674568125 37577927565920855502963047)
  ·
    refine ⟨56366891348881283254444571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37577927565920855502963047 56366891348881283254444571)
    ·
      refine ⟨84550337023321924881666857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56366891348881283254444571 84550337023321924881666857)
      ·
        refine ⟨63412752767491443661250143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84550337023321924881666857 63412752767491443661250143)
        ·
          refine ⟨95119129151237165491875215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63412752767491443661250143 95119129151237165491875215)
          ·
            refine ⟨142678693726855748237812823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95119129151237165491875215 142678693726855748237812823)
            ·
              refine ⟨214018040590283622356719235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142678693726855748237812823 214018040590283622356719235)
              ·
                refine ⟨321027060885425433535078853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214018040590283622356719235 321027060885425433535078853)
                ·
                  refine ⟨60192573916017268787827285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321027060885425433535078853 60192573916017268787827285)
                  ·
                    refine ⟨705381725578327368607351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60192573916017268787827285 705381725578327368607351)
                    ·
                      rfl

theorem cell23_4121178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_4121178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121178 prefixEnd_4121178 := by exact prefixLift 4121178
  have htrace : WordTrace (prefixWord ++ tailWord_4121178) baseStart_4121178 baseEnd_4121178 := by
    simpa [prefixWord, tailWord_4121178, baseEnd_4121178] using wordTrace_append hprefix tailTrace_4121178
  have hstable : (prefixWord ++ tailWord_4121178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121178).length < 2 ^ (prefixWord ++ tailWord_4121178).sum := by decide
  have hdescent : baseEnd_4121178 < baseStart_4121178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121202 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_4121202 : Nat := 118140960795 + 4121202 * 2 ^ 59
def prefixEnd_4121202 : Nat := 4983230072969 + 3 ^ 40 * 4121202 * 2
def baseEnd_4121202 : Nat := 2116157500270690011921943

theorem tailTrace_4121202 : CollatzResearch.WordTrace tailWord_4121202 prefixEnd_4121202 2116157500270690011921943 := by
  unfold tailWord_4121202
  simp only [CollatzResearch.WordTrace]
  refine ⟨37578146403899118527681465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100208390410397649407150573 37578146403899118527681465)
  ·
    refine ⟨28183609802924338895761099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37578146403899118527681465 28183609802924338895761099)
    ·
      refine ⟨42275414704386508343641649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28183609802924338895761099 42275414704386508343641649)
      ·
        refine ⟨31706561028289881257731237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42275414704386508343641649 31706561028289881257731237)
        ·
          refine ⟨5944980192804352735824607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31706561028289881257731237 5944980192804352735824607)
          ·
            refine ⟨8917470289206529103736911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944980192804352735824607 8917470289206529103736911)
            ·
              refine ⟨13376205433809793655605367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8917470289206529103736911 13376205433809793655605367)
              ·
                refine ⟨20064308150714690483408051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13376205433809793655605367 20064308150714690483408051)
                ·
                  refine ⟨30096462226072035725112077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20064308150714690483408051 30096462226072035725112077)
                  ·
                    refine ⟨11286173334777013396917029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30096462226072035725112077 11286173334777013396917029)
                    ·
                      refine ⟨2116157500270690011921943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11286173334777013396917029 2116157500270690011921943)
                      ·
                        rfl

theorem cell23_4121202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_4121202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121202 prefixEnd_4121202 := by exact prefixLift 4121202
  have htrace : WordTrace (prefixWord ++ tailWord_4121202) baseStart_4121202 baseEnd_4121202 := by
    simpa [prefixWord, tailWord_4121202, baseEnd_4121202] using wordTrace_append hprefix tailTrace_4121202
  have hstable : (prefixWord ++ tailWord_4121202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121202).length < 2 ^ (prefixWord ++ tailWord_4121202).sum := by decide
  have hdescent : baseEnd_4121202 < baseStart_4121202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121208 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 10]
def baseStart_4121208 : Nat := 118140960795 + 4121208 * 2 ^ 59
def prefixEnd_4121208 : Nat := 4983230072969 + 3 ^ 40 * 4121208 * 2
def baseEnd_4121208 : Nat := 235128953461624109827435

theorem tailTrace_4121208 : CollatzResearch.WordTrace tailWord_4121208 prefixEnd_4121208 235128953461624109827435 := by
  unfold tailWord_4121208
  simp only [CollatzResearch.WordTrace]
  refine ⟨75156402226787368567722139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100208536302383158090296185 75156402226787368567722139)
  ·
    refine ⟨112734603340181052851583209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75156402226787368567722139 112734603340181052851583209)
    ·
      refine ⟨84550952505135789638687407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112734603340181052851583209 84550952505135789638687407)
      ·
        refine ⟨126826428757703684458031111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84550952505135789638687407 126826428757703684458031111)
        ·
          refine ⟨190239643136555526687046667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126826428757703684458031111 190239643136555526687046667)
          ·
            refine ⟨285359464704833290030570001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190239643136555526687046667 285359464704833290030570001)
            ·
              refine ⟨214019598528624967522927501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285359464704833290030570001 214019598528624967522927501)
              ·
                refine ⟨80257349448234362821097813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214019598528624967522927501 80257349448234362821097813)
                ·
                  refine ⟨235128953461624109827435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 80257349448234362821097813 235128953461624109827435)
                  ·
                    rfl

theorem cell23_4121208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 10].length) (baseStart_4121208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121208 prefixEnd_4121208 := by exact prefixLift 4121208
  have htrace : WordTrace (prefixWord ++ tailWord_4121208) baseStart_4121208 baseEnd_4121208 := by
    simpa [prefixWord, tailWord_4121208, baseEnd_4121208] using wordTrace_append hprefix tailTrace_4121208
  have hstable : (prefixWord ++ tailWord_4121208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121208).length < 2 ^ (prefixWord ++ tailWord_4121208).sum := by decide
  have hdescent : baseEnd_4121208 < baseStart_4121208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121275 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 4]
def baseStart_4121275 : Nat := 118140960795 + 4121275 * 2 ^ 59
def prefixEnd_4121275 : Nat := 4983230072969 + 3 ^ 40 * 4121275 * 2
def baseEnd_4121275 : Nat := 2116194984358468226309107

theorem tailTrace_4121275 : CollatzResearch.WordTrace tailWord_4121275 prefixEnd_4121275 2116194984358468226309107 := by
  unfold tailWord_4121275
  simp only [CollatzResearch.WordTrace]
  refine ⟨150315248144332007578133279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100210165429554671718755519 150315248144332007578133279)
  ·
    refine ⟨225472872216498011367199919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150315248144332007578133279 225472872216498011367199919)
    ·
      refine ⟨338209308324747017050799879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225472872216498011367199919 338209308324747017050799879)
      ·
        refine ⟨507313962487120525576199819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338209308324747017050799879 507313962487120525576199819)
        ·
          refine ⟨760970943730680788364299729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507313962487120525576199819 760970943730680788364299729)
          ·
            refine ⟨570728207798010591273224797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760970943730680788364299729 570728207798010591273224797)
            ·
              refine ⟨214023077924253971727459299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570728207798010591273224797 214023077924253971727459299)
              ·
                refine ⟨321034616886380957591188949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214023077924253971727459299 321034616886380957591188949)
                ·
                  refine ⟨7524248833274553693543491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 321034616886380957591188949 7524248833274553693543491)
                  ·
                    refine ⟨11286373249911830540315237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7524248833274553693543491 11286373249911830540315237)
                    ·
                      refine ⟨2116194984358468226309107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11286373249911830540315237 2116194984358468226309107)
                      ·
                        rfl

theorem cell23_4121275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 4].length) (baseStart_4121275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121275 prefixEnd_4121275 := by exact prefixLift 4121275
  have htrace : WordTrace (prefixWord ++ tailWord_4121275) baseStart_4121275 baseEnd_4121275 := by
    simpa [prefixWord, tailWord_4121275, baseEnd_4121275] using wordTrace_append hprefix tailTrace_4121275
  have hstable : (prefixWord ++ tailWord_4121275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121275).length < 2 ^ (prefixWord ++ tailWord_4121275).sum := by decide
  have hdescent : baseEnd_4121275 < baseStart_4121275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121279 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 2, 3, 2]
def baseStart_4121279 : Nat := 118140960795 + 4121279 * 2 ^ 59
def prefixEnd_4121279 : Nat := 4983230072969 + 3 ^ 40 * 4121279 * 2
def baseEnd_4121279 : Nat := 2116197038281086210659089

theorem tailTrace_4121279 : CollatzResearch.WordTrace tailWord_4121279 prefixEnd_4121279 2116197038281086210659089 := by
  unfold tailWord_4121279
  simp only [CollatzResearch.WordTrace]
  refine ⟨150315394036317516261278891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100210262690878344174185927 150315394036317516261278891)
  ·
    refine ⟨225473091054476274391918337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150315394036317516261278891 225473091054476274391918337)
    ·
      refine ⟨169104818290857205793938753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225473091054476274391918337 169104818290857205793938753)
      ·
        refine ⟨126828613718142904345454065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169104818290857205793938753 126828613718142904345454065)
        ·
          refine ⟨95121460288607178259090549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126828613718142904345454065 95121460288607178259090549)
          ·
            refine ⟨8917636902056922961789739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95121460288607178259090549 8917636902056922961789739)
            ·
              refine ⟨13376455353085384442684609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8917636902056922961789739 13376455353085384442684609)
              ·
                refine ⟨10032341514814038332013457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13376455353085384442684609 10032341514814038332013457)
                ·
                  refine ⟨7524256136110528749010093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10032341514814038332013457 7524256136110528749010093)
                  ·
                    refine ⟨2821596051041448280878785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7524256136110528749010093 2821596051041448280878785)
                    ·
                      refine ⟨2116197038281086210659089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821596051041448280878785 2116197038281086210659089)
                      ·
                        rfl

theorem cell23_4121279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_4121279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121279 prefixEnd_4121279 := by exact prefixLift 4121279
  have htrace : WordTrace (prefixWord ++ tailWord_4121279) baseStart_4121279 baseEnd_4121279 := by
    simpa [prefixWord, tailWord_4121279, baseEnd_4121279] using wordTrace_append hprefix tailTrace_4121279
  have hstable : (prefixWord ++ tailWord_4121279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121279).length < 2 ^ (prefixWord ++ tailWord_4121279).sum := by decide
  have hdescent : baseEnd_4121279 < baseStart_4121279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121293 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 6]
def baseStart_4121293 : Nat := 118140960795 + 4121293 * 2 ^ 59
def prefixEnd_4121293 : Nat := 4983230072969 + 3 ^ 40 * 4121293 * 2
def baseEnd_4121293 : Nat := 235133803001138795098225

theorem tailTrace_4121293 : CollatzResearch.WordTrace tailWord_4121293 prefixEnd_4121293 235133803001138795098225 := by
  unfold tailWord_4121293
  simp only [CollatzResearch.WordTrace]
  refine ⟨150315904658266796652288533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100210603105511197768192355 150315904658266796652288533)
  ·
    refine ⟨7046058030856256093076025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150315904658266796652288533 7046058030856256093076025)
    ·
      refine ⟨5284543523142192069807019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7046058030856256093076025 5284543523142192069807019)
      ·
        refine ⟨7926815284713288104710529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284543523142192069807019 7926815284713288104710529)
        ·
          refine ⟨5945111463534966078532897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7926815284713288104710529 5945111463534966078532897)
          ·
            refine ⟨4458833597651224558899673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5945111463534966078532897 4458833597651224558899673)
            ·
              refine ⟨3344125198238418419174755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458833597651224558899673 3344125198238418419174755)
              ·
                refine ⟨5016187797357627628762133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344125198238418419174755 5016187797357627628762133)
                ·
                  refine ⟨235133803001138795098225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5016187797357627628762133 235133803001138795098225)
                  ·
                    rfl

theorem cell23_4121293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_4121293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121293 prefixEnd_4121293 := by exact prefixLift 4121293
  have htrace : WordTrace (prefixWord ++ tailWord_4121293) baseStart_4121293 baseEnd_4121293 := by
    simpa [prefixWord, tailWord_4121293, baseEnd_4121293] using wordTrace_append hprefix tailTrace_4121293
  have hstable : (prefixWord ++ tailWord_4121293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121293).length < 2 ^ (prefixWord ++ tailWord_4121293).sum := by decide
  have hdescent : baseEnd_4121293 < baseStart_4121293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121295 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 3]
def baseStart_4121295 : Nat := 118140960795 + 4121295 * 2 ^ 59
def prefixEnd_4121295 : Nat := 4983230072969 + 3 ^ 40 * 4121295 * 2
def baseEnd_4121295 : Nat := 2116205253971558148059015

theorem tailTrace_4121295 : CollatzResearch.WordTrace tailWord_4121295 prefixEnd_4121295 2116205253971558148059015 := by
  unfold tailWord_4121295
  simp only [CollatzResearch.WordTrace]
  refine ⟨150315977604259550993861339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100210651736173033995907559 150315977604259550993861339)
  ·
    refine ⟨225473966406389326490792009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150315977604259550993861339 225473966406389326490792009)
    ·
      refine ⟨169105474804791994868094007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225473966406389326490792009 169105474804791994868094007)
      ·
        refine ⟨253658212207187992302141011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169105474804791994868094007 253658212207187992302141011)
        ·
          refine ⟨380487318310781988453211517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253658212207187992302141011 380487318310781988453211517)
          ·
            refine ⟨142682744366543245669954319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380487318310781988453211517 142682744366543245669954319)
            ·
              refine ⟨214024116549814868504931479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142682744366543245669954319 214024116549814868504931479)
              ·
                refine ⟨321036174824722302757397219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214024116549814868504931479 321036174824722302757397219)
                ·
                  refine ⟨481554262237083454136095829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321036174824722302757397219 481554262237083454136095829)
                  ·
                    refine ⟨5643214010590821728157373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 481554262237083454136095829 5643214010590821728157373)
                    ·
                      refine ⟨2116205253971558148059015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5643214010590821728157373 2116205253971558148059015)
                      ·
                        rfl

theorem cell23_4121295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 3].length) (baseStart_4121295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121295 prefixEnd_4121295 := by exact prefixLift 4121295
  have htrace : WordTrace (prefixWord ++ tailWord_4121295) baseStart_4121295 baseEnd_4121295 := by
    simpa [prefixWord, tailWord_4121295, baseEnd_4121295] using wordTrace_append hprefix tailTrace_4121295
  have hstable : (prefixWord ++ tailWord_4121295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121295).length < 2 ^ (prefixWord ++ tailWord_4121295).sum := by decide
  have hdescent : baseEnd_4121295 < baseStart_4121295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121305 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_4121305 : Nat := 118140960795 + 4121305 * 2 ^ 59
def prefixEnd_4121305 : Nat := 4983230072969 + 3 ^ 40 * 4121305 * 2
def baseEnd_4121305 : Nat := 2116210388778103108933969

theorem tailTrace_4121305 : CollatzResearch.WordTrace tailWord_4121305 prefixEnd_4121305 2116210388778103108933969 := by
  unfold tailWord_4121305
  simp only [CollatzResearch.WordTrace]
  refine ⟨150316342334223322701725369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100210894889482215134483579 150316342334223322701725369)
  ·
    refine ⟨112737256750667492026294027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150316342334223322701725369 112737256750667492026294027)
    ·
      refine ⟨169105885126001238039441041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112737256750667492026294027 169105885126001238039441041)
      ·
        refine ⟨126829413844500928529580781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169105885126001238039441041 126829413844500928529580781)
        ·
          refine ⟨47561030191687848198592793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126829413844500928529580781 47561030191687848198592793)
          ·
            refine ⟨35670772643765886148944595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47561030191687848198592793 35670772643765886148944595)
            ·
              refine ⟨53506158965648829223416893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35670772643765886148944595 53506158965648829223416893)
              ·
                refine ⟨20064809612118310958781335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53506158965648829223416893 20064809612118310958781335)
                ·
                  refine ⟨30097214418177466438172003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20064809612118310958781335 30097214418177466438172003)
                  ·
                    refine ⟨45145821627266199657258005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30097214418177466438172003 45145821627266199657258005)
                    ·
                      refine ⟨2116210388778103108933969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45145821627266199657258005 2116210388778103108933969)
                      ·
                        rfl

theorem cell23_4121305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_4121305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121305 prefixEnd_4121305 := by exact prefixLift 4121305
  have htrace : WordTrace (prefixWord ++ tailWord_4121305) baseStart_4121305 baseEnd_4121305 := by
    simpa [prefixWord, tailWord_4121305, baseEnd_4121305] using wordTrace_append hprefix tailTrace_4121305
  have hstable : (prefixWord ++ tailWord_4121305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121305).length < 2 ^ (prefixWord ++ tailWord_4121305).sum := by decide
  have hdescent : baseEnd_4121305 < baseStart_4121305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121326 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_4121326 : Nat := 118140960795 + 4121326 * 2 ^ 59
def prefixEnd_4121326 : Nat := 4983230072969 + 3 ^ 40 * 4121326 * 2
def baseEnd_4121326 : Nat := 2116221171871847526771373

theorem tailTrace_4121326 : CollatzResearch.WordTrace tailWord_4121326 prefixEnd_4121326 2116221171871847526771373 := by
  unfold tailWord_4121326
  simp only [CollatzResearch.WordTrace]
  refine ⟨18789638533393405411029979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100211405511431495525493221 18789638533393405411029979)
  ·
    refine ⟨28184457800090108116544969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18789638533393405411029979 28184457800090108116544969)
    ·
      refine ⟨21138343350067581087408727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28184457800090108116544969 21138343350067581087408727)
      ·
        refine ⟨31707515025101371631113091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21138343350067581087408727 31707515025101371631113091)
        ·
          refine ⟨47561272537652057446669637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31707515025101371631113091 47561272537652057446669637)
          ·
            refine ⟨8917738600809760771250557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47561272537652057446669637 8917738600809760771250557)
            ·
              refine ⟨3344151975303660289218959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8917738600809760771250557 3344151975303660289218959)
              ·
                refine ⟨5016227962955490433828439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344151975303660289218959 5016227962955490433828439)
                ·
                  refine ⟨7524341944433235650742659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016227962955490433828439 7524341944433235650742659)
                  ·
                    refine ⟨11286512916649853476113989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7524341944433235650742659 11286512916649853476113989)
                    ·
                      refine ⟨2116221171871847526771373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11286512916649853476113989 2116221171871847526771373)
                      ·
                        rfl

theorem cell23_4121326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_4121326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121326 prefixEnd_4121326 := by exact prefixLift 4121326
  have htrace : WordTrace (prefixWord ++ tailWord_4121326) baseStart_4121326 baseEnd_4121326 := by
    simpa [prefixWord, tailWord_4121326, baseEnd_4121326] using wordTrace_append hprefix tailTrace_4121326
  have hstable : (prefixWord ++ tailWord_4121326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121326).length < 2 ^ (prefixWord ++ tailWord_4121326).sum := by decide
  have hdescent : baseEnd_4121326 < baseStart_4121326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121355 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 5]
def baseStart_4121355 : Nat := 118140960795 + 4121355 * 2 ^ 59
def prefixEnd_4121355 : Nat := 4983230072969 + 3 ^ 40 * 4121355 * 2
def baseEnd_4121355 : Nat := 2116236062810827913308739

theorem tailTrace_4121355 : CollatzResearch.WordTrace tailWord_4121355 prefixEnd_4121355 2116236062810827913308739 := by
  unfold tailWord_4121355
  simp only [CollatzResearch.WordTrace]
  refine ⟨150318165984042181241045519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100212110656028120827363679 150318165984042181241045519)
  ·
    refine ⟨225477248976063271861568279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150318165984042181241045519 225477248976063271861568279)
    ·
      refine ⟨338215873464094907792352419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225477248976063271861568279 338215873464094907792352419)
      ·
        refine ⟨507323810196142361688528629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338215873464094907792352419 507323810196142361688528629)
        ·
          refine ⟨47561607205888346408299559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 507323810196142361688528629 47561607205888346408299559)
          ·
            refine ⟨71342410808832519612449339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47561607205888346408299559 71342410808832519612449339)
            ·
              refine ⟨107013616213248779418674009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71342410808832519612449339 107013616213248779418674009)
              ·
                refine ⟨80260212159936584564005507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107013616213248779418674009 80260212159936584564005507)
                ·
                  refine ⟨120390318239904876846008261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80260212159936584564005507 120390318239904876846008261)
                  ·
                    refine ⟨22573184669982164408626549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120390318239904876846008261 22573184669982164408626549)
                    ·
                      refine ⟨2116236062810827913308739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22573184669982164408626549 2116236062810827913308739)
                      ·
                        rfl

theorem cell23_4121355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_4121355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121355 prefixEnd_4121355 := by exact prefixLift 4121355
  have htrace : WordTrace (prefixWord ++ tailWord_4121355) baseStart_4121355 baseEnd_4121355 := by
    simpa [prefixWord, tailWord_4121355, baseEnd_4121355] using wordTrace_append hprefix tailTrace_4121355
  have hstable : (prefixWord ++ tailWord_4121355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121355).length < 2 ^ (prefixWord ++ tailWord_4121355).sum := by decide
  have hdescent : baseEnd_4121355 < baseStart_4121355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121359 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 2, 1, 3]
def baseStart_4121359 : Nat := 118140960795 + 4121359 * 2 ^ 59
def prefixEnd_4121359 : Nat := 4983230072969 + 3 ^ 40 * 4121359 * 2
def baseEnd_4121359 : Nat := 2116238116733445897658721

theorem tailTrace_4121359 : CollatzResearch.WordTrace tailWord_4121359 prefixEnd_4121359 2116238116733445897658721 := by
  unfold tailWord_4121359
  simp only [CollatzResearch.WordTrace]
  refine ⟨150318311876027689924191131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100212207917351793282794087 150318311876027689924191131)
  ·
    refine ⟨225477467814041534886286697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150318311876027689924191131 225477467814041534886286697)
    ·
      refine ⟨169108100860531151164715023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225477467814041534886286697 169108100860531151164715023)
      ·
        refine ⟨253662151290796726747072535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169108100860531151164715023 253662151290796726747072535)
        ·
          refine ⟨380493226936195090120608803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253662151290796726747072535 380493226936195090120608803)
          ·
            refine ⟨570739840404292635180913205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380493226936195090120608803 570739840404292635180913205)
            ·
              refine ⟨53506860037902434548210613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 570739840404292635180913205 53506860037902434548210613)
              ·
                refine ⟨5016268128553353238894745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53506860037902434548210613 5016268128553353238894745)
                ·
                  refine ⟨3762201096415014929171059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5016268128553353238894745 3762201096415014929171059)
                  ·
                    refine ⟨5643301644622522393756589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3762201096415014929171059 5643301644622522393756589)
                    ·
                      refine ⟨2116238116733445897658721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5643301644622522393756589 2116238116733445897658721)
                      ·
                        rfl

theorem cell23_4121359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 1, 3].length) (baseStart_4121359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121359 prefixEnd_4121359 := by exact prefixLift 4121359
  have htrace : WordTrace (prefixWord ++ tailWord_4121359) baseStart_4121359 baseEnd_4121359 := by
    simpa [prefixWord, tailWord_4121359, baseEnd_4121359] using wordTrace_append hprefix tailTrace_4121359
  have hstable : (prefixWord ++ tailWord_4121359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121359).length < 2 ^ (prefixWord ++ tailWord_4121359).sum := by decide
  have hdescent : baseEnd_4121359 < baseStart_4121359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121380 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 1, 2, 3]
def baseStart_4121380 : Nat := 118140960795 + 4121380 * 2 ^ 59
def prefixEnd_4121380 : Nat := 4983230072969 + 3 ^ 40 * 4121380 * 2
def baseEnd_4121380 : Nat := 2116248899827190315496125

theorem tailTrace_4121380 : CollatzResearch.WordTrace tailWord_4121380 prefixEnd_4121380 2116248899827190315496125 := by
  unfold tailWord_4121380
  simp only [CollatzResearch.WordTrace]
  refine ⟨75159538904475805255352797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100212718539301073673803729 75159538904475805255352797)
  ·
    refine ⟨28184827089178426970757299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75159538904475805255352797 28184827089178426970757299)
    ·
      refine ⟨42277240633767640456135949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28184827089178426970757299 42277240633767640456135949)
      ·
        refine ⟨15853965237662865171050981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42277240633767640456135949 15853965237662865171050981)
        ·
          refine ⟨2972618482061787219572059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15853965237662865171050981 2972618482061787219572059)
          ·
            refine ⟨4458927723092680829358089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972618482061787219572059 4458927723092680829358089)
            ·
              refine ⟨3344195792319510622018567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458927723092680829358089 3344195792319510622018567)
              ·
                refine ⟨5016293688479265933027851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344195792319510622018567 5016293688479265933027851)
                ·
                  refine ⟨7524440532718898899541777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016293688479265933027851 7524440532718898899541777)
                  ·
                    refine ⟨5643330399539174174656333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7524440532718898899541777 5643330399539174174656333)
                    ·
                      refine ⟨2116248899827190315496125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5643330399539174174656333 2116248899827190315496125)
                      ·
                        rfl

theorem cell23_4121380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_4121380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121380 prefixEnd_4121380 := by exact prefixLift 4121380
  have htrace : WordTrace (prefixWord ++ tailWord_4121380) baseStart_4121380 baseEnd_4121380 := by
    simpa [prefixWord, tailWord_4121380, baseEnd_4121380] using wordTrace_append hprefix tailTrace_4121380
  have hstable : (prefixWord ++ tailWord_4121380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121380).length < 2 ^ (prefixWord ++ tailWord_4121380).sum := by decide
  have hdescent : baseEnd_4121380 < baseStart_4121380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121432 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 1, 5, 3]
def baseStart_4121432 : Nat := 118140960795 + 4121432 * 2 ^ 59
def prefixEnd_4121432 : Nat := 4983230072969 + 3 ^ 40 * 4121432 * 2
def baseEnd_4121432 : Nat := 2116275600821224112045885

theorem tailTrace_4121432 : CollatzResearch.WordTrace tailWord_4121432 prefixEnd_4121432 2116275600821224112045885 := by
  unfold tailWord_4121432
  simp only [CollatzResearch.WordTrace]
  refine ⟨75160487202381611695799275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100213982936508815594399033 75160487202381611695799275)
  ·
    refine ⟨112740730803572417543698913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75160487202381611695799275 112740730803572417543698913)
    ·
      refine ⟨84555548102679313157774185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112740730803572417543698913 84555548102679313157774185)
      ·
        refine ⟨63416661077009484868330639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84555548102679313157774185 63416661077009484868330639)
        ·
          refine ⟨95124991615514227302495959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63416661077009484868330639 95124991615514227302495959)
          ·
            refine ⟨142687487423271340953743939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95124991615514227302495959 142687487423271340953743939)
            ·
              refine ⟨214031231134907011430615909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142687487423271340953743939 214031231134907011430615909)
              ·
                refine ⟨40130855837795064643240483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214031231134907011430615909 40130855837795064643240483)
                ·
                  refine ⟨60196283756692596964860725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40130855837795064643240483 60196283756692596964860725)
                  ·
                    refine ⟨5643401602189930965455693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60196283756692596964860725 5643401602189930965455693)
                    ·
                      refine ⟨2116275600821224112045885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5643401602189930965455693 2116275600821224112045885)
                      ·
                        rfl

theorem cell23_4121432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_4121432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121432 prefixEnd_4121432 := by exact prefixLift 4121432
  have htrace : WordTrace (prefixWord ++ tailWord_4121432) baseStart_4121432 baseEnd_4121432 := by
    simpa [prefixWord, tailWord_4121432, baseEnd_4121432] using wordTrace_append hprefix tailTrace_4121432
  have hstable : (prefixWord ++ tailWord_4121432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121432).length < 2 ^ (prefixWord ++ tailWord_4121432).sum := by decide
  have hdescent : baseEnd_4121432 < baseStart_4121432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121472 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_4121472 : Nat := 118140960795 + 4121472 * 2 ^ 59
def prefixEnd_4121472 : Nat := 4983230072969 + 3 ^ 40 * 4121472 * 2
def baseEnd_4121472 : Nat := 2116296140047403955545701

theorem tailTrace_4121472 : CollatzResearch.WordTrace tailWord_4121472 prefixEnd_4121472 2116296140047403955545701 := by
  unfold tailWord_4121472
  simp only [CollatzResearch.WordTrace]
  refine ⟨75161216662309155111527335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100214955549745540148703113 75161216662309155111527335)
  ·
    refine ⟨112741824993463732667291003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75161216662309155111527335 112741824993463732667291003)
    ·
      refine ⟨169112737490195599000936505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112741824993463732667291003 169112737490195599000936505)
      ·
        refine ⟨126834553117646699250702379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169112737490195599000936505 126834553117646699250702379)
        ·
          refine ⟨190251829676470048876053569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126834553117646699250702379 190251829676470048876053569)
          ·
            refine ⟨142688872257352536657040177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190251829676470048876053569 142688872257352536657040177)
            ·
              refine ⟨107016654193014402492780133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142688872257352536657040177 107016654193014402492780133)
              ·
                refine ⟨20065622661190200467396275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107016654193014402492780133 20065622661190200467396275)
                ·
                  refine ⟨30098433991785300701094413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20065622661190200467396275 30098433991785300701094413)
                  ·
                    refine ⟨11286912746919487762910405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30098433991785300701094413 11286912746919487762910405)
                    ·
                      refine ⟨2116296140047403955545701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11286912746919487762910405 2116296140047403955545701)
                      ·
                        rfl

theorem cell23_4121472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_4121472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121472 prefixEnd_4121472 := by exact prefixLift 4121472
  have htrace : WordTrace (prefixWord ++ tailWord_4121472) baseStart_4121472 baseEnd_4121472 := by
    simpa [prefixWord, tailWord_4121472, baseEnd_4121472] using wordTrace_append hprefix tailTrace_4121472
  have hstable : (prefixWord ++ tailWord_4121472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121472).length < 2 ^ (prefixWord ++ tailWord_4121472).sum := by decide
  have hdescent : baseEnd_4121472 < baseStart_4121472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121489 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 4, 4, 2]
def baseStart_4121489 : Nat := 118140960795 + 4121489 * 2 ^ 59
def prefixEnd_4121489 : Nat := 4983230072969 + 3 ^ 40 * 4121489 * 2
def baseEnd_4121489 : Nat := 2116304869218530389033123

theorem tailTrace_4121489 : CollatzResearch.WordTrace tailWord_4121489 prefixEnd_4121489 2116304869218530389033123 := by
  unfold tailWord_4121489
  simp only [CollatzResearch.WordTrace]
  refine ⟨150323053365556722126423521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100215368910371148084282347 150323053365556722126423521)
  ·
    refine ⟨112742290024167541594817641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150323053365556722126423521 112742290024167541594817641)
    ·
      refine ⟨84556717518125656196113231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112742290024167541594817641 84556717518125656196113231)
      ·
        refine ⟨126835076277188484294169847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84556717518125656196113231 126835076277188484294169847)
        ·
          refine ⟨190252614415782726441254771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126835076277188484294169847 190252614415782726441254771)
          ·
            refine ⟨285378921623674089661882157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190252614415782726441254771 285378921623674089661882157)
            ·
              refine ⟨107017095608877783623205809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285378921623674089661882157 107017095608877783623205809)
              ·
                refine ⟨80262821706658337717404357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107017095608877783623205809 80262821706658337717404357)
                ·
                  refine ⟨15049279069998438322013317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80262821706658337717404357 15049279069998438322013317)
                  ·
                    refine ⟨2821739825624707185377497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15049279069998438322013317 2821739825624707185377497)
                    ·
                      refine ⟨2116304869218530389033123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821739825624707185377497 2116304869218530389033123)
                      ·
                        rfl

theorem cell23_4121489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_4121489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121489 prefixEnd_4121489 := by exact prefixLift 4121489
  have htrace : WordTrace (prefixWord ++ tailWord_4121489) baseStart_4121489 baseEnd_4121489 := by
    simpa [prefixWord, tailWord_4121489, baseEnd_4121489] using wordTrace_append hprefix tailTrace_4121489
  have hstable : (prefixWord ++ tailWord_4121489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121489).length < 2 ^ (prefixWord ++ tailWord_4121489).sum := by decide
  have hdescent : baseEnd_4121489 < baseStart_4121489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121506 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_4121506 : Nat := 118140960795 + 4121506 * 2 ^ 59
def prefixEnd_4121506 : Nat := 4983230072969 + 3 ^ 40 * 4121506 * 2
def baseEnd_4121506 : Nat := 2116313598389656822520545

theorem tailTrace_4121506 : CollatzResearch.WordTrace tailWord_4121506 prefixEnd_4121506 2116313598389656822520545 := by
  unfold tailWord_4121506
  simp only [CollatzResearch.WordTrace]
  refine ⟨37580918351623783507448093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100215782270996756019861581 37580918351623783507448093)
  ·
    refine ⟨14092844381858918815293035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37580918351623783507448093 14092844381858918815293035)
    ·
      refine ⟨21139266572788378222939553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14092844381858918815293035 21139266572788378222939553)
      ·
        refine ⟨15854449929591283667204665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21139266572788378222939553 15854449929591283667204665)
        ·
          refine ⟨11890837447193462750403499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15854449929591283667204665 11890837447193462750403499)
          ·
            refine ⟨17836256170790194125605249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11890837447193462750403499 17836256170790194125605249)
            ·
              refine ⟨13377192128092645594203937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17836256170790194125605249 13377192128092645594203937)
              ·
                refine ⟨10032894096069484195652953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13377192128092645594203937 10032894096069484195652953)
                ·
                  refine ⟨7524670572052113146739715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10032894096069484195652953 7524670572052113146739715)
                  ·
                    refine ⟨11287005858078169720109573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7524670572052113146739715 11287005858078169720109573)
                    ·
                      refine ⟨2116313598389656822520545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11287005858078169720109573 2116313598389656822520545)
                      ·
                        rfl

theorem cell23_4121506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_4121506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121506 prefixEnd_4121506 := by exact prefixLift 4121506
  have htrace : WordTrace (prefixWord ++ tailWord_4121506) baseStart_4121506 baseEnd_4121506 := by
    simpa [prefixWord, tailWord_4121506, baseEnd_4121506] using wordTrace_append hprefix tailTrace_4121506
  have hstable : (prefixWord ++ tailWord_4121506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121506).length < 2 ^ (prefixWord ++ tailWord_4121506).sum := by decide
  have hdescent : baseEnd_4121506 < baseStart_4121506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121516 : List Nat := [2, 2, 1, 1, 1, 1, 2, 8, 1, 4]
def baseStart_4121516 : Nat := 118140960795 + 4121516 * 2 ^ 59
def prefixEnd_4121516 : Nat := 4983230072969 + 3 ^ 40 * 4121516 * 2
def baseEnd_4121516 : Nat := 705439577732067261131833

theorem tailTrace_4121516 : CollatzResearch.WordTrace tailWord_4121516 prefixEnd_4121516 705439577732067261131833 := by
  unfold tailWord_4121516
  simp only [CollatzResearch.WordTrace]
  refine ⟨75162019068229452868828201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100216025424305937158437601 75162019068229452868828201)
  ·
    refine ⟨56371514301172089651621151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75162019068229452868828201 56371514301172089651621151)
    ·
      refine ⟨84557271451758134477431727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56371514301172089651621151 84557271451758134477431727)
      ·
        refine ⟨126835907177637201716147591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84557271451758134477431727 126835907177637201716147591)
        ·
          refine ⟨190253860766455802574221387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126835907177637201716147591 190253860766455802574221387)
          ·
            refine ⟨285380791149683703861332081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190253860766455802574221387 285380791149683703861332081)
            ·
              refine ⟨214035593362262777895999061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285380791149683703861332081 214035593362262777895999061)
              ·
                refine ⟨2508229609714016928468739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 214035593362262777895999061 2508229609714016928468739)
                ·
                  refine ⟨3762344414571025392703109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2508229609714016928468739 3762344414571025392703109)
                  ·
                    refine ⟨705439577732067261131833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3762344414571025392703109 705439577732067261131833)
                    ·
                      rfl

theorem cell23_4121516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_4121516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121516 prefixEnd_4121516 := by exact prefixLift 4121516
  have htrace : WordTrace (prefixWord ++ tailWord_4121516) baseStart_4121516 baseEnd_4121516 := by
    simpa [prefixWord, tailWord_4121516, baseEnd_4121516] using wordTrace_append hprefix tailTrace_4121516
  have hstable : (prefixWord ++ tailWord_4121516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121516).length < 2 ^ (prefixWord ++ tailWord_4121516).sum := by decide
  have hdescent : baseEnd_4121516 < baseStart_4121516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121529 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 6]
def baseStart_4121529 : Nat := 118140960795 + 4121529 * 2 ^ 59
def prefixEnd_4121529 : Nat := 4983230072969 + 3 ^ 40 * 4121529 * 2
def baseEnd_4121529 : Nat := 235147267604967803614771

theorem tailTrace_4121529 : CollatzResearch.WordTrace tailWord_4121529 prefixEnd_4121529 235147267604967803614771 := by
  unfold tailWord_4121529
  simp only [CollatzResearch.WordTrace]
  refine ⟨150324512285411808957879641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100216341523607872638586427 150324512285411808957879641)
  ·
    refine ⟨112743384214058856718409731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150324512285411808957879641 112743384214058856718409731)
    ·
      refine ⟨169115076321088285077614597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112743384214058856718409731 169115076321088285077614597)
      ·
        refine ⟨31709076810204053452052737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169115076321088285077614597 31709076810204053452052737)
        ·
          refine ⟨23781807607653040089039553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31709076810204053452052737 23781807607653040089039553)
          ·
            refine ⟨17836355705739780066779665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23781807607653040089039553 17836355705739780066779665)
            ·
              refine ⟨13377266779304835050084749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17836355705739780066779665 13377266779304835050084749)
              ·
                refine ⟨5016475042239313143781781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13377266779304835050084749 5016475042239313143781781)
                ·
                  refine ⟨235147267604967803614771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5016475042239313143781781 235147267604967803614771)
                  ·
                    rfl

theorem cell23_4121529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 6].length) (baseStart_4121529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121529 prefixEnd_4121529 := by exact prefixLift 4121529
  have htrace : WordTrace (prefixWord ++ tailWord_4121529) baseStart_4121529 baseEnd_4121529 := by
    simpa [prefixWord, tailWord_4121529, baseEnd_4121529] using wordTrace_append hprefix tailTrace_4121529
  have hstable : (prefixWord ++ tailWord_4121529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121529).length < 2 ^ (prefixWord ++ tailWord_4121529).sum := by decide
  have hdescent : baseEnd_4121529 < baseStart_4121529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121540 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4121540 : Nat := 118140960795 + 4121540 * 2 ^ 59
def prefixEnd_4121540 : Nat := 4983230072969 + 3 ^ 40 * 4121540 * 2
def baseEnd_4121540 : Nat := 2116331056731909689495389

theorem tailTrace_4121540 : CollatzResearch.WordTrace tailWord_4121540 prefixEnd_4121540 2116331056731909689495389 := by
  unfold tailWord_4121540
  simp only [CollatzResearch.WordTrace]
  refine ⟨75162456744185978918265037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100216608992247971891020049 75162456744185978918265037)
  ·
    refine ⟨28185921279069742094349389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75162456744185978918265037 28185921279069742094349389)
    ·
      refine ⟨10569720479651153285381021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28185921279069742094349389 10569720479651153285381021)
      ·
        refine ⟨3963645179869182482017883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10569720479651153285381021 3963645179869182482017883)
        ·
          refine ⟨5945467769803773723026825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963645179869182482017883 5945467769803773723026825)
          ·
            refine ⟨4459100827352830292270119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5945467769803773723026825 4459100827352830292270119)
            ·
              refine ⟨6688651241029245438405179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459100827352830292270119 6688651241029245438405179)
              ·
                refine ⟨10032976861543868157607769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6688651241029245438405179 10032976861543868157607769)
                ·
                  refine ⟨7524732646157901118205827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10032976861543868157607769 7524732646157901118205827)
                  ·
                    refine ⟨11287098969236851677308741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7524732646157901118205827 11287098969236851677308741)
                    ·
                      refine ⟨2116331056731909689495389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11287098969236851677308741 2116331056731909689495389)
                      ·
                        rfl

theorem cell23_4121540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4121540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121540 prefixEnd_4121540 := by exact prefixLift 4121540
  have htrace : WordTrace (prefixWord ++ tailWord_4121540) baseStart_4121540 baseEnd_4121540 := by
    simpa [prefixWord, tailWord_4121540, baseEnd_4121540] using wordTrace_append hprefix tailTrace_4121540
  have hstable : (prefixWord ++ tailWord_4121540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121540).length < 2 ^ (prefixWord ++ tailWord_4121540).sum := by decide
  have hdescent : baseEnd_4121540 < baseStart_4121540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121552 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_4121552 : Nat := 118140960795 + 4121552 * 2 ^ 59
def prefixEnd_4121552 : Nat := 4983230072969 + 3 ^ 40 * 4121552 * 2
def baseEnd_4121552 : Nat := 2116337218499763642545333

theorem tailTrace_4121552 : CollatzResearch.WordTrace tailWord_4121552 prefixEnd_4121552 2116337218499763642545333 := by
  unfold tailWord_4121552
  simp only [CollatzResearch.WordTrace]
  refine ⟨75162675582164241942983455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100216900776218989257311273 75162675582164241942983455)
  ·
    refine ⟨112744013373246362914475183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75162675582164241942983455 112744013373246362914475183)
    ·
      refine ⟨169116020059869544371712775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112744013373246362914475183 169116020059869544371712775)
      ·
        refine ⟨253674030089804316557569163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169116020059869544371712775 253674030089804316557569163)
        ·
          refine ⟨380511045134706474836353745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253674030089804316557569163 380511045134706474836353745)
          ·
            refine ⟨285383283851029856127265309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380511045134706474836353745 285383283851029856127265309)
            ·
              refine ⟨107018731444136196047724491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285383283851029856127265309 107018731444136196047724491)
              ·
                refine ⟨160528097166204294071586737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107018731444136196047724491 160528097166204294071586737)
                ·
                  refine ⟨120396072874653220553690053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160528097166204294071586737 120396072874653220553690053)
                  ·
                    refine ⟨22574263663997478853816885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120396072874653220553690053 22574263663997478853816885)
                    ·
                      refine ⟨2116337218499763642545333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22574263663997478853816885 2116337218499763642545333)
                      ·
                        rfl

theorem cell23_4121552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_4121552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121552 prefixEnd_4121552 := by exact prefixLift 4121552
  have htrace : WordTrace (prefixWord ++ tailWord_4121552) baseStart_4121552 baseEnd_4121552 := by
    simpa [prefixWord, tailWord_4121552, baseEnd_4121552] using wordTrace_append hprefix tailTrace_4121552
  have hstable : (prefixWord ++ tailWord_4121552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121552).length < 2 ^ (prefixWord ++ tailWord_4121552).sum := by decide
  have hdescent : baseEnd_4121552 < baseStart_4121552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121596 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_4121596 : Nat := 118140960795 + 4121596 * 2 ^ 59
def prefixEnd_4121596 : Nat := 4983230072969 + 3 ^ 40 * 4121596 * 2
def baseEnd_4121596 : Nat := 2116359811648561470395131

theorem tailTrace_4121596 : CollatzResearch.WordTrace tailWord_4121596 prefixEnd_4121596 2116359811648561470395131 := by
  unfold tailWord_4121596
  simp only [CollatzResearch.WordTrace]
  refine ⟨75163477988084539700284321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100217970650779386267045761 75163477988084539700284321)
  ·
    refine ⟨56372608491063404775213241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75163477988084539700284321 56372608491063404775213241)
    ·
      refine ⟨42279456368297553581409931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56372608491063404775213241 42279456368297553581409931)
      ·
        refine ⟨63419184552446330372114897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42279456368297553581409931 63419184552446330372114897)
        ·
          refine ⟨47564388414334747779086173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63419184552446330372114897 47564388414334747779086173)
          ·
            refine ⟨17836645655375530417157315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47564388414334747779086173 17836645655375530417157315)
            ·
              refine ⟨26754968483063295625735973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17836645655375530417157315 26754968483063295625735973)
              ·
                refine ⟨5016556590574367929825495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26754968483063295625735973 5016556590574367929825495)
                ·
                  refine ⟨7524834885861551894738243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016556590574367929825495 7524834885861551894738243)
                  ·
                    refine ⟨11287252328792327842107365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7524834885861551894738243 11287252328792327842107365)
                    ·
                      refine ⟨2116359811648561470395131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11287252328792327842107365 2116359811648561470395131)
                      ·
                        rfl

theorem cell23_4121596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_4121596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121596 prefixEnd_4121596 := by exact prefixLift 4121596
  have htrace : WordTrace (prefixWord ++ tailWord_4121596) baseStart_4121596 baseEnd_4121596 := by
    simpa [prefixWord, tailWord_4121596, baseEnd_4121596] using wordTrace_append hprefix tailTrace_4121596
  have hstable : (prefixWord ++ tailWord_4121596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121596).length < 2 ^ (prefixWord ++ tailWord_4121596).sum := by decide
  have hdescent : baseEnd_4121596 < baseStart_4121596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121609 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 4]
def baseStart_4121609 : Nat := 118140960795 + 4121609 * 2 ^ 59
def prefixEnd_4121609 : Nat := 4983230072969 + 3 ^ 40 * 4121609 * 2
def baseEnd_4121609 : Nat := 2116366486897069919532571

theorem tailTrace_4121609 : CollatzResearch.WordTrace tailWord_4121609 prefixEnd_4121609 2116366486897069919532571 := by
  unfold tailWord_4121609
  simp only [CollatzResearch.WordTrace]
  refine ⟨150327430125121982620791881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100218286750081321747194587 150327430125121982620791881)
  ·
    refine ⟨112745572593841486965593911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150327430125121982620791881 112745572593841486965593911)
    ·
      refine ⟨169118358890762230448390867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112745572593841486965593911 169118358890762230448390867)
      ·
        refine ⟨253677538336143345672586301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169118358890762230448390867 253677538336143345672586301)
        ·
          refine ⟨95129076876053754627219863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253677538336143345672586301 95129076876053754627219863)
          ·
            refine ⟨142693615314080631940829795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95129076876053754627219863 142693615314080631940829795)
            ·
              refine ⟨214040422971120947911244693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142693615314080631940829795 214040422971120947911244693)
              ·
                refine ⟨10033144826771294433339595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214040422971120947911244693 10033144826771294433339595)
                ·
                  refine ⟨15049717240156941650009393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10033144826771294433339595 15049717240156941650009393)
                  ·
                    refine ⟨11287287930117706237507045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15049717240156941650009393 11287287930117706237507045)
                    ·
                      refine ⟨2116366486897069919532571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11287287930117706237507045 2116366486897069919532571)
                      ·
                        rfl

theorem cell23_4121609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_4121609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121609 prefixEnd_4121609 := by exact prefixLift 4121609
  have htrace : WordTrace (prefixWord ++ tailWord_4121609) baseStart_4121609 baseEnd_4121609 := by
    simpa [prefixWord, tailWord_4121609, baseEnd_4121609] using wordTrace_append hprefix tailTrace_4121609
  have hstable : (prefixWord ++ tailWord_4121609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121609).length < 2 ^ (prefixWord ++ tailWord_4121609).sum := by decide
  have hdescent : baseEnd_4121609 < baseStart_4121609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121636 : List Nat := [2, 3, 1, 4, 1, 2, 2, 8]
def baseStart_4121636 : Nat := 118140960795 + 4121636 * 2 ^ 59
def prefixEnd_4121636 : Nat := 4983230072969 + 3 ^ 40 * 4121636 * 2
def baseEnd_4121636 : Nat := 78384457439805233847961

theorem tailTrace_4121636 : CollatzResearch.WordTrace tailWord_4121636 prefixEnd_4121636 78384457439805233847961 := by
  unfold tailWord_4121636
  simp only [CollatzResearch.WordTrace]
  refine ⟨75164207448012083116012381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100218943264016110821349841 75164207448012083116012381)
  ·
    refine ⟨28186577793004531168504643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75164207448012083116012381 28186577793004531168504643)
    ·
      refine ⟨42279866689506796752756965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28186577793004531168504643 42279866689506796752756965)
      ·
        refine ⟨7927475004282524391141931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42279866689506796752756965 7927475004282524391141931)
        ·
          refine ⟨11891212506423786586712897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927475004282524391141931 11891212506423786586712897)
          ·
            refine ⟨8918409379817839940034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11891212506423786586712897 8918409379817839940034673)
            ·
              refine ⟨6688807034863379955026005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8918409379817839940034673 6688807034863379955026005)
              ·
                refine ⟨78384457439805233847961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6688807034863379955026005 78384457439805233847961)
                ·
                  rfl

theorem cell23_4121636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 8].length) (baseStart_4121636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121636 prefixEnd_4121636 := by exact prefixLift 4121636
  have htrace : WordTrace (prefixWord ++ tailWord_4121636) baseStart_4121636 baseEnd_4121636 := by
    simpa [prefixWord, tailWord_4121636, baseEnd_4121636] using wordTrace_append hprefix tailTrace_4121636
  have hstable : (prefixWord ++ tailWord_4121636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121636).length < 2 ^ (prefixWord ++ tailWord_4121636).sum := by decide
  have hdescent : baseEnd_4121636 < baseStart_4121636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121689 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_4121689 : Nat := 118140960795 + 4121689 * 2 ^ 59
def prefixEnd_4121689 : Nat := 4983230072969 + 3 ^ 40 * 4121689 * 2
def baseEnd_4121689 : Nat := 2116407565349429606532203

theorem tailTrace_4121689 : CollatzResearch.WordTrace tailWord_4121689 prefixEnd_4121689 2116407565349429606532203 := by
  unfold tailWord_4121689
  simp only [CollatzResearch.WordTrace]
  refine ⟨150330347964832156283704121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100220231976554770855802747 150330347964832156283704121)
  ·
    refine ⟨112747760973624117212778091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150330347964832156283704121 112747760973624117212778091)
    ·
      refine ⟨169121641460436175819167137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112747760973624117212778091 169121641460436175819167137)
      ·
        refine ⟨126841231095327131864375353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169121641460436175819167137 126841231095327131864375353)
        ·
          refine ⟨95130923321495348898281515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126841231095327131864375353 95130923321495348898281515)
          ·
            refine ⟨142696384982243023347422273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95130923321495348898281515 142696384982243023347422273)
            ·
              refine ⟨107022288736682267510566705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142696384982243023347422273 107022288736682267510566705)
              ·
                refine ⟨80266716552511700632925029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107022288736682267510566705 80266716552511700632925029)
                ·
                  refine ⟨15050009353595943868673443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80266716552511700632925029 15050009353595943868673443)
                  ·
                    refine ⟨22575014030393915803010165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15050009353595943868673443 22575014030393915803010165)
                    ·
                      refine ⟨2116407565349429606532203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22575014030393915803010165 2116407565349429606532203)
                      ·
                        rfl

theorem cell23_4121689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_4121689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121689 prefixEnd_4121689 := by exact prefixLift 4121689
  have htrace : WordTrace (prefixWord ++ tailWord_4121689) baseStart_4121689 baseEnd_4121689 := by
    simpa [prefixWord, tailWord_4121689, baseEnd_4121689] using wordTrace_append hprefix tailTrace_4121689
  have hstable : (prefixWord ++ tailWord_4121689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121689).length < 2 ^ (prefixWord ++ tailWord_4121689).sum := by decide
  have hdescent : baseEnd_4121689 < baseStart_4121689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121703 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_4121703 : Nat := 118140960795 + 4121703 * 2 ^ 59
def prefixEnd_4121703 : Nat := 4983230072969 + 3 ^ 40 * 4121703 * 2
def baseEnd_4121703 : Nat := 2116414754078592551757139

theorem tailTrace_4121703 : CollatzResearch.WordTrace tailWord_4121703 prefixEnd_4121703 2116414754078592551757139 := by
  unfold tailWord_4121703
  simp only [CollatzResearch.WordTrace]
  refine ⟨150330858586781436674713763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100220572391187624449809175 150330858586781436674713763)
  ·
    refine ⟨225496287880172155012070645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150330858586781436674713763 225496287880172155012070645)
    ·
      refine ⟨21140276988766139532381623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225496287880172155012070645 21140276988766139532381623)
      ·
        refine ⟨31710415483149209298572435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21140276988766139532381623 31710415483149209298572435)
        ·
          refine ⟨47565623224723813947858653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31710415483149209298572435 47565623224723813947858653)
          ·
            refine ⟨17837108709271430230446995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47565623224723813947858653 17837108709271430230446995)
            ·
              refine ⟨26755663063907145345670493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17837108709271430230446995 26755663063907145345670493)
              ·
                refine ⟨10033373648965179504626435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26755663063907145345670493 10033373648965179504626435)
                ·
                  refine ⟨15050060473447769256939653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10033373648965179504626435 15050060473447769256939653)
                  ·
                    refine ⟨2821886338771456735676185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15050060473447769256939653 2821886338771456735676185)
                    ·
                      refine ⟨2116414754078592551757139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821886338771456735676185 2116414754078592551757139)
                      ·
                        rfl

theorem cell23_4121703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_4121703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121703 prefixEnd_4121703 := by exact prefixLift 4121703
  have htrace : WordTrace (prefixWord ++ tailWord_4121703) baseStart_4121703 baseEnd_4121703 := by
    simpa [prefixWord, tailWord_4121703, baseEnd_4121703] using wordTrace_append hprefix tailTrace_4121703
  have hstable : (prefixWord ++ tailWord_4121703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121703).length < 2 ^ (prefixWord ++ tailWord_4121703).sum := by decide
  have hdescent : baseEnd_4121703 < baseStart_4121703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121737 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 2, 2, 2]
def baseStart_4121737 : Nat := 118140960795 + 4121737 * 2 ^ 59
def prefixEnd_4121737 : Nat := 4983230072969 + 3 ^ 40 * 4121737 * 2
def baseEnd_4121737 : Nat := 2116432212420845418731983

theorem tailTrace_4121737 : CollatzResearch.WordTrace tailWord_4121737 prefixEnd_4121737 2116432212420845418731983 := by
  unfold tailWord_4121737
  simp only [CollatzResearch.WordTrace]
  refine ⟨150332098668658260481451465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100221399112438840320967643 150332098668658260481451465)
  ·
    refine ⟨112749074001493695361088599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150332098668658260481451465 112749074001493695361088599)
    ·
      refine ⟨169123611002240543041632899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112749074001493695361088599 169123611002240543041632899)
      ·
        refine ⟨253685416503360814562449349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169123611002240543041632899 253685416503360814562449349)
        ·
          refine ⟨47566015594380152730459253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253685416503360814562449349 47566015594380152730459253)
          ·
            refine ⟨4459313961973139318480555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47566015594380152730459253 4459313961973139318480555)
            ·
              refine ⟨6688970942959708977720833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459313961973139318480555 6688970942959708977720833)
              ·
                refine ⟨5016728207219781733290625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6688970942959708977720833 5016728207219781733290625)
                ·
                  refine ⟨3762546155414836299967969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5016728207219781733290625 3762546155414836299967969)
                  ·
                    refine ⟨2821909616561127224975977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3762546155414836299967969 2821909616561127224975977)
                    ·
                      refine ⟨2116432212420845418731983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821909616561127224975977 2116432212420845418731983)
                      ·
                        rfl

theorem cell23_4121737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 2, 2].length) (baseStart_4121737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121737 prefixEnd_4121737 := by exact prefixLift 4121737
  have htrace : WordTrace (prefixWord ++ tailWord_4121737) baseStart_4121737 baseEnd_4121737 := by
    simpa [prefixWord, tailWord_4121737, baseEnd_4121737] using wordTrace_append hprefix tailTrace_4121737
  have hstable : (prefixWord ++ tailWord_4121737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121737).length < 2 ^ (prefixWord ++ tailWord_4121737).sum := by decide
  have hdescent : baseEnd_4121737 < baseStart_4121737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121754 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2]
def baseStart_4121754 : Nat := 118140960795 + 4121754 * 2 ^ 59
def prefixEnd_4121754 : Nat := 4983230072969 + 3 ^ 40 * 4121754 * 2
def baseEnd_4121754 : Nat := 2116440941591971852219405

theorem tailTrace_4121754 : CollatzResearch.WordTrace tailWord_4121754 prefixEnd_4121754 2116440941591971852219405 := by
  unfold tailWord_4121754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37583179677399168096205079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100221812473064448256546877 37583179677399168096205079)
  ·
    refine ⟨56374769516098752144307619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37583179677399168096205079 56374769516098752144307619)
    ·
      refine ⟨84562154274148128216461429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56374769516098752144307619 84562154274148128216461429)
      ·
        refine ⟨7927701963201387020293259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84562154274148128216461429 7927701963201387020293259)
        ·
          refine ⟨11891552944802080530439889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927701963201387020293259 11891552944802080530439889)
          ·
            refine ⟨8918664708601560397829917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11891552944802080530439889 8918664708601560397829917)
            ·
              refine ⟨3344499265725585149186219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8918664708601560397829917 3344499265725585149186219)
              ·
                refine ⟨5016748898588377723779329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344499265725585149186219 5016748898588377723779329)
                ·
                  refine ⟨3762561673941283292834497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5016748898588377723779329 3762561673941283292834497)
                  ·
                    refine ⟨2821921255455962469625873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3762561673941283292834497 2821921255455962469625873)
                    ·
                      refine ⟨2116440941591971852219405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821921255455962469625873 2116440941591971852219405)
                      ·
                        rfl

theorem cell23_4121754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_4121754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121754 prefixEnd_4121754 := by exact prefixLift 4121754
  have htrace : WordTrace (prefixWord ++ tailWord_4121754) baseStart_4121754 baseEnd_4121754 := by
    simpa [prefixWord, tailWord_4121754, baseEnd_4121754] using wordTrace_append hprefix tailTrace_4121754
  have hstable : (prefixWord ++ tailWord_4121754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121754).length < 2 ^ (prefixWord ++ tailWord_4121754).sum := by decide
  have hdescent : baseEnd_4121754 < baseStart_4121754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121756 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_4121756 : Nat := 118140960795 + 4121756 * 2 ^ 59
def prefixEnd_4121756 : Nat := 4983230072969 + 3 ^ 40 * 4121756 * 2
def baseEnd_4121756 : Nat := 705480656184426948131465

theorem tailTrace_4121756 : CollatzResearch.WordTrace tailWord_4121756 prefixEnd_4121756 705480656184426948131465 := by
  unfold tailWord_4121756
  simp only [CollatzResearch.WordTrace]
  refine ⟨75166395827794713363196561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100221861103726284484262081 75166395827794713363196561)
  ·
    refine ⟨56374796870846035022397421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75166395827794713363196561 56374796870846035022397421)
    ·
      refine ⟨21140548826567263133399033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56374796870846035022397421 21140548826567263133399033)
      ·
        refine ⟨15855411619925447350049275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21140548826567263133399033 15855411619925447350049275)
        ·
          refine ⟨23783117429888171025073913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15855411619925447350049275 23783117429888171025073913)
          ·
            refine ⟨17837338072416128268805435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23783117429888171025073913 17837338072416128268805435)
            ·
              refine ⟨26756007108624192403208153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17837338072416128268805435 26756007108624192403208153)
              ·
                refine ⟨20067005331468144302406115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26756007108624192403208153 20067005331468144302406115)
                ·
                  refine ⟨30100507997202216453609173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20067005331468144302406115 30100507997202216453609173)
                  ·
                    refine ⟨705480656184426948131465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30100507997202216453609173 705480656184426948131465)
                    ·
                      rfl

theorem cell23_4121756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_4121756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121756 prefixEnd_4121756 := by exact prefixLift 4121756
  have htrace : WordTrace (prefixWord ++ tailWord_4121756) baseStart_4121756 baseEnd_4121756 := by
    simpa [prefixWord, tailWord_4121756, baseEnd_4121756] using wordTrace_append hprefix tailTrace_4121756
  have hstable : (prefixWord ++ tailWord_4121756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121756).length < 2 ^ (prefixWord ++ tailWord_4121756).sum := by decide
  have hdescent : baseEnd_4121756 < baseStart_4121756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121794 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4121794 : Nat := 118140960795 + 4121794 * 2 ^ 59
def prefixEnd_4121794 : Nat := 4983230072969 + 3 ^ 40 * 4121794 * 2
def baseEnd_4121794 : Nat := 235162386757572410635469

theorem tailTrace_4121794 : CollatzResearch.WordTrace tailWord_4121794 prefixEnd_4121794 235162386757572410635469 := by
  unfold tailWord_4121794
  simp only [CollatzResearch.WordTrace]
  refine ⟨37583544407362939804069109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100222785086301172810850957 37583544407362939804069109)
  ·
    refine ⟨3523457288190275606631479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37583544407362939804069109 3523457288190275606631479)
    ·
      refine ⟨5285185932285413409947219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3523457288190275606631479 5285185932285413409947219)
      ·
        refine ⟨7927778898428120114920829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285185932285413409947219 7927778898428120114920829)
        ·
          refine ⟨2972917086910545043095311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7927778898428120114920829 2972917086910545043095311)
          ·
            refine ⟨4459375630365817564642967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972917086910545043095311 4459375630365817564642967)
            ·
              refine ⟨6689063445548726346964451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459375630365817564642967 6689063445548726346964451)
              ·
                refine ⟨10033595168323089520446677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6689063445548726346964451 10033595168323089520446677)
                ·
                  refine ⟨235162386757572410635469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10033595168323089520446677 235162386757572410635469)
                  ·
                    rfl

theorem cell23_4121794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4121794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121794 prefixEnd_4121794 := by exact prefixLift 4121794
  have htrace : WordTrace (prefixWord ++ tailWord_4121794) baseStart_4121794 baseEnd_4121794 := by
    simpa [prefixWord, tailWord_4121794, baseEnd_4121794] using wordTrace_append hprefix tailTrace_4121794
  have hstable : (prefixWord ++ tailWord_4121794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121794).length < 2 ^ (prefixWord ++ tailWord_4121794).sum := by decide
  have hdescent : baseEnd_4121794 < baseStart_4121794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121805 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_4121805 : Nat := 118140960795 + 4121805 * 2 ^ 59
def prefixEnd_4121805 : Nat := 4983230072969 + 3 ^ 40 * 4121805 * 2
def baseEnd_4121805 : Nat := 2116467129105351152681671

theorem tailTrace_4121805 : CollatzResearch.WordTrace tailWord_4121805 prefixEnd_4121805 2116467129105351152681671 := by
  unfold tailWord_4121805
  simp only [CollatzResearch.WordTrace]
  refine ⟨150334578832411908094926869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100223052554941272063284579 150334578832411908094926869)
  ·
    refine ⟨7046933382769308191949697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150334578832411908094926869 7046933382769308191949697)
    ·
      refine ⟨5285200037076981143962273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7046933382769308191949697 5285200037076981143962273)
      ·
        refine ⟨3963900027807735857971705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5285200037076981143962273 3963900027807735857971705)
        ·
          refine ⟨2972925020855801893478779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3963900027807735857971705 2972925020855801893478779)
          ·
            refine ⟨4459387531283702840218169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972925020855801893478779 4459387531283702840218169)
            ·
              refine ⟨3344540648462777130163627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4459387531283702840218169 3344540648462777130163627)
              ·
                refine ⟨5016810972694165695245441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344540648462777130163627 5016810972694165695245441)
                ·
                  refine ⟨3762608229520624271434081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5016810972694165695245441 3762608229520624271434081)
                  ·
                    refine ⟨2821956172140468203575561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3762608229520624271434081 2821956172140468203575561)
                    ·
                      refine ⟨2116467129105351152681671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821956172140468203575561 2116467129105351152681671)
                      ·
                        rfl

theorem cell23_4121805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_4121805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121805 prefixEnd_4121805 := by exact prefixLift 4121805
  have htrace : WordTrace (prefixWord ++ tailWord_4121805) baseStart_4121805 baseEnd_4121805 := by
    simpa [prefixWord, tailWord_4121805, baseEnd_4121805] using wordTrace_append hprefix tailTrace_4121805
  have hstable : (prefixWord ++ tailWord_4121805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121805).length < 2 ^ (prefixWord ++ tailWord_4121805).sum := by decide
  have hdescent : baseEnd_4121805 < baseStart_4121805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121853 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 5, 5, 2]
def baseStart_4121853 : Nat := 118140960795 + 4121853 * 2 ^ 59
def prefixEnd_4121853 : Nat := 4983230072969 + 3 ^ 40 * 4121853 * 2
def baseEnd_4121853 : Nat := 2116491776176766964881449

theorem tailTrace_4121853 : CollatzResearch.WordTrace tailWord_4121853 prefixEnd_4121853 2116491776176766964881449 := by
  unfold tailWord_4121853
  simp only [CollatzResearch.WordTrace]
  refine ⟨150336329536238012292674213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100224219690825341528449475 150336329536238012292674213)
  ·
    refine ⟨28188061788044627304876415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150336329536238012292674213 28188061788044627304876415)
    ·
      refine ⟨42282092682066940957314623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28188061788044627304876415 42282092682066940957314623)
      ·
        refine ⟨63423139023100411435971935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42282092682066940957314623 63423139023100411435971935)
        ·
          refine ⟨95134708534650617153957903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63423139023100411435971935 95134708534650617153957903)
          ·
            refine ⟨142702062801975925730936855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95134708534650617153957903 142702062801975925730936855)
            ·
              refine ⟨214053094202963888596405283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142702062801975925730936855 214053094202963888596405283)
              ·
                refine ⟨321079641304445832894607925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214053094202963888596405283 321079641304445832894607925)
                ·
                  refine ⟨30101216372291796833869493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321079641304445832894607925 30101216372291796833869493)
                  ·
                    refine ⟨2821989034902355953175265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30101216372291796833869493 2821989034902355953175265)
                    ·
                      refine ⟨2116491776176766964881449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821989034902355953175265 2116491776176766964881449)
                      ·
                        rfl

theorem cell23_4121853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_4121853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121853 prefixEnd_4121853 := by exact prefixLift 4121853
  have htrace : WordTrace (prefixWord ++ tailWord_4121853) baseStart_4121853 baseEnd_4121853 := by
    simpa [prefixWord, tailWord_4121853, baseEnd_4121853] using wordTrace_append hprefix tailTrace_4121853
  have hstable : (prefixWord ++ tailWord_4121853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121853).length < 2 ^ (prefixWord ++ tailWord_4121853).sum := by decide
  have hdescent : baseEnd_4121853 < baseStart_4121853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121854 : List Nat := [4, 2, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_4121854 : Nat := 118140960795 + 4121854 * 2 ^ 59
def prefixEnd_4121854 : Nat := 4983230072969 + 3 ^ 40 * 4121854 * 2
def baseEnd_4121854 : Nat := 705497429885807153656315

theorem tailTrace_4121854 : CollatzResearch.WordTrace tailWord_4121854 prefixEnd_4121854 705497429885807153656315 := by
  unfold tailWord_4121854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18792045751154298682932577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100224244006156259642307077 18792045751154298682932577)
  ·
    refine ⟨14094034313365724012199433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18792045751154298682932577 14094034313365724012199433)
    ·
      refine ⟨10570525735024293009149575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14094034313365724012199433 10570525735024293009149575)
      ·
        refine ⟨15855788602536439513724363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10570525735024293009149575 15855788602536439513724363)
        ·
          refine ⟨23783682903804659270586545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15855788602536439513724363 23783682903804659270586545)
          ·
            refine ⟨17837762177853494452939909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23783682903804659270586545 17837762177853494452939909)
            ·
              refine ⟨3344580408347530209926233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17837762177853494452939909 3344580408347530209926233)
              ·
                refine ⟨2508435306260647657444675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344580408347530209926233 2508435306260647657444675)
                ·
                  refine ⟨3762652959390971486167013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2508435306260647657444675 3762652959390971486167013)
                  ·
                    refine ⟨705497429885807153656315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3762652959390971486167013 705497429885807153656315)
                    ·
                      rfl

theorem cell23_4121854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_4121854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121854 prefixEnd_4121854 := by exact prefixLift 4121854
  have htrace : WordTrace (prefixWord ++ tailWord_4121854) baseStart_4121854 baseEnd_4121854 := by
    simpa [prefixWord, tailWord_4121854, baseEnd_4121854] using wordTrace_append hprefix tailTrace_4121854
  have hstable : (prefixWord ++ tailWord_4121854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121854).length < 2 ^ (prefixWord ++ tailWord_4121854).sum := by decide
  have hdescent : baseEnd_4121854 < baseStart_4121854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121883 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 4]
def baseStart_4121883 : Nat := 118140960795 + 4121883 * 2 ^ 59
def prefixEnd_4121883 : Nat := 4983230072969 + 3 ^ 40 * 4121883 * 2
def baseEnd_4121883 : Nat := 2116507180596401847506311

theorem tailTrace_4121883 : CollatzResearch.WordTrace tailWord_4121883 prefixEnd_4121883 2116507180596401847506311 := by
  unfold tailWord_4121883
  simp only [CollatzResearch.WordTrace]
  refine ⟨150337423726129327416266303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100224949150752884944177535 150337423726129327416266303)
  ·
    refine ⟨225506135589193991124399455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150337423726129327416266303 225506135589193991124399455)
    ·
      refine ⟨338259203383790986686599183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225506135589193991124399455 338259203383790986686599183)
      ·
        refine ⟨507388805075686480029898775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338259203383790986686599183 507388805075686480029898775)
        ·
          refine ⟨761083207613529720044848163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507388805075686480029898775 761083207613529720044848163)
          ·
            refine ⟨1141624811420294580067272245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761083207613529720044848163 1141624811420294580067272245)
            ·
              refine ⟨107027326070652616881306773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1141624811420294580067272245 107027326070652616881306773)
              ·
                refine ⟨5016905909561841416311255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107027326070652616881306773 5016905909561841416311255)
                ·
                  refine ⟨7525358864342762124466883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016905909561841416311255 7525358864342762124466883)
                  ·
                    refine ⟨11288038296514143186700325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7525358864342762124466883 11288038296514143186700325)
                    ·
                      refine ⟨2116507180596401847506311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11288038296514143186700325 2116507180596401847506311)
                      ·
                        rfl

theorem cell23_4121883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 4].length) (baseStart_4121883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121883 prefixEnd_4121883 := by exact prefixLift 4121883
  have htrace : WordTrace (prefixWord ++ tailWord_4121883) baseStart_4121883 baseEnd_4121883 := by
    simpa [prefixWord, tailWord_4121883, baseEnd_4121883] using wordTrace_append hprefix tailTrace_4121883
  have hstable : (prefixWord ++ tailWord_4121883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121883).length < 2 ^ (prefixWord ++ tailWord_4121883).sum := by decide
  have hdescent : baseEnd_4121883 < baseStart_4121883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121893 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_4121893 : Nat := 118140960795 + 4121893 * 2 ^ 59
def prefixEnd_4121893 : Nat := 4983230072969 + 3 ^ 40 * 4121893 * 2
def baseEnd_4121893 : Nat := 705504105134315602793755

theorem tailTrace_4121893 : CollatzResearch.WordTrace tailWord_4121893 prefixEnd_4121893 705504105134315602793755 := by
  unfold tailWord_4121893
  simp only [CollatzResearch.WordTrace]
  refine ⟨150337788456093099124130333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100225192304062066082753555 150337788456093099124130333)
  ·
    refine ⟨56376670671034912171548875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150337788456093099124130333 56376670671034912171548875)
    ·
      refine ⟨84565006006552368257323313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56376670671034912171548875 84565006006552368257323313)
      ·
        refine ⟨63423754504914276192992485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84565006006552368257323313 63423754504914276192992485)
        ·
          refine ⟨11891953969671426786186091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63423754504914276192992485 11891953969671426786186091)
          ·
            refine ⟨17837930954507140179279137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11891953969671426786186091 17837930954507140179279137)
            ·
              refine ⟨13378448215880355134459353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17837930954507140179279137 13378448215880355134459353)
              ·
                refine ⟨10033836161910266350844515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13378448215880355134459353 10033836161910266350844515)
                ·
                  refine ⟨15050754242865399526266773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10033836161910266350844515 15050754242865399526266773)
                  ·
                    refine ⟨705504105134315602793755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15050754242865399526266773 705504105134315602793755)
                    ·
                      rfl

theorem cell23_4121893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_4121893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121893 prefixEnd_4121893 := by exact prefixLift 4121893
  have htrace : WordTrace (prefixWord ++ tailWord_4121893) baseStart_4121893 baseEnd_4121893 := by
    simpa [prefixWord, tailWord_4121893, baseEnd_4121893] using wordTrace_append hprefix tailTrace_4121893
  have hstable : (prefixWord ++ tailWord_4121893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121893).length < 2 ^ (prefixWord ++ tailWord_4121893).sum := by decide
  have hdescent : baseEnd_4121893 < baseStart_4121893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121900 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 7, 2, 2]
def baseStart_4121900 : Nat := 118140960795 + 4121900 * 2 ^ 59
def prefixEnd_4121900 : Nat := 4983230072969 + 3 ^ 40 * 4121900 * 2
def baseEnd_4121900 : Nat := 2116515909767528280993733

theorem tailTrace_4121900 : CollatzResearch.WordTrace tailWord_4121900 prefixEnd_4121900 2116515909767528280993733 := by
  unfold tailWord_4121900
  simp only [CollatzResearch.WordTrace]
  refine ⟨75169021883533869659817577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100225362511378492879756769 75169021883533869659817577)
  ·
    refine ⟨56376766412650402244863183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75169021883533869659817577 56376766412650402244863183)
    ·
      refine ⟨84565149618975603367294775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56376766412650402244863183 84565149618975603367294775)
      ·
        refine ⟨126847724428463405050942163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84565149618975603367294775 126847724428463405050942163)
        ·
          refine ⟨190271586642695107576413245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126847724428463405050942163 190271586642695107576413245)
          ·
            refine ⟨71351844991010665341154967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190271586642695107576413245 71351844991010665341154967)
            ·
              refine ⟨107027767486515998011732451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71351844991010665341154967 107027767486515998011732451)
              ·
                refine ⟨160541651229773997017598677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107027767486515998011732451 160541651229773997017598677)
                ·
                  refine ⟨3762694950697828055099969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 160541651229773997017598677 3762694950697828055099969)
                  ·
                    refine ⟨2822021213023371041324977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3762694950697828055099969 2822021213023371041324977)
                    ·
                      refine ⟨2116515909767528280993733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822021213023371041324977 2116515909767528280993733)
                      ·
                        rfl

theorem cell23_4121900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_4121900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121900 prefixEnd_4121900 := by exact prefixLift 4121900
  have htrace : WordTrace (prefixWord ++ tailWord_4121900) baseStart_4121900 baseEnd_4121900 := by
    simpa [prefixWord, tailWord_4121900, baseEnd_4121900] using wordTrace_append hprefix tailTrace_4121900
  have hstable : (prefixWord ++ tailWord_4121900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121900).length < 2 ^ (prefixWord ++ tailWord_4121900).sum := by decide
  have hdescent : baseEnd_4121900 < baseStart_4121900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121927 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 2, 4]
def baseStart_4121927 : Nat := 118140960795 + 4121927 * 2 ^ 59
def prefixEnd_4121927 : Nat := 4983230072969 + 3 ^ 40 * 4121927 * 2
def baseEnd_4121927 : Nat := 705509924581733225118703

theorem tailTrace_4121927 : CollatzResearch.WordTrace tailWord_4121927 prefixEnd_4121927 705509924581733225118703 := by
  unfold tailWord_4121927
  simp only [CollatzResearch.WordTrace]
  refine ⟨150339028537969922930868035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100226019025313281953912023 150339028537969922930868035)
  ·
    refine ⟨225508542806954884396302053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150339028537969922930868035 225508542806954884396302053)
    ·
      refine ⟨42282851776304040824306635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225508542806954884396302053 42282851776304040824306635)
      ·
        refine ⟨63424277664456061236459953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42282851776304040824306635 63424277664456061236459953)
        ·
          refine ⟨47568208248342045927344965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63424277664456061236459953 47568208248342045927344965)
          ·
            refine ⟨8919039046564133611377181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47568208248342045927344965 8919039046564133611377181)
            ·
              refine ⟨3344639642461550104266443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8919039046564133611377181 3344639642461550104266443)
              ·
                refine ⟨5016959463692325156399665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344639642461550104266443 5016959463692325156399665)
                ·
                  refine ⟨3762719597769243867299749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5016959463692325156399665 3762719597769243867299749)
                  ·
                    refine ⟨705509924581733225118703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3762719597769243867299749 705509924581733225118703)
                    ·
                      rfl

theorem cell23_4121927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_4121927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4121927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4121927 prefixEnd_4121927 := by exact prefixLift 4121927
  have htrace : WordTrace (prefixWord ++ tailWord_4121927) baseStart_4121927 baseEnd_4121927 := by
    simpa [prefixWord, tailWord_4121927, baseEnd_4121927] using wordTrace_append hprefix tailTrace_4121927
  have hstable : (prefixWord ++ tailWord_4121927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121927).length < 2 ^ (prefixWord ++ tailWord_4121927).sum := by decide
  have hdescent : baseEnd_4121927 < baseStart_4121927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122060 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_4122060 : Nat := 118140960795 + 4122060 * 2 ^ 59
def prefixEnd_4122060 : Nat := 4983230072969 + 3 ^ 40 * 4122060 * 2
def baseEnd_4122060 : Nat := 705532688890749218330999

theorem tailTrace_4122060 : CollatzResearch.WordTrace tailWord_4122060 prefixEnd_4122060 705532688890749218330999 := by
  unfold tailWord_4122060
  simp only [CollatzResearch.WordTrace]
  refine ⟨75171939723244043322729817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100229252964325391096973089 75171939723244043322729817)
  ·
    refine ⟨56378954792433032492047363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75171939723244043322729817 56378954792433032492047363)
    ·
      refine ⟨84568432188649548738071045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56378954792433032492047363 84568432188649548738071045)
      ·
        refine ⟨15856581035371790388388321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84568432188649548738071045 15856581035371790388388321)
        ·
          refine ⟨11892435776528842791291241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15856581035371790388388321 11892435776528842791291241)
          ·
            refine ⟨8919326832396632093468431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11892435776528842791291241 8919326832396632093468431)
            ·
              refine ⟨13378990248594948140202647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8919326832396632093468431 13378990248594948140202647)
              ·
                refine ⟨20068485372892422210303971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13378990248594948140202647 20068485372892422210303971)
                ·
                  refine ⟨30102728059338633315455957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20068485372892422210303971 30102728059338633315455957)
                  ·
                    refine ⟨705532688890749218330999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30102728059338633315455957 705532688890749218330999)
                    ·
                      rfl

theorem cell23_4122060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_4122060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122060 prefixEnd_4122060 := by exact prefixLift 4122060
  have htrace : WordTrace (prefixWord ++ tailWord_4122060) baseStart_4122060 baseEnd_4122060 := by
    simpa [prefixWord, tailWord_4122060, baseEnd_4122060] using wordTrace_append hprefix tailTrace_4122060
  have hstable : (prefixWord ++ tailWord_4122060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122060).length < 2 ^ (prefixWord ++ tailWord_4122060).sum := by decide
  have hdescent : baseEnd_4122060 < baseStart_4122060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122097 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 2, 4, 2]
def baseStart_4122097 : Nat := 118140960795 + 4122097 * 2 ^ 59
def prefixEnd_4122097 : Nat := 4983230072969 + 3 ^ 40 * 4122097 * 2
def baseEnd_4122097 : Nat := 2116617065456464010230327

theorem tailTrace_4122097 : CollatzResearch.WordTrace tailWord_4122097 prefixEnd_4122097 2116617065456464010230327 := by
  unfold tailWord_4122097
  simp only [CollatzResearch.WordTrace]
  refine ⟨150345228947354041964556545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100230152631569361309704363 150345228947354041964556545)
  ·
    refine ⟨112758921710515531473417409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150345228947354041964556545 112758921710515531473417409)
    ·
      refine ⟨84569191282886648605063057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112758921710515531473417409 84569191282886648605063057)
      ·
        refine ⟨63426893462164986453797293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84569191282886648605063057 63426893462164986453797293)
        ·
          refine ⟨23785085048311869920173985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63426893462164986453797293 23785085048311869920173985)
          ·
            refine ⟨17838813786233902440130489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23785085048311869920173985 17838813786233902440130489)
            ·
              refine ⟨13379110339675426830097867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17838813786233902440130489 13379110339675426830097867)
              ·
                refine ⟨20068665509513140245146801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13379110339675426830097867 20068665509513140245146801)
                ·
                  refine ⟨15051499132134855183860101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20068665509513140245146801 15051499132134855183860101)
                  ·
                    refine ⟨2822156087275285346973769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15051499132134855183860101 2822156087275285346973769)
                    ·
                      refine ⟨2116617065456464010230327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822156087275285346973769 2116617065456464010230327)
                      ·
                        rfl

theorem cell23_4122097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_4122097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122097 prefixEnd_4122097 := by exact prefixLift 4122097
  have htrace : WordTrace (prefixWord ++ tailWord_4122097) baseStart_4122097 baseEnd_4122097 := by
    simpa [prefixWord, tailWord_4122097, baseEnd_4122097] using wordTrace_append hprefix tailTrace_4122097
  have hstable : (prefixWord ++ tailWord_4122097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122097).length < 2 ^ (prefixWord ++ tailWord_4122097).sum := by decide
  have hdescent : baseEnd_4122097 < baseStart_4122097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122141 : List Nat := [1, 4, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_4122141 : Nat := 118140960795 + 4122141 * 2 ^ 59
def prefixEnd_4122141 : Nat := 4983230072969 + 3 ^ 40 * 4122141 * 2
def baseEnd_4122141 : Nat := 705546552868420612693375

theorem tailTrace_4122141 : CollatzResearch.WordTrace tailWord_4122141 prefixEnd_4122141 705546552868420612693375 := by
  unfold tailWord_4122141
  simp only [CollatzResearch.WordTrace]
  refine ⟨150346833759194637479158277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100231222506129758319438851 150346833759194637479158277)
  ·
    refine ⟨28190031329848994527342177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150346833759194637479158277 28190031329848994527342177)
    ·
      refine ⟨21142523497386745895506633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28190031329848994527342177 21142523497386745895506633)
      ·
        refine ⟨15856892623040059421629975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21142523497386745895506633 15856892623040059421629975)
        ·
          refine ⟨23785338934560089132444963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15856892623040059421629975 23785338934560089132444963)
          ·
            refine ⟨35678008401840133698667445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23785338934560089132444963 35678008401840133698667445)
            ·
              refine ⟨3344813287672512534250073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35678008401840133698667445 3344813287672512534250073)
              ·
                refine ⟨2508609965754384400687555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344813287672512534250073 2508609965754384400687555)
                ·
                  refine ⟨3762914948631576601031333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2508609965754384400687555 3762914948631576601031333)
                  ·
                    refine ⟨705546552868420612693375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3762914948631576601031333 705546552868420612693375)
                    ·
                      rfl

theorem cell23_4122141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_4122141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122141 prefixEnd_4122141 := by exact prefixLift 4122141
  have htrace : WordTrace (prefixWord ++ tailWord_4122141) baseStart_4122141 baseEnd_4122141 := by
    simpa [prefixWord, tailWord_4122141, baseEnd_4122141] using wordTrace_append hprefix tailTrace_4122141
  have hstable : (prefixWord ++ tailWord_4122141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122141).length < 2 ^ (prefixWord ++ tailWord_4122141).sum := by decide
  have hdescent : baseEnd_4122141 < baseStart_4122141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122153 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_4122153 : Nat := 118140960795 + 4122153 * 2 ^ 59
def prefixEnd_4122153 : Nat := 4983230072969 + 3 ^ 40 * 4122153 * 2
def baseEnd_4122153 : Nat := 2116645820373115791130069

theorem tailTrace_4122153 : CollatzResearch.WordTrace tailWord_4122153 prefixEnd_4122153 2116645820373115791130069 := by
  unfold tailWord_4122153
  simp only [CollatzResearch.WordTrace]
  refine ⟨150347271435151163528595113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100231514290100775685730075 150347271435151163528595113)
  ·
    refine ⟨112760453576363372646446335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150347271435151163528595113 112760453576363372646446335)
    ·
      refine ⟨169140680364545058969669503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112760453576363372646446335 169140680364545058969669503)
      ·
        refine ⟨253711020546817588454504255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169140680364545058969669503 253711020546817588454504255)
        ·
          refine ⟨380566530820226382681756383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253711020546817588454504255 380566530820226382681756383)
          ·
            refine ⟨570849796230339574022634575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380566530820226382681756383 570849796230339574022634575)
            ·
              refine ⟨856274694345509361033951863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570849796230339574022634575 856274694345509361033951863)
              ·
                refine ⟨1284412041518264041550927795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856274694345509361033951863 1284412041518264041550927795)
                ·
                  refine ⟨1926618062277396062326391693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284412041518264041550927795 1926618062277396062326391693)
                  ·
                    refine ⟨722481773354023523372396885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1926618062277396062326391693 722481773354023523372396885)
                    ·
                      refine ⟨2116645820373115791130069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 722481773354023523372396885 2116645820373115791130069)
                      ·
                        rfl

theorem cell23_4122153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_4122153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122153 prefixEnd_4122153 := by exact prefixLift 4122153
  have htrace : WordTrace (prefixWord ++ tailWord_4122153) baseStart_4122153 baseEnd_4122153 := by
    simpa [prefixWord, tailWord_4122153, baseEnd_4122153] using wordTrace_append hprefix tailTrace_4122153
  have hstable : (prefixWord ++ tailWord_4122153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122153).length < 2 ^ (prefixWord ++ tailWord_4122153).sum := by decide
  have hdescent : baseEnd_4122153 < baseStart_4122153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122167 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 1, 5]
def baseStart_4122167 : Nat := 118140960795 + 4122167 * 2 ^ 59
def prefixEnd_4122167 : Nat := 4983230072969 + 3 ^ 40 * 4122167 * 2
def baseEnd_4122167 : Nat := 705551003034092912118335

theorem tailTrace_4122167 : CollatzResearch.WordTrace tailWord_4122167 prefixEnd_4122167 705551003034092912118335 := by
  unfold tailWord_4122167
  simp only [CollatzResearch.WordTrace]
  refine ⟨150347782057100443919604755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100231854704733629279736503 150347782057100443919604755)
  ·
    refine ⟨225521673085650665879407133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150347782057100443919604755 225521673085650665879407133)
    ·
      refine ⟨84570627407118999704777675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225521673085650665879407133 84570627407118999704777675)
      ·
        refine ⟨126855941110678499557166513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84570627407118999704777675 126855941110678499557166513)
        ·
          refine ⟨95141955833008874667874885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126855941110678499557166513 95141955833008874667874885)
          ·
            refine ⟨17839116718689164000226541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95141955833008874667874885 17839116718689164000226541)
            ·
              refine ⟨6689668769508436500084953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17839116718689164000226541 6689668769508436500084953)
              ·
                refine ⟨5017251577131327375063715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6689668769508436500084953 5017251577131327375063715)
                ·
                  refine ⟨7525877365696991062595573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5017251577131327375063715 7525877365696991062595573)
                  ·
                    refine ⟨705551003034092912118335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7525877365696991062595573 705551003034092912118335)
                    ·
                      rfl

theorem cell23_4122167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_4122167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122167 prefixEnd_4122167 := by exact prefixLift 4122167
  have htrace : WordTrace (prefixWord ++ tailWord_4122167) baseStart_4122167 baseEnd_4122167 := by
    simpa [prefixWord, tailWord_4122167, baseEnd_4122167] using wordTrace_append hprefix tailTrace_4122167
  have hstable : (prefixWord ++ tailWord_4122167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122167).length < 2 ^ (prefixWord ++ tailWord_4122167).sum := by decide
  have hdescent : baseEnd_4122167 < baseStart_4122167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122200 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_4122200 : Nat := 118140960795 + 4122200 * 2 ^ 59
def prefixEnd_4122200 : Nat := 4983230072969 + 3 ^ 40 * 4122200 * 2
def baseEnd_4122200 : Nat := 2116669953963877107242353

theorem tailTrace_4122200 : CollatzResearch.WordTrace tailWord_4122200 prefixEnd_4122200 2116669953963877107242353 := by
  unfold tailWord_4122200
  simp only [CollatzResearch.WordTrace]
  refine ⟨75174492832990445277778027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100232657110653927037037369 75174492832990445277778027)
  ·
    refine ⟨112761739249485667916667041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75174492832990445277778027 112761739249485667916667041)
    ·
      refine ⟨84571304437114250937500281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112761739249485667916667041 84571304437114250937500281)
      ·
        refine ⟨63428478327835688203125211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84571304437114250937500281 63428478327835688203125211)
        ·
          refine ⟨95142717491753532304687817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63428478327835688203125211 95142717491753532304687817)
          ·
            refine ⟨71357038118815149228515863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95142717491753532304687817 71357038118815149228515863)
            ·
              refine ⟨107035557178222723842773795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71357038118815149228515863 107035557178222723842773795)
              ·
                refine ⟨160553335767334085764160693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107035557178222723842773795 160553335767334085764160693)
                ·
                  refine ⟨15051875228187570540390065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160553335767334085764160693 15051875228187570540390065)
                  ·
                    refine ⟨11288906421140677905292549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15051875228187570540390065 11288906421140677905292549)
                    ·
                      refine ⟨2116669953963877107242353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11288906421140677905292549 2116669953963877107242353)
                      ·
                        rfl

theorem cell23_4122200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_4122200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122200 prefixEnd_4122200 := by exact prefixLift 4122200
  have htrace : WordTrace (prefixWord ++ tailWord_4122200) baseStart_4122200 baseEnd_4122200 := by
    simpa [prefixWord, tailWord_4122200, baseEnd_4122200] using wordTrace_append hprefix tailTrace_4122200
  have hstable : (prefixWord ++ tailWord_4122200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122200).length < 2 ^ (prefixWord ++ tailWord_4122200).sum := by decide
  have hdescent : baseEnd_4122200 < baseStart_4122200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122241 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_4122241 : Nat := 118140960795 + 4122241 * 2 ^ 59
def prefixEnd_4122241 : Nat := 4983230072969 + 3 ^ 40 * 4122241 * 2
def baseEnd_4122241 : Nat := 2116691006670711446829665

theorem tailTrace_4122241 : CollatzResearch.WordTrace tailWord_4122241 prefixEnd_4122241 2116691006670711446829665 := by
  unfold tailWord_4122241
  simp only [CollatzResearch.WordTrace]
  refine ⟨150350481058832354557798577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100233654039221569705199051 150350481058832354557798577)
  ·
    refine ⟨112762860794124265918348933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150350481058832354557798577 112762860794124265918348933)
    ·
      refine ⟨21143036398898299859690425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112762860794124265918348933 21143036398898299859690425)
      ·
        refine ⟨15857277299173724894767819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21143036398898299859690425 15857277299173724894767819)
        ·
          refine ⟨23785915948760587342151729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15857277299173724894767819 23785915948760587342151729)
          ·
            refine ⟨17839436961570440506613797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23785915948760587342151729 17839436961570440506613797)
            ·
              refine ⟨3344894430294457594990087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17839436961570440506613797 3344894430294457594990087)
              ·
                refine ⟨5017341645441686392485131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344894430294457594990087 5017341645441686392485131)
                ·
                  refine ⟨7526012468162529588727697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5017341645441686392485131 7526012468162529588727697)
                  ·
                    refine ⟨5644509351121897191545773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7526012468162529588727697 5644509351121897191545773)
                    ·
                      refine ⟨2116691006670711446829665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5644509351121897191545773 2116691006670711446829665)
                      ·
                        rfl

theorem cell23_4122241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_4122241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122241 prefixEnd_4122241 := by exact prefixLift 4122241
  have htrace : WordTrace (prefixWord ++ tailWord_4122241) baseStart_4122241 baseEnd_4122241 := by
    simpa [prefixWord, tailWord_4122241, baseEnd_4122241] using wordTrace_append hprefix tailTrace_4122241
  have hstable : (prefixWord ++ tailWord_4122241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122241).length < 2 ^ (prefixWord ++ tailWord_4122241).sum := by decide
  have hdescent : baseEnd_4122241 < baseStart_4122241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122248 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 2, 4]
def baseStart_4122248 : Nat := 118140960795 + 4122248 * 2 ^ 59
def prefixEnd_4122248 : Nat := 4983230072969 + 3 ^ 40 * 4122248 * 2
def baseEnd_4122248 : Nat := 705564867011764306480711

theorem tailTrace_4122248 : CollatzResearch.WordTrace tailWord_4122248 prefixEnd_4122248 705564867011764306480711 := by
  unfold tailWord_4122248
  simp only [CollatzResearch.WordTrace]
  refine ⟨75175368184903497376651699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100233824246537996502202265 75175368184903497376651699)
  ·
    refine ⟨112763052277355246064977549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75175368184903497376651699 112763052277355246064977549)
    ·
      refine ⟨42286144604008217274366581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112763052277355246064977549 42286144604008217274366581)
      ·
        refine ⟨3964326056625770369471867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42286144604008217274366581 3964326056625770369471867)
        ·
          refine ⟨5946489084938655554207801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964326056625770369471867 5946489084938655554207801)
          ·
            refine ⟨4459866813703991665655851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5946489084938655554207801 4459866813703991665655851)
            ·
              refine ⟨6689800220555987498483777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459866813703991665655851 6689800220555987498483777)
              ·
                refine ⟨5017350165416990623862833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6689800220555987498483777 5017350165416990623862833)
                ·
                  refine ⟨3763012624062742967897125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5017350165416990623862833 3763012624062742967897125)
                  ·
                    refine ⟨705564867011764306480711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763012624062742967897125 705564867011764306480711)
                    ·
                      rfl

theorem cell23_4122248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_4122248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122248 prefixEnd_4122248 := by exact prefixLift 4122248
  have htrace : WordTrace (prefixWord ++ tailWord_4122248) baseStart_4122248 baseEnd_4122248 := by
    simpa [prefixWord, tailWord_4122248, baseEnd_4122248] using wordTrace_append hprefix tailTrace_4122248
  have hstable : (prefixWord ++ tailWord_4122248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122248).length < 2 ^ (prefixWord ++ tailWord_4122248).sum := by decide
  have hdescent : baseEnd_4122248 < baseStart_4122248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122306 : List Nat := [3, 5, 1, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_4122306 : Nat := 118140960795 + 4122306 * 2 ^ 59
def prefixEnd_4122306 : Nat := 4983230072969 + 3 ^ 40 * 4122306 * 2
def baseEnd_4122306 : Nat := 2116724382913253692516867

theorem tailTrace_4122306 : CollatzResearch.WordTrace tailWord_4122306 prefixEnd_4122306 2116724382913253692516867 := by
  unfold tailWord_4122306
  simp only [CollatzResearch.WordTrace]
  refine ⟨37588212950899217664728693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100235234535731247105943181 37588212950899217664728693)
  ·
    refine ⟨3523894964146801656068315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37588212950899217664728693 3523894964146801656068315)
    ·
      refine ⟨5285842446220202484102473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3523894964146801656068315 5285842446220202484102473)
      ·
        refine ⟨3964381834665151863076855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5285842446220202484102473 3964381834665151863076855)
        ·
          refine ⟨5946572751997727794615283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964381834665151863076855 5946572751997727794615283)
          ·
            refine ⟨8919859127996591691922925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5946572751997727794615283 8919859127996591691922925)
            ·
              refine ⟨3344947172998721884471097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8919859127996591691922925 3344947172998721884471097)
              ·
                refine ⟨2508710379749041413353323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344947172998721884471097 2508710379749041413353323)
                ·
                  refine ⟨3763065569623562120029985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2508710379749041413353323 3763065569623562120029985)
                  ·
                    refine ⟨2822299177217671590022489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3763065569623562120029985 2822299177217671590022489)
                    ·
                      refine ⟨2116724382913253692516867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822299177217671590022489 2116724382913253692516867)
                      ·
                        rfl

theorem cell23_4122306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_4122306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122306 prefixEnd_4122306 := by exact prefixLift 4122306
  have htrace : WordTrace (prefixWord ++ tailWord_4122306) baseStart_4122306 baseEnd_4122306 := by
    simpa [prefixWord, tailWord_4122306, baseEnd_4122306] using wordTrace_append hprefix tailTrace_4122306
  have hstable : (prefixWord ++ tailWord_4122306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122306).length < 2 ^ (prefixWord ++ tailWord_4122306).sum := by decide
  have hdescent : baseEnd_4122306 < baseStart_4122306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122311 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 2, 2, 2]
def baseStart_4122311 : Nat := 118140960795 + 4122311 * 2 ^ 59
def prefixEnd_4122311 : Nat := 4983230072969 + 3 ^ 40 * 4122311 * 2
def baseEnd_4122311 : Nat := 2116726950316526172954343

theorem tailTrace_4122311 : CollatzResearch.WordTrace tailWord_4122311 prefixEnd_4122311 2116726950316526172954343 := by
  unfold tailWord_4122311
  simp only [CollatzResearch.WordTrace]
  refine ⟨150353034168578756512846787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100235356112385837675231191 150353034168578756512846787)
  ·
    refine ⟨225529551252868134769270181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150353034168578756512846787 225529551252868134769270181)
    ·
      refine ⟨42286790859912775269238159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225529551252868134769270181 42286790859912775269238159)
      ·
        refine ⟨63430186289869162903857239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42286790859912775269238159 63430186289869162903857239)
        ·
          refine ⟨95145279434803744355785859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63430186289869162903857239 95145279434803744355785859)
          ·
            refine ⟨142717919152205616533678789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95145279434803744355785859 142717919152205616533678789)
            ·
              refine ⟨26759609841038553100064773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142717919152205616533678789 26759609841038553100064773)
              ·
                refine ⟨5017426845194728706262145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26759609841038553100064773 5017426845194728706262145)
                ·
                  refine ⟨3763070133896046529696609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5017426845194728706262145 3763070133896046529696609)
                  ·
                    refine ⟨2822302600422034897272457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3763070133896046529696609 2822302600422034897272457)
                    ·
                      refine ⟨2116726950316526172954343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822302600422034897272457 2116726950316526172954343)
                      ·
                        rfl

theorem cell23_4122311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_4122311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122311 prefixEnd_4122311 := by exact prefixLift 4122311
  have htrace : WordTrace (prefixWord ++ tailWord_4122311) baseStart_4122311 baseEnd_4122311 := by
    simpa [prefixWord, tailWord_4122311, baseEnd_4122311] using wordTrace_append hprefix tailTrace_4122311
  have hstable : (prefixWord ++ tailWord_4122311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122311).length < 2 ^ (prefixWord ++ tailWord_4122311).sum := by decide
  have hdescent : baseEnd_4122311 < baseStart_4122311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122320 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_4122320 : Nat := 118140960795 + 4122320 * 2 ^ 59
def prefixEnd_4122320 : Nat := 4983230072969 + 3 ^ 40 * 4122320 * 2
def baseEnd_4122320 : Nat := 2116731571642416637741801

theorem tailTrace_4122320 : CollatzResearch.WordTrace tailWord_4122320 prefixEnd_4122320 2116731571642416637741801 := by
  unfold tailWord_4122320
  simp only [CollatzResearch.WordTrace]
  refine ⟨75176681212773075524962207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100235574950364100699949609 75176681212773075524962207)
  ·
    refine ⟨112765021819159613287443311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75176681212773075524962207 112765021819159613287443311)
    ·
      refine ⟨169147532728739419931164967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112765021819159613287443311 169147532728739419931164967)
      ·
        refine ⟨253721299093109129896747451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169147532728739419931164967 253721299093109129896747451)
        ·
          refine ⟨380581948639663694845121177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253721299093109129896747451 380581948639663694845121177)
          ·
            refine ⟨285436461479747771133840883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380581948639663694845121177 285436461479747771133840883)
            ·
              refine ⟨428154692219621656700761325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285436461479747771133840883 428154692219621656700761325)
              ·
                refine ⟨160558009582358121262785497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428154692219621656700761325 160558009582358121262785497)
                ·
                  refine ⟨120418507186768590947089123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160558009582358121262785497 120418507186768590947089123)
                  ·
                    refine ⟨180627760780152886420633685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120418507186768590947089123 180627760780152886420633685)
                    ·
                      refine ⟨2116731571642416637741801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 180627760780152886420633685 2116731571642416637741801)
                      ·
                        rfl

theorem cell23_4122320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_4122320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122320 prefixEnd_4122320 := by exact prefixLift 4122320
  have htrace : WordTrace (prefixWord ++ tailWord_4122320) baseStart_4122320 baseEnd_4122320 := by
    simpa [prefixWord, tailWord_4122320, baseEnd_4122320] using wordTrace_append hprefix tailTrace_4122320
  have hstable : (prefixWord ++ tailWord_4122320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122320).length < 2 ^ (prefixWord ++ tailWord_4122320).sum := by decide
  have hdescent : baseEnd_4122320 < baseStart_4122320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122327 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 3]
def baseStart_4122327 : Nat := 118140960795 + 4122327 * 2 ^ 59
def prefixEnd_4122327 : Nat := 4983230072969 + 3 ^ 40 * 4122327 * 2
def baseEnd_4122327 : Nat := 2116735166006998110354269

theorem tailTrace_4122327 : CollatzResearch.WordTrace tailWord_4122327 prefixEnd_4122327 2116735166006998110354269 := by
  unfold tailWord_4122327
  simp only [CollatzResearch.WordTrace]
  refine ⟨150353617736520791245429235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100235745157680527496952823 150353617736520791245429235)
  ·
    refine ⟨225530426604781186868143853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150353617736520791245429235 225530426604781186868143853)
    ·
      refine ⟨84573909976792945075553945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225530426604781186868143853 84573909976792945075553945)
      ·
        refine ⟨63430432482594708806665459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84573909976792945075553945 63430432482594708806665459)
        ·
          refine ⟨95145648723892063209998189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63430432482594708806665459 95145648723892063209998189)
          ·
            refine ⟨35679618271459523703749321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95145648723892063209998189 35679618271459523703749321)
            ·
              refine ⟨26759713703594642777811991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35679618271459523703749321 26759713703594642777811991)
              ·
                refine ⟨40139570555391964166717987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26759713703594642777811991 40139570555391964166717987)
                ·
                  refine ⟨60209355833087946250076981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40139570555391964166717987 60209355833087946250076981)
                  ·
                    refine ⟨5644627109351994960944717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60209355833087946250076981 5644627109351994960944717)
                    ·
                      refine ⟨2116735166006998110354269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5644627109351994960944717 2116735166006998110354269)
                      ·
                        rfl

theorem cell23_4122327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_4122327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122327 prefixEnd_4122327 := by exact prefixLift 4122327
  have htrace : WordTrace (prefixWord ++ tailWord_4122327) baseStart_4122327 baseEnd_4122327 := by
    simpa [prefixWord, tailWord_4122327, baseEnd_4122327] using wordTrace_append hprefix tailTrace_4122327
  have hstable : (prefixWord ++ tailWord_4122327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122327).length < 2 ^ (prefixWord ++ tailWord_4122327).sum := by decide
  have hdescent : baseEnd_4122327 < baseStart_4122327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122332 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_4122332 : Nat := 118140960795 + 4122332 * 2 ^ 59
def prefixEnd_4122332 : Nat := 4983230072969 + 3 ^ 40 * 4122332 * 2
def baseEnd_4122332 : Nat := 2116737733410270590791747

theorem tailTrace_4122332 : CollatzResearch.WordTrace tailWord_4122332 prefixEnd_4122332 2116737733410270590791747 := by
  unfold tailWord_4122332
  simp only [CollatzResearch.WordTrace]
  refine ⟨75176900050751338549680625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100235866734335118066240833 75176900050751338549680625)
  ·
    refine ⟨56382675038063503912260469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75176900050751338549680625 56382675038063503912260469)
    ·
      refine ⟨5285875784818453491774419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56382675038063503912260469 5285875784818453491774419)
      ·
        refine ⟨7928813677227680237661629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285875784818453491774419 7928813677227680237661629)
        ·
          refine ⟨2973305128960380089123111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7928813677227680237661629 2973305128960380089123111)
          ·
            refine ⟨4459957693440570133684667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973305128960380089123111 4459957693440570133684667)
            ·
              refine ⟨6689936540160855200527001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459957693440570133684667 6689936540160855200527001)
              ·
                refine ⟨5017452405120641400395251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6689936540160855200527001 5017452405120641400395251)
                ·
                  refine ⟨7526178607680962100592877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5017452405120641400395251 7526178607680962100592877)
                  ·
                    refine ⟨2822316977880360787722329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7526178607680962100592877 2822316977880360787722329)
                    ·
                      refine ⟨2116737733410270590791747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822316977880360787722329 2116737733410270590791747)
                      ·
                        rfl

theorem cell23_4122332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_4122332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122332 prefixEnd_4122332 := by exact prefixLift 4122332
  have htrace : WordTrace (prefixWord ++ tailWord_4122332) baseStart_4122332 baseEnd_4122332 := by
    simpa [prefixWord, tailWord_4122332, baseEnd_4122332] using wordTrace_append hprefix tailTrace_4122332
  have hstable : (prefixWord ++ tailWord_4122332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122332).length < 2 ^ (prefixWord ++ tailWord_4122332).sum := by decide
  have hdescent : baseEnd_4122332 < baseStart_4122332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122347 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 2, 5]
def baseStart_4122347 : Nat := 118140960795 + 4122347 * 2 ^ 59
def prefixEnd_4122347 : Nat := 4983230072969 + 3 ^ 40 * 4122347 * 2
def baseEnd_4122347 : Nat := 705581811873362677368059

theorem tailTrace_4122347 : CollatzResearch.WordTrace tailWord_4122347 prefixEnd_4122347 705581811873362677368059 := by
  unfold tailWord_4122347
  simp only [CollatzResearch.WordTrace]
  refine ⟨150354347196448334661157295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100236231464298889774104863 150354347196448334661157295)
  ·
    refine ⟨225531520794672501991735943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150354347196448334661157295 225531520794672501991735943)
    ·
      refine ⟨338297281192008752987603915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225531520794672501991735943 338297281192008752987603915)
      ·
        refine ⟨507445921788013129481405873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338297281192008752987603915 507445921788013129481405873)
        ·
          refine ⟨380584441341009847111054405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507445921788013129481405873 380584441341009847111054405)
          ·
            refine ⟨71359582751439346333322701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380584441341009847111054405 71359582751439346333322701)
            ·
              refine ⟨26759843531789754874996013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71359582751439346333322701 26759843531789754874996013)
              ·
                refine ⟨10034941324421158078123505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26759843531789754874996013 10034941324421158078123505)
                ·
                  refine ⟨7526205993315868558592629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10034941324421158078123505 7526205993315868558592629)
                  ·
                    refine ⟨705581811873362677368059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7526205993315868558592629 705581811873362677368059)
                    ·
                      rfl

theorem cell23_4122347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 5].length) (baseStart_4122347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122347 prefixEnd_4122347 := by exact prefixLift 4122347
  have htrace : WordTrace (prefixWord ++ tailWord_4122347) baseStart_4122347 baseEnd_4122347 := by
    simpa [prefixWord, tailWord_4122347, baseEnd_4122347] using wordTrace_append hprefix tailTrace_4122347
  have hstable : (prefixWord ++ tailWord_4122347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122347).length < 2 ^ (prefixWord ++ tailWord_4122347).sum := by decide
  have hdescent : baseEnd_4122347 < baseStart_4122347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122394 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_4122394 : Nat := 118140960795 + 4122394 * 2 ^ 59
def prefixEnd_4122394 : Nat := 4983230072969 + 3 ^ 40 * 4122394 * 2
def baseEnd_4122394 : Nat := 705589856403616449405487

theorem tailTrace_4122394 : CollatzResearch.WordTrace tailWord_4122394 prefixEnd_4122394 705589856403616449405487 := by
  unfold tailWord_4122394
  simp only [CollatzResearch.WordTrace]
  refine ⟨37589015356819515422029559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100237374284852041125412157 37589015356819515422029559)
  ·
    refine ⟨56383523035229273133044339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37589015356819515422029559 56383523035229273133044339)
    ·
      refine ⟨84575284552843909699566509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56383523035229273133044339 84575284552843909699566509)
      ·
        refine ⟨31715731707316466137337441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84575284552843909699566509 31715731707316466137337441)
        ·
          refine ⟨23786798780487349603003081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31715731707316466137337441 23786798780487349603003081)
          ·
            refine ⟨17840099085365512202252311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23786798780487349603003081 17840099085365512202252311)
            ·
              refine ⟨26760148628048268303378467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17840099085365512202252311 26760148628048268303378467)
              ·
                refine ⟨40140222942072402455067701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26760148628048268303378467 40140222942072402455067701)
                ·
                  refine ⟨3763145900819287730162597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40140222942072402455067701 3763145900819287730162597)
                  ·
                    refine ⟨705589856403616449405487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763145900819287730162597 705589856403616449405487)
                    ·
                      rfl

theorem cell23_4122394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_4122394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122394 prefixEnd_4122394 := by exact prefixLift 4122394
  have htrace : WordTrace (prefixWord ++ tailWord_4122394) baseStart_4122394 baseEnd_4122394 := by
    simpa [prefixWord, tailWord_4122394, baseEnd_4122394] using wordTrace_append hprefix tailTrace_4122394
  have hstable : (prefixWord ++ tailWord_4122394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122394).length < 2 ^ (prefixWord ++ tailWord_4122394).sum := by decide
  have hdescent : baseEnd_4122394 < baseStart_4122394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122398 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_4122398 : Nat := 118140960795 + 4122398 * 2 ^ 59
def prefixEnd_4122398 : Nat := 4983230072969 + 3 ^ 40 * 4122398 * 2
def baseEnd_4122398 : Nat := 705590541044489110855481

theorem tailTrace_4122398 : CollatzResearch.WordTrace tailWord_4122398 prefixEnd_4122398 705590541044489110855481 := by
  unfold tailWord_4122398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18794525914907946296407981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100237471546175713580842565 18794525914907946296407981)
  ·
    refine ⟨7047947218090479861152993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18794525914907946296407981 7047947218090479861152993)
    ·
      refine ⟨5285960413567859895864745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7047947218090479861152993 5285960413567859895864745)
      ·
        refine ⟨3964470310175894921898559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5285960413567859895864745 3964470310175894921898559)
        ·
          refine ⟨5946705465263842382847839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964470310175894921898559 5946705465263842382847839)
          ·
            refine ⟨8920058197895763574271759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5946705465263842382847839 8920058197895763574271759)
            ·
              refine ⟨13380087296843645361407639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8920058197895763574271759 13380087296843645361407639)
              ·
                refine ⟨20070130945265468042111459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13380087296843645361407639 20070130945265468042111459)
                ·
                  refine ⟨30105196417898202063167189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20070130945265468042111459 30105196417898202063167189)
                  ·
                    refine ⟨705590541044489110855481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30105196417898202063167189 705590541044489110855481)
                    ·
                      rfl

theorem cell23_4122398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_4122398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122398 prefixEnd_4122398 := by exact prefixLift 4122398
  have htrace : WordTrace (prefixWord ++ tailWord_4122398) baseStart_4122398 baseEnd_4122398 := by
    simpa [prefixWord, tailWord_4122398, baseEnd_4122398] using wordTrace_append hprefix tailTrace_4122398
  have hstable : (prefixWord ++ tailWord_4122398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122398).length < 2 ^ (prefixWord ++ tailWord_4122398).sum := by decide
  have hdescent : baseEnd_4122398 < baseStart_4122398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122401 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_4122401 : Nat := 118140960795 + 4122401 * 2 ^ 59
def prefixEnd_4122401 : Nat := 4983230072969 + 3 ^ 40 * 4122401 * 2
def baseEnd_4122401 : Nat := 2116773163575430820828929

theorem tailTrace_4122401 : CollatzResearch.WordTrace tailWord_4122401 prefixEnd_4122401 2116773163575430820828929 := by
  unfold tailWord_4122401
  simp only [CollatzResearch.WordTrace]
  refine ⟨150356316738252701883623057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100237544492168467922415371 150356316738252701883623057)
  ·
    refine ⟨112767237553689526412717293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150356316738252701883623057 112767237553689526412717293)
    ·
      refine ⟨42287714082633572404768985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112767237553689526412717293 42287714082633572404768985)
      ·
        refine ⟨31715785561975179303576739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42287714082633572404768985 31715785561975179303576739)
        ·
          refine ⟨47573678342962768955365109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31715785561975179303576739 47573678342962768955365109)
          ·
            refine ⟨4460032344652759589565479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47573678342962768955365109 4460032344652759589565479)
            ·
              refine ⟨6690048516979139384348219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4460032344652759589565479 6690048516979139384348219)
              ·
                refine ⟨10035072775468709076522329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6690048516979139384348219 10035072775468709076522329)
                ·
                  refine ⟨7526304581601531807391747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10035072775468709076522329 7526304581601531807391747)
                  ·
                    refine ⟨11289456872402297711087621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7526304581601531807391747 11289456872402297711087621)
                    ·
                      refine ⟨2116773163575430820828929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11289456872402297711087621 2116773163575430820828929)
                      ·
                        rfl

theorem cell23_4122401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_4122401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122401 prefixEnd_4122401 := by exact prefixLift 4122401
  have htrace : WordTrace (prefixWord ++ tailWord_4122401) baseStart_4122401 baseEnd_4122401 := by
    simpa [prefixWord, tailWord_4122401, baseEnd_4122401] using wordTrace_append hprefix tailTrace_4122401
  have hstable : (prefixWord ++ tailWord_4122401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122401).length < 2 ^ (prefixWord ++ tailWord_4122401).sum := by decide
  have hdescent : baseEnd_4122401 < baseStart_4122401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122424 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 6]
def baseStart_4122424 : Nat := 118140960795 + 4122424 * 2 ^ 59
def prefixEnd_4122424 : Nat := 4983230072969 + 3 ^ 40 * 4122424 * 2
def baseEnd_4122424 : Nat := 235198330403387136760147

theorem tailTrace_4122424 : CollatzResearch.WordTrace tailWord_4122424 prefixEnd_4122424 235198330403387136760147 := by
  unfold tailWord_4122424
  simp only [CollatzResearch.WordTrace]
  refine ⟨75178577808584688405855163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100238103744779584541140217 75178577808584688405855163)
  ·
    refine ⟨112767866712877032608782745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75178577808584688405855163 112767866712877032608782745)
    ·
      refine ⟨84575900034657774456587059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112767866712877032608782745 84575900034657774456587059)
      ·
        refine ⟨126863850051986661684880589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84575900034657774456587059 126863850051986661684880589)
        ·
          refine ⟨47573943769494998131830221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126863850051986661684880589 47573943769494998131830221)
          ·
            refine ⟨17840228913560624299436333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47573943769494998131830221 17840228913560624299436333)
            ·
              refine ⟨6690085842585234112288625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17840228913560624299436333 6690085842585234112288625)
              ·
                refine ⟨5017564381938925584216469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6690085842585234112288625 5017564381938925584216469)
                ·
                  refine ⟨235198330403387136760147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5017564381938925584216469 235198330403387136760147)
                  ·
                    rfl

theorem cell23_4122424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 6].length) (baseStart_4122424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122424 prefixEnd_4122424 := by exact prefixLift 4122424
  have htrace : WordTrace (prefixWord ++ tailWord_4122424) baseStart_4122424 baseEnd_4122424 := by
    simpa [prefixWord, tailWord_4122424, baseEnd_4122424] using wordTrace_append hprefix tailTrace_4122424
  have hstable : (prefixWord ++ tailWord_4122424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122424).length < 2 ^ (prefixWord ++ tailWord_4122424).sum := by decide
  have hdescent : baseEnd_4122424 < baseStart_4122424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122438 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4122438 : Nat := 118140960795 + 4122438 * 2 ^ 59
def prefixEnd_4122438 : Nat := 4983230072969 + 3 ^ 40 * 4122438 * 2
def baseEnd_4122438 : Nat := 2116792162359647176066259

theorem tailTrace_4122438 : CollatzResearch.WordTrace tailWord_4122438 prefixEnd_4122438 2116792162359647176066259 := by
  unfold tailWord_4122438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698677069972458037584999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100238444159412438135146645 4698677069972458037584999)
  ·
    refine ⟨7048015604958687056377499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4698677069972458037584999 7048015604958687056377499)
    ·
      refine ⟨10572023407438030584566249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7048015604958687056377499 10572023407438030584566249)
      ·
        refine ⟨7929017555578522938424687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10572023407438030584566249 7929017555578522938424687)
        ·
          refine ⟨11893526333367784407637031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7929017555578522938424687 11893526333367784407637031)
          ·
            refine ⟨17840289500051676611455547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11893526333367784407637031 17840289500051676611455547)
            ·
              refine ⟨26760434250077514917183321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17840289500051676611455547 26760434250077514917183321)
              ·
                refine ⟨20070325687558136187887491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26760434250077514917183321 20070325687558136187887491)
                ·
                  refine ⟨30105488531337204281831237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20070325687558136187887491 30105488531337204281831237)
                  ·
                    refine ⟨5644779099625725802843357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30105488531337204281831237 5644779099625725802843357)
                    ·
                      refine ⟨2116792162359647176066259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5644779099625725802843357 2116792162359647176066259)
                      ·
                        rfl

theorem cell23_4122438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4122438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122438 prefixEnd_4122438 := by exact prefixLift 4122438
  have htrace : WordTrace (prefixWord ++ tailWord_4122438) baseStart_4122438 baseEnd_4122438 := by
    simpa [prefixWord, tailWord_4122438, baseEnd_4122438] using wordTrace_append hprefix tailTrace_4122438
  have hstable : (prefixWord ++ tailWord_4122438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122438).length < 2 ^ (prefixWord ++ tailWord_4122438).sum := by decide
  have hdescent : baseEnd_4122438 < baseStart_4122438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122478 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_4122478 : Nat := 118140960795 + 4122478 * 2 ^ 59
def prefixEnd_4122478 : Nat := 4983230072969 + 3 ^ 40 * 4122478 * 2
def baseEnd_4122478 : Nat := 2116812701585827019566075

theorem tailTrace_4122478 : CollatzResearch.WordTrace tailWord_4122478 prefixEnd_4122478 2116812701585827019566075 := by
  unfold tailWord_4122478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18794890644871718004272011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100239416772649162689450725 18794890644871718004272011)
  ·
    refine ⟨28192335967307577006408017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18794890644871718004272011 28192335967307577006408017)
    ·
      refine ⟨21144251975480682754806013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28192335967307577006408017 21144251975480682754806013)
      ·
        refine ⟨7929094490805256033052255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21144251975480682754806013 7929094490805256033052255)
        ·
          refine ⟨11893641736207884049578383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7929094490805256033052255 11893641736207884049578383)
          ·
            refine ⟨17840462604311826074367575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11893641736207884049578383 17840462604311826074367575)
            ·
              refine ⟨26760693906467739111551363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17840462604311826074367575 26760693906467739111551363)
              ·
                refine ⟨40141040859701608667327045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26760693906467739111551363 40141040859701608667327045)
                ·
                  refine ⟨7526445161194051625123821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40141040859701608667327045 7526445161194051625123821)
                  ·
                    refine ⟨2822416935447769359421433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7526445161194051625123821 2822416935447769359421433)
                    ·
                      refine ⟨2116812701585827019566075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822416935447769359421433 2116812701585827019566075)
                      ·
                        rfl

theorem cell23_4122478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_4122478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122478 prefixEnd_4122478 := by exact prefixLift 4122478
  have htrace : WordTrace (prefixWord ++ tailWord_4122478) baseStart_4122478 baseEnd_4122478 := by
    simpa [prefixWord, tailWord_4122478, baseEnd_4122478] using wordTrace_append hprefix tailTrace_4122478
  have hstable : (prefixWord ++ tailWord_4122478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122478).length < 2 ^ (prefixWord ++ tailWord_4122478).sum := by decide
  have hdescent : baseEnd_4122478 < baseStart_4122478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122501 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_4122501 : Nat := 118140960795 + 4122501 * 2 ^ 59
def prefixEnd_4122501 : Nat := 4983230072969 + 3 ^ 40 * 4122501 * 2
def baseEnd_4122501 : Nat := 705608170546960143192823

theorem tailTrace_4122501 : CollatzResearch.WordTrace tailWord_4122501 prefixEnd_4122501 705608170546960143192823 := by
  unfold tailWord_4122501
  simp only [CollatzResearch.WordTrace]
  refine ⟨150359964037890418962263357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100239976025260279308175571 150359964037890418962263357)
  ·
    refine ⟨56384986514208907110848759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150359964037890418962263357 56384986514208907110848759)
    ·
      refine ⟨84577479771313360666273139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56384986514208907110848759 84577479771313360666273139)
      ·
        refine ⟨126866219656970040999409709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84577479771313360666273139 126866219656970040999409709)
        ·
          refine ⟨47574832371363765374778641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126866219656970040999409709 47574832371363765374778641)
          ·
            refine ⟨35681124278522824031083981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47574832371363765374778641 35681124278522824031083981)
            ·
              refine ⟨13380421604446059011656493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35681124278522824031083981 13380421604446059011656493)
              ·
                refine ⟨5017658101667272129371185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13380421604446059011656493 5017658101667272129371185)
                ·
                  refine ⟨3763243576250454097028389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5017658101667272129371185 3763243576250454097028389)
                  ·
                    refine ⟨705608170546960143192823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763243576250454097028389 705608170546960143192823)
                    ·
                      rfl

theorem cell23_4122501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_4122501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122501 prefixEnd_4122501 := by exact prefixLift 4122501
  have htrace : WordTrace (prefixWord ++ tailWord_4122501) baseStart_4122501 baseEnd_4122501 := by
    simpa [prefixWord, tailWord_4122501, baseEnd_4122501] using wordTrace_append hprefix tailTrace_4122501
  have hstable : (prefixWord ++ tailWord_4122501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122501).length < 2 ^ (prefixWord ++ tailWord_4122501).sum := by decide
  have hdescent : baseEnd_4122501 < baseStart_4122501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122536 : List Nat := [2, 1, 6, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4122536 : Nat := 118140960795 + 4122536 * 2 ^ 59
def prefixEnd_4122536 : Nat := 4983230072969 + 3 ^ 40 * 4122536 * 2
def baseEnd_4122536 : Nat := 2116842483463787792640809

theorem tailTrace_4122536 : CollatzResearch.WordTrace tailWord_4122536 prefixEnd_4122536 2116842483463787792640809 := by
  unfold tailWord_4122536
  simp only [CollatzResearch.WordTrace]
  refine ⟨75180620296381809969893731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100240827061842413293191641 75180620296381809969893731)
  ·
    refine ⟨112770930444572714954840597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75180620296381809969893731 112770930444572714954840597)
    ·
      refine ⟨5286137364589346013508153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112770930444572714954840597 5286137364589346013508153)
      ·
        refine ⟨3964603023442009510131115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5286137364589346013508153 3964603023442009510131115)
        ·
          refine ⟨5946904535163014265196673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964603023442009510131115 5946904535163014265196673)
          ·
            refine ⟨4460178401372260698897505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5946904535163014265196673 4460178401372260698897505)
            ·
              refine ⟨3345133801029195524173129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460178401372260698897505 3345133801029195524173129)
              ·
                refine ⟨2508850350771896643129847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3345133801029195524173129 2508850350771896643129847)
                ·
                  refine ⟨3763275526157844964694771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2508850350771896643129847 3763275526157844964694771)
                  ·
                    refine ⟨5644913289236767447042157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3763275526157844964694771 5644913289236767447042157)
                    ·
                      refine ⟨2116842483463787792640809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5644913289236767447042157 2116842483463787792640809)
                      ·
                        rfl

theorem cell23_4122536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4122536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122536 prefixEnd_4122536 := by exact prefixLift 4122536
  have htrace : WordTrace (prefixWord ++ tailWord_4122536) baseStart_4122536 baseEnd_4122536 := by
    simpa [prefixWord, tailWord_4122536, baseEnd_4122536] using wordTrace_append hprefix tailTrace_4122536
  have hstable : (prefixWord ++ tailWord_4122536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122536).length < 2 ^ (prefixWord ++ tailWord_4122536).sum := by decide
  have hdescent : baseEnd_4122536 < baseStart_4122536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122558 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_4122558 : Nat := 118140960795 + 4122558 * 2 ^ 59
def prefixEnd_4122558 : Nat := 4983230072969 + 3 ^ 40 * 4122558 * 2
def baseEnd_4122558 : Nat := 2116853780038186706565707

theorem tailTrace_4122558 : CollatzResearch.WordTrace tailWord_4122558 prefixEnd_4122558 2116853780038186706565707 := by
  unfold tailWord_4122558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18795255374835489712136041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100241361999122611798058885 18795255374835489712136041)
  ·
    refine ⟨14096441531126617284102031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18795255374835489712136041 14096441531126617284102031)
    ·
      refine ⟨21144662296689925926153047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14096441531126617284102031 21144662296689925926153047)
      ·
        refine ⟨31716993445034888889229571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21144662296689925926153047 31716993445034888889229571)
        ·
          refine ⟨47575490167552333333844357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31716993445034888889229571 47575490167552333333844357)
          ·
            refine ⟨8920404406416062500095817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47575490167552333333844357 8920404406416062500095817)
            ·
              refine ⟨6690303304812046875071863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8920404406416062500095817 6690303304812046875071863)
              ·
                refine ⟨10035454957218070312607795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6690303304812046875071863 10035454957218070312607795)
                ·
                  refine ⟨15053182435827105468911693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10035454957218070312607795 15053182435827105468911693)
                  ·
                    refine ⟨5644943413435164550841885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15053182435827105468911693 5644943413435164550841885)
                    ·
                      refine ⟨2116853780038186706565707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5644943413435164550841885 2116853780038186706565707)
                      ·
                        rfl

theorem cell23_4122558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_4122558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122558 prefixEnd_4122558 := by exact prefixLift 4122558
  have htrace : WordTrace (prefixWord ++ tailWord_4122558) baseStart_4122558 baseEnd_4122558 := by
    simpa [prefixWord, tailWord_4122558, baseEnd_4122558] using wordTrace_append hprefix tailTrace_4122558
  have hstable : (prefixWord ++ tailWord_4122558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122558).length < 2 ^ (prefixWord ++ tailWord_4122558).sum := by decide
  have hdescent : baseEnd_4122558 < baseStart_4122558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122568 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 3, 3, 2]
def baseStart_4122568 : Nat := 118140960795 + 4122568 * 2 ^ 59
def prefixEnd_4122568 : Nat := 4983230072969 + 3 ^ 40 * 4122568 * 2
def baseEnd_4122568 : Nat := 2116858914844731667440661

theorem tailTrace_4122568 : CollatzResearch.WordTrace tailWord_4122568 prefixEnd_4122568 2116858914844731667440661 := by
  unfold tailWord_4122568
  simp only [CollatzResearch.WordTrace]
  refine ⟨75181203864323844702476179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100241605152431792936634905 75181203864323844702476179)
  ·
    refine ⟨112771805796485767053714269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75181203864323844702476179 112771805796485767053714269)
    ·
      refine ⟨42289427173682162645142851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112771805796485767053714269 42289427173682162645142851)
      ·
        refine ⟨63434140760523243967714277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42289427173682162645142851 63434140760523243967714277)
        ·
          refine ⟨11893901392598108243946427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63434140760523243967714277 11893901392598108243946427)
          ·
            refine ⟨17840852088897162365919641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11893901392598108243946427 17840852088897162365919641)
            ·
              refine ⟨13380639066672871774439731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17840852088897162365919641 13380639066672871774439731)
              ·
                refine ⟨20070958600009307661659597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13380639066672871774439731 20070958600009307661659597)
                ·
                  refine ⟨7526609475003490373122349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20070958600009307661659597 7526609475003490373122349)
                  ·
                    refine ⟨2822478553126308889920881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7526609475003490373122349 2822478553126308889920881)
                    ·
                      refine ⟨2116858914844731667440661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822478553126308889920881 2116858914844731667440661)
                      ·
                        rfl

theorem cell23_4122568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_4122568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122568 prefixEnd_4122568 := by exact prefixLift 4122568
  have htrace : WordTrace (prefixWord ++ tailWord_4122568) baseStart_4122568 baseEnd_4122568 := by
    simpa [prefixWord, tailWord_4122568, baseEnd_4122568] using wordTrace_append hprefix tailTrace_4122568
  have hstable : (prefixWord ++ tailWord_4122568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122568).length < 2 ^ (prefixWord ++ tailWord_4122568).sum := by decide
  have hdescent : baseEnd_4122568 < baseStart_4122568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122574 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_4122574 : Nat := 118140960795 + 4122574 * 2 ^ 59
def prefixEnd_4122574 : Nat := 4983230072969 + 3 ^ 40 * 4122574 * 2
def baseEnd_4122574 : Nat := 705620665242886214655211

theorem tailTrace_4122574 : CollatzResearch.WordTrace tailWord_4122574 prefixEnd_4122574 705620665242886214655211 := by
  unfold tailWord_4122574
  simp only [CollatzResearch.WordTrace]
  refine ⟨18795328320828244053708847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100241751044417301619780517 18795328320828244053708847)
  ·
    refine ⟨28192992481242366080563271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18795328320828244053708847 28192992481242366080563271)
    ·
      refine ⟨42289488721863549120844907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28192992481242366080563271 42289488721863549120844907)
      ·
        refine ⟨63434233082795323681267361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42289488721863549120844907 63434233082795323681267361)
        ·
          refine ⟨47575674812096492760950521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63434233082795323681267361 47575674812096492760950521)
          ·
            refine ⟨35681756109072369570712891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47575674812096492760950521 35681756109072369570712891)
            ·
              refine ⟨53522634163608554356069337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35681756109072369570712891 53522634163608554356069337)
              ·
                refine ⟨40141975622706415767052003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53522634163608554356069337 40141975622706415767052003)
                ·
                  refine ⟨60212963434059623650578005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40141975622706415767052003 60212963434059623650578005)
                  ·
                    refine ⟨705620665242886214655211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60212963434059623650578005 705620665242886214655211)
                    ·
                      rfl

theorem cell23_4122574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_4122574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122574 prefixEnd_4122574 := by exact prefixLift 4122574
  have htrace : WordTrace (prefixWord ++ tailWord_4122574) baseStart_4122574 baseEnd_4122574 := by
    simpa [prefixWord, tailWord_4122574, baseEnd_4122574] using wordTrace_append hprefix tailTrace_4122574
  have hstable : (prefixWord ++ tailWord_4122574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122574).length < 2 ^ (prefixWord ++ tailWord_4122574).sum := by decide
  have hdescent : baseEnd_4122574 < baseStart_4122574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122584 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_4122584 : Nat := 118140960795 + 4122584 * 2 ^ 59
def prefixEnd_4122584 : Nat := 4983230072969 + 3 ^ 40 * 4122584 * 2
def baseEnd_4122584 : Nat := 2116867130535203604840587

theorem tailTrace_4122584 : CollatzResearch.WordTrace tailWord_4122584 prefixEnd_4122584 2116867130535203604840587 := by
  unfold tailWord_4122584
  simp only [CollatzResearch.WordTrace]
  refine ⟨75181495648294862068767403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100241994197726482758356537 75181495648294862068767403)
  ·
    refine ⟨112772243472442293103151105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75181495648294862068767403 112772243472442293103151105)
    ·
      refine ⟨84579182604331719827363329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112772243472442293103151105 84579182604331719827363329)
      ·
        refine ⟨63434386953248789870522497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84579182604331719827363329 63434386953248789870522497)
        ·
          refine ⟨47575790214936592402891873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63434386953248789870522497 47575790214936592402891873)
          ·
            refine ⟨35681842661202444302168905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47575790214936592402891873 35681842661202444302168905)
            ·
              refine ⟨26761381995901833226626679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35681842661202444302168905 26761381995901833226626679)
              ·
                refine ⟨40142072993852749839940019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26761381995901833226626679 40142072993852749839940019)
                ·
                  refine ⟨60213109490779124759910029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40142072993852749839940019 60213109490779124759910029)
                  ·
                    refine ⟨22579916059042171784966261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60213109490779124759910029 22579916059042171784966261)
                    ·
                      refine ⟨2116867130535203604840587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22579916059042171784966261 2116867130535203604840587)
                      ·
                        rfl

theorem cell23_4122584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_4122584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122584 prefixEnd_4122584 := by exact prefixLift 4122584
  have htrace : WordTrace (prefixWord ++ tailWord_4122584) baseStart_4122584 baseEnd_4122584 := by
    simpa [prefixWord, tailWord_4122584, baseEnd_4122584] using wordTrace_append hprefix tailTrace_4122584
  have hstable : (prefixWord ++ tailWord_4122584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122584).length < 2 ^ (prefixWord ++ tailWord_4122584).sum := by decide
  have hdescent : baseEnd_4122584 < baseStart_4122584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122585 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 1, 3, 2]
def baseStart_4122585 : Nat := 118140960795 + 4122585 * 2 ^ 59
def prefixEnd_4122585 : Nat := 4983230072969 + 3 ^ 40 * 4122585 * 2
def baseEnd_4122585 : Nat := 2116867644015858100928083

theorem tailTrace_4122585 : CollatzResearch.WordTrace tailWord_4122585 prefixEnd_4122585 2116867644015858100928083 := by
  unfold tailWord_4122585
  simp only [CollatzResearch.WordTrace]
  refine ⟨150363027769586101308321209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100242018513057400872214139 150363027769586101308321209)
  ·
    refine ⟨112772270827189575981240907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150363027769586101308321209 112772270827189575981240907)
    ·
      refine ⟨169158406240784363971861361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112772270827189575981240907 169158406240784363971861361)
      ·
        refine ⟨126868804680588272978896021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169158406240784363971861361 126868804680588272978896021)
        ·
          refine ⟨5946975219402575295885751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126868804680588272978896021 5946975219402575295885751)
          ·
            refine ⟨8920462829103862943828627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5946975219402575295885751 8920462829103862943828627)
            ·
              refine ⟨13380694243655794415742941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8920462829103862943828627 13380694243655794415742941)
              ·
                refine ⟨5017760341370922905903603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13380694243655794415742941 5017760341370922905903603)
                ·
                  refine ⟨7526640512056384358855405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5017760341370922905903603 7526640512056384358855405)
                  ·
                    refine ⟨2822490192021144134570777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7526640512056384358855405 2822490192021144134570777)
                    ·
                      refine ⟨2116867644015858100928083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822490192021144134570777 2116867644015858100928083)
                      ·
                        rfl

theorem cell23_4122585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_4122585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122585 prefixEnd_4122585 := by exact prefixLift 4122585
  have htrace : WordTrace (prefixWord ++ tailWord_4122585) baseStart_4122585 baseEnd_4122585 := by
    simpa [prefixWord, tailWord_4122585, baseEnd_4122585] using wordTrace_append hprefix tailTrace_4122585
  have hstable : (prefixWord ++ tailWord_4122585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122585).length < 2 ^ (prefixWord ++ tailWord_4122585).sum := by decide
  have hdescent : baseEnd_4122585 < baseStart_4122585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122641 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 3, 7, 2]
def baseStart_4122641 : Nat := 118140960795 + 4122641 * 2 ^ 59
def prefixEnd_4122641 : Nat := 4983230072969 + 3 ^ 40 * 4122641 * 2
def baseEnd_4122641 : Nat := 2116896398932509881827825

theorem tailTrace_4122641 : CollatzResearch.WordTrace tailWord_4122641 prefixEnd_4122641 2116896398932509881827825 := by
  unfold tailWord_4122641
  simp only [CollatzResearch.WordTrace]
  refine ⟨150365070257383222872359777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100243380171588815248239851 150365070257383222872359777)
  ·
    refine ⟨112773802693037417154269833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150365070257383222872359777 112773802693037417154269833)
    ·
      refine ⟨84580352019778062865702375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112773802693037417154269833 84580352019778062865702375)
      ·
        refine ⟨126870528029667094298553563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84580352019778062865702375 126870528029667094298553563)
        ·
          refine ⟨190305792044500641447830345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126870528029667094298553563 190305792044500641447830345)
          ·
            refine ⟨142729344033375481085872759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190305792044500641447830345 142729344033375481085872759)
            ·
              refine ⟨214094016050063221628809139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142729344033375481085872759 214094016050063221628809139)
              ·
                refine ⟨321141024075094832443213709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214094016050063221628809139 321141024075094832443213709)
                ·
                  refine ⟨120427884028160562166205141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321141024075094832443213709 120427884028160562166205141)
                  ·
                    refine ⟨2822528531910013175770433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 120427884028160562166205141 2822528531910013175770433)
                    ·
                      refine ⟨2116896398932509881827825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822528531910013175770433 2116896398932509881827825)
                      ·
                        rfl

theorem cell23_4122641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_4122641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122641 prefixEnd_4122641 := by exact prefixLift 4122641
  have htrace : WordTrace (prefixWord ++ tailWord_4122641) baseStart_4122641 baseEnd_4122641 := by
    simpa [prefixWord, tailWord_4122641, baseEnd_4122641] using wordTrace_append hprefix tailTrace_4122641
  have hstable : (prefixWord ++ tailWord_4122641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122641).length < 2 ^ (prefixWord ++ tailWord_4122641).sum := by decide
  have hdescent : baseEnd_4122641 < baseStart_4122641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122658 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_4122658 : Nat := 118140960795 + 4122658 * 2 ^ 59
def prefixEnd_4122658 : Nat := 4983230072969 + 3 ^ 40 * 4122658 * 2
def baseEnd_4122658 : Nat := 2116905128103636315315247

theorem tailTrace_4122658 : CollatzResearch.WordTrace tailWord_4122658 prefixEnd_4122658 2116905128103636315315247 := by
  unfold tailWord_4122658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37591422574580408693932157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100243793532214423183819085 37591422574580408693932157)
  ·
    refine ⟨14096783465467653260224559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37591422574580408693932157 14096783465467653260224559)
    ·
      refine ⟨21145175198201479890336839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14096783465467653260224559 21145175198201479890336839)
      ·
        refine ⟨31717762797302219835505259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21145175198201479890336839 31717762797302219835505259)
        ·
          refine ⟨47576644195953329753257889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31717762797302219835505259 47576644195953329753257889)
          ·
            refine ⟨35682483146964997314943417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47576644195953329753257889 35682483146964997314943417)
            ·
              refine ⟨26761862360223747986207563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35682483146964997314943417 26761862360223747986207563)
              ·
                refine ⟨40142793540335621979311345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26761862360223747986207563 40142793540335621979311345)
                ·
                  refine ⟨30107095155251716484483509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40142793540335621979311345 30107095155251716484483509)
                  ·
                    refine ⟨2822540170804848420420329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30107095155251716484483509 2822540170804848420420329)
                    ·
                      refine ⟨2116905128103636315315247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822540170804848420420329 2116905128103636315315247)
                      ·
                        rfl

theorem cell23_4122658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_4122658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122658 prefixEnd_4122658 := by exact prefixLift 4122658
  have htrace : WordTrace (prefixWord ++ tailWord_4122658) baseStart_4122658 baseEnd_4122658 := by
    simpa [prefixWord, tailWord_4122658, baseEnd_4122658] using wordTrace_append hprefix tailTrace_4122658
  have hstable : (prefixWord ++ tailWord_4122658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122658).length < 2 ^ (prefixWord ++ tailWord_4122658).sum := by decide
  have hdescent : baseEnd_4122658 < baseStart_4122658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122661 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_4122661 : Nat := 118140960795 + 4122661 * 2 ^ 59
def prefixEnd_4122661 : Nat := 4983230072969 + 3 ^ 40 * 4122661 * 2
def baseEnd_4122661 : Nat := 2116906668545599803577733

theorem tailTrace_4122661 : CollatzResearch.WordTrace tailWord_4122661 prefixEnd_4122661 2116906668545599803577733 := by
  unfold tailWord_4122661
  simp only [CollatzResearch.WordTrace]
  refine ⟨150365799717310766288087837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100243866478207177525391891 150365799717310766288087837)
  ·
    refine ⟨56387174893991537358032939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150365799717310766288087837 56387174893991537358032939)
    ·
      refine ⟨84580762340987306037049409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56387174893991537358032939 84580762340987306037049409)
      ·
        refine ⟨63435571755740479527787057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84580762340987306037049409 63435571755740479527787057)
        ·
          refine ⟨47576678816805359645840293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63435571755740479527787057 47576678816805359645840293)
          ·
            refine ⟨8920627278151004933595055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47576678816805359645840293 8920627278151004933595055)
            ·
              refine ⟨13380940917226507400392583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8920627278151004933595055 13380940917226507400392583)
              ·
                refine ⟨20071411375839761100588875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13380940917226507400392583 20071411375839761100588875)
                ·
                  refine ⟨30107117063759641650883313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20071411375839761100588875 30107117063759641650883313)
                  ·
                    refine ⟨22580337797819731238162485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30107117063759641650883313 22580337797819731238162485)
                    ·
                      refine ⟨2116906668545599803577733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22580337797819731238162485 2116906668545599803577733)
                      ·
                        rfl

theorem cell23_4122661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_4122661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122661 prefixEnd_4122661 := by exact prefixLift 4122661
  have htrace : WordTrace (prefixWord ++ tailWord_4122661) baseStart_4122661 baseEnd_4122661 := by
    simpa [prefixWord, tailWord_4122661, baseEnd_4122661] using wordTrace_append hprefix tailTrace_4122661
  have hstable : (prefixWord ++ tailWord_4122661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122661).length < 2 ^ (prefixWord ++ tailWord_4122661).sum := by decide
  have hdescent : baseEnd_4122661 < baseStart_4122661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122688 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 4]
def baseStart_4122688 : Nat := 118140960795 + 4122688 * 2 ^ 59
def prefixEnd_4122688 : Nat := 4983230072969 + 3 ^ 40 * 4122688 * 2
def baseEnd_4122688 : Nat := 2116920532523271197940109

theorem tailTrace_4122688 : CollatzResearch.WordTrace tailWord_4122688 prefixEnd_4122688 2116920532523271197940109 := by
  unfold tailWord_4122688
  simp only [CollatzResearch.WordTrace]
  refine ⟨75183392244106474949660359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100244522992141966599547145 75183392244106474949660359)
  ·
    refine ⟨112775088366159712424490539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75183392244106474949660359 112775088366159712424490539)
    ·
      refine ⟨169162632549239568636735809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112775088366159712424490539 169162632549239568636735809)
      ·
        refine ⟨126871974411929676477551857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169162632549239568636735809 126871974411929676477551857)
        ·
          refine ⟨95153980808947257358163893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126871974411929676477551857 95153980808947257358163893)
          ·
            refine ⟨8920685700838805377327865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95153980808947257358163893 8920685700838805377327865)
            ·
              refine ⟨6690514275629104032995899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8920685700838805377327865 6690514275629104032995899)
              ·
                refine ⟨10035771413443656049493849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6690514275629104032995899 10035771413443656049493849)
                ·
                  refine ⟨7526828560082742037120387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10035771413443656049493849 7526828560082742037120387)
                  ·
                    refine ⟨11290242840124113055680581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7526828560082742037120387 11290242840124113055680581)
                    ·
                      refine ⟨2116920532523271197940109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11290242840124113055680581 2116920532523271197940109)
                      ·
                        rfl

theorem cell23_4122688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_4122688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122688 prefixEnd_4122688 := by exact prefixLift 4122688
  have htrace : WordTrace (prefixWord ++ tailWord_4122688) baseStart_4122688 baseEnd_4122688 := by
    simpa [prefixWord, tailWord_4122688, baseEnd_4122688] using wordTrace_append hprefix tailTrace_4122688
  have hstable : (prefixWord ++ tailWord_4122688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122688).length < 2 ^ (prefixWord ++ tailWord_4122688).sum := by decide
  have hdescent : baseEnd_4122688 < baseStart_4122688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122711 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 6]
def baseStart_4122711 : Nat := 118140960795 + 4122711 * 2 ^ 59
def prefixEnd_4122711 : Nat := 4983230072969 + 3 ^ 40 * 4122711 * 2
def baseEnd_4122711 : Nat := 235214704730924956439167

theorem tailTrace_4122711 : CollatzResearch.WordTrace tailWord_4122711 prefixEnd_4122711 235214704730924956439167 := by
  unfold tailWord_4122711
  simp only [CollatzResearch.WordTrace]
  refine ⟨150367623367129624827407987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100245082244753083218271991 150367623367129624827407987)
  ·
    refine ⟨225551435050694437241111981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150367623367129624827407987 225551435050694437241111981)
    ·
      refine ⟨84581788144010413965416993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225551435050694437241111981 84581788144010413965416993)
      ·
        refine ⟨63436341108007810474062745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84581788144010413965416993 63436341108007810474062745)
        ·
          refine ⟨47577255831005857855547059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63436341108007810474062745 47577255831005857855547059)
          ·
            refine ⟨71365883746508786783320589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47577255831005857855547059 71365883746508786783320589)
            ·
              refine ⟨26762206404940795043745221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71365883746508786783320589 26762206404940795043745221)
              ·
                refine ⟨5017913700926399070702229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26762206404940795043745221 5017913700926399070702229)
                ·
                  refine ⟨235214704730924956439167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5017913700926399070702229 235214704730924956439167)
                  ·
                    rfl

theorem cell23_4122711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 6].length) (baseStart_4122711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122711 prefixEnd_4122711 := by exact prefixLift 4122711
  have htrace : WordTrace (prefixWord ++ tailWord_4122711) baseStart_4122711 baseEnd_4122711 := by
    simpa [prefixWord, tailWord_4122711, baseEnd_4122711] using wordTrace_append hprefix tailTrace_4122711
  have hstable : (prefixWord ++ tailWord_4122711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122711).length < 2 ^ (prefixWord ++ tailWord_4122711).sum := by decide
  have hdescent : baseEnd_4122711 < baseStart_4122711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122721 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_4122721 : Nat := 118140960795 + 4122721 * 2 ^ 59
def prefixEnd_4122721 : Nat := 4983230072969 + 3 ^ 40 * 4122721 * 2
def baseEnd_4122721 : Nat := 2116937477384869568827457

theorem tailTrace_4122721 : CollatzResearch.WordTrace tailWord_4122721 prefixEnd_4122721 2116937477384869568827457 := by
  unfold tailWord_4122721
  simp only [CollatzResearch.WordTrace]
  refine ⟨150367988097093396535272017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100245325398062264356848011 150367988097093396535272017)
  ·
    refine ⟨112775991072820047401454013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150367988097093396535272017 112775991072820047401454013)
    ·
      refine ⟨42290996652307517775545255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112775991072820047401454013 42290996652307517775545255)
      ·
        refine ⟨63436494978461276663317883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42290996652307517775545255 63436494978461276663317883)
        ·
          refine ⟨95154742467691914994976825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63436494978461276663317883 95154742467691914994976825)
          ·
            refine ⟨71366056850768936246232619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95154742467691914994976825 71366056850768936246232619)
            ·
              refine ⟨107049085276153404369348929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71366056850768936246232619 107049085276153404369348929)
              ·
                refine ⟨80286813957115053277011697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107049085276153404369348929 80286813957115053277011697)
                ·
                  refine ⟨60215110467836289957758773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80286813957115053277011697 60215110467836289957758773)
                  ·
                    refine ⟨5645166606359652183539885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60215110467836289957758773 5645166606359652183539885)
                    ·
                      refine ⟨2116937477384869568827457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5645166606359652183539885 2116937477384869568827457)
                      ·
                        rfl

theorem cell23_4122721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_4122721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122721 prefixEnd_4122721 := by exact prefixLift 4122721
  have htrace : WordTrace (prefixWord ++ tailWord_4122721) baseStart_4122721 baseEnd_4122721 := by
    simpa [prefixWord, tailWord_4122721, baseEnd_4122721] using wordTrace_append hprefix tailTrace_4122721
  have hstable : (prefixWord ++ tailWord_4122721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122721).length < 2 ^ (prefixWord ++ tailWord_4122721).sum := by decide
  have hdescent : baseEnd_4122721 < baseStart_4122721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122722 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4122722 : Nat := 118140960795 + 4122722 * 2 ^ 59
def prefixEnd_4122722 : Nat := 4983230072969 + 3 ^ 40 * 4122722 * 2
def baseEnd_4122722 : Nat := 2116937990865524064914953

theorem tailTrace_4122722 : CollatzResearch.WordTrace tailWord_4122722 prefixEnd_4122722 2116937990865524064914953 := by
  unfold tailWord_4122722
  simp only [CollatzResearch.WordTrace]
  refine ⟨37592006142522443426514605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100245349713393182470705613 37592006142522443426514605)
  ·
    refine ⟨14097002303445916284942977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37592006142522443426514605 14097002303445916284942977)
    ·
      refine ⟨10572751727584437213707233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14097002303445916284942977 10572751727584437213707233)
      ·
        refine ⟨7929563795688327910280425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10572751727584437213707233 7929563795688327910280425)
        ·
          refine ⟨5947172846766245932710319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7929563795688327910280425 5947172846766245932710319)
          ·
            refine ⟨8920759270149368899065479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947172846766245932710319 8920759270149368899065479)
            ·
              refine ⟨13381138905224053348598219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8920759270149368899065479 13381138905224053348598219)
              ·
                refine ⟨20071708357836080022897329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13381138905224053348598219 20071708357836080022897329)
                ·
                  refine ⟨15053781268377060017172997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20071708357836080022897329 15053781268377060017172997)
                  ·
                    refine ⟨2822583987820698753219937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15053781268377060017172997 2822583987820698753219937)
                    ·
                      refine ⟨2116937990865524064914953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822583987820698753219937 2116937990865524064914953)
                      ·
                        rfl

theorem cell23_4122722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4122722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122722 prefixEnd_4122722 := by exact prefixLift 4122722
  have htrace : WordTrace (prefixWord ++ tailWord_4122722) baseStart_4122722 baseEnd_4122722 := by
    simpa [prefixWord, tailWord_4122722, baseEnd_4122722] using wordTrace_append hprefix tailTrace_4122722
  have hstable : (prefixWord ++ tailWord_4122722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122722).length < 2 ^ (prefixWord ++ tailWord_4122722).sum := by decide
  have hdescent : baseEnd_4122722 < baseStart_4122722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122742 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_4122742 : Nat := 118140960795 + 4122742 * 2 ^ 59
def prefixEnd_4122742 : Nat := 4983230072969 + 3 ^ 40 * 4122742 * 2
def baseEnd_4122742 : Nat := 2116948260478613986664861

theorem tailTrace_4122742 : CollatzResearch.WordTrace tailWord_4122742 prefixEnd_4122742 2116948260478613986664861 := by
  unfold tailWord_4122742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9398047126876082320111655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100245836020011544747857653 9398047126876082320111655)
  ·
    refine ⟨14097070690314123480167483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9398047126876082320111655 14097070690314123480167483)
    ·
      refine ⟨21145606035471185220251225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14097070690314123480167483 21145606035471185220251225)
      ·
        refine ⟨15859204526603388915188419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21145606035471185220251225 15859204526603388915188419)
        ·
          refine ⟨23788806789905083372782629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15859204526603388915188419 23788806789905083372782629)
          ·
            refine ⟨4460401273107203132396743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23788806789905083372782629 4460401273107203132396743)
            ·
              refine ⟨6690601909660804698595115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4460401273107203132396743 6690601909660804698595115)
              ·
                refine ⟨10035902864491207047892673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6690601909660804698595115 10035902864491207047892673)
                ·
                  refine ⟨7526927148368405285919505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10035902864491207047892673 7526927148368405285919505)
                  ·
                    refine ⟨5645195361276303964439629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7526927148368405285919505 5645195361276303964439629)
                    ·
                      refine ⟨2116948260478613986664861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5645195361276303964439629 2116948260478613986664861)
                      ·
                        rfl

theorem cell23_4122742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_4122742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122742 prefixEnd_4122742 := by exact prefixLift 4122742
  have htrace : WordTrace (prefixWord ++ tailWord_4122742) baseStart_4122742 baseEnd_4122742 := by
    simpa [prefixWord, tailWord_4122742, baseEnd_4122742] using wordTrace_append hprefix tailTrace_4122742
  have hstable : (prefixWord ++ tailWord_4122742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122742).length < 2 ^ (prefixWord ++ tailWord_4122742).sum := by decide
  have hdescent : baseEnd_4122742 < baseStart_4122742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122831 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 2, 7]
def baseStart_4122831 : Nat := 118140960795 + 4122831 * 2 ^ 59
def prefixEnd_4122831 : Nat := 4983230072969 + 3 ^ 40 * 4122831 * 2
def baseEnd_4122831 : Nat := 705664653418954712817317

theorem tailTrace_4122831 : CollatzResearch.WordTrace tailWord_4122831 prefixEnd_4122831 705664653418954712817317 := by
  unfold tailWord_4122831
  simp only [CollatzResearch.WordTrace]
  refine ⟨150372000126694885321776347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100248000084463256881184231 150372000126694885321776347)
  ·
    refine ⟨225558000190042327982664521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150372000126694885321776347 225558000190042327982664521)
    ·
      refine ⟨169168500142531745986998391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225558000190042327982664521 169168500142531745986998391)
      ·
        refine ⟨253752750213797618980497587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169168500142531745986998391 253752750213797618980497587)
        ·
          refine ⟨380629125320696428470746381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253752750213797618980497587 380629125320696428470746381)
          ·
            refine ⟨142735921995261160676529893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380629125320696428470746381 142735921995261160676529893)
            ·
              refine ⟨26762985374111467626849355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142735921995261160676529893 26762985374111467626849355)
              ·
                refine ⟨40144478061167201440274033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26762985374111467626849355 40144478061167201440274033)
                ·
                  refine ⟨30108358545875401080205525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40144478061167201440274033 30108358545875401080205525)
                  ·
                    refine ⟨705664653418954712817317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30108358545875401080205525 705664653418954712817317)
                    ·
                      rfl

theorem cell23_4122831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_4122831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122831 prefixEnd_4122831 := by exact prefixLift 4122831
  have htrace : WordTrace (prefixWord ++ tailWord_4122831) baseStart_4122831 baseEnd_4122831 := by
    simpa [prefixWord, tailWord_4122831, baseEnd_4122831] using wordTrace_append hprefix tailTrace_4122831
  have hstable : (prefixWord ++ tailWord_4122831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122831).length < 2 ^ (prefixWord ++ tailWord_4122831).sum := by decide
  have hdescent : baseEnd_4122831 < baseStart_4122831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122942 : List Nat := [4, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_4122942 : Nat := 118140960795 + 4122942 * 2 ^ 59
def prefixEnd_4122942 : Nat := 4983230072969 + 3 ^ 40 * 4122942 * 2
def baseEnd_4122942 : Nat := 235227884067723689351549

theorem tailTrace_4122942 : CollatzResearch.WordTrace tailWord_4122942 prefixEnd_4122942 235227884067723689351549 := by
  unfold tailWord_4122942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18797006078661593909883385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100250699086195167519378053 18797006078661593909883385)
  ·
    refine ⟨14097754558996195432412539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18797006078661593909883385 14097754558996195432412539)
    ·
      refine ⟨21146631838494293148618809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14097754558996195432412539 21146631838494293148618809)
      ·
        refine ⟨15859973878870719861464107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21146631838494293148618809 15859973878870719861464107)
        ·
          refine ⟨23789960818306079792196161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15859973878870719861464107 23789960818306079792196161)
          ·
            refine ⟨17842470613729559844147121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23789960818306079792196161 17842470613729559844147121)
            ·
              refine ⟨13381852960297169883110341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17842470613729559844147121 13381852960297169883110341)
              ·
                refine ⟨2509097430055719353083189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13381852960297169883110341 2509097430055719353083189)
                ·
                  refine ⟨235227884067723689351549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2509097430055719353083189 235227884067723689351549)
                  ·
                    rfl

theorem cell23_4122942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_4122942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122942 prefixEnd_4122942 := by exact prefixLift 4122942
  have htrace : WordTrace (prefixWord ++ tailWord_4122942) baseStart_4122942 baseEnd_4122942 := by
    simpa [prefixWord, tailWord_4122942, baseEnd_4122942] using wordTrace_append hprefix tailTrace_4122942
  have hstable : (prefixWord ++ tailWord_4122942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122942).length < 2 ^ (prefixWord ++ tailWord_4122942).sum := by decide
  have hdescent : baseEnd_4122942 < baseStart_4122942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122975 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 1, 6, 2]
def baseStart_4122975 : Nat := 118140960795 + 4122975 * 2 ^ 59
def prefixEnd_4122975 : Nat := 4983230072969 + 3 ^ 40 * 4122975 * 2
def baseEnd_4122975 : Nat := 2117067901471111575051289

theorem tailTrace_4122975 : CollatzResearch.WordTrace tailWord_4122975 prefixEnd_4122975 2117067901471111575051289 := by
  unfold tailWord_4122975
  simp only [CollatzResearch.WordTrace]
  refine ⟨150377252238173197915018379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100251501492115465276678919 150377252238173197915018379)
  ·
    refine ⟨225565878357259796872527569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150377252238173197915018379 225565878357259796872527569)
    ·
      refine ⟨169174408767944847654395677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225565878357259796872527569 169174408767944847654395677)
      ·
        refine ⟨63440403287979317870398379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169174408767944847654395677 63440403287979317870398379)
        ·
          refine ⟨95160604931968976805597569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63440403287979317870398379 95160604931968976805597569)
          ·
            refine ⟨71370453698976732604198177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95160604931968976805597569 71370453698976732604198177)
            ·
              refine ⟨53527840274232549453148633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71370453698976732604198177 53527840274232549453148633)
              ·
                refine ⟨40145880205674412089861475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53527840274232549453148633 40145880205674412089861475)
                ·
                  refine ⟨60218820308511618134792213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40145880205674412089861475 60218820308511618134792213)
                  ·
                    refine ⟨2822757201961482100068385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60218820308511618134792213 2822757201961482100068385)
                    ·
                      refine ⟨2117067901471111575051289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822757201961482100068385 2117067901471111575051289)
                      ·
                        rfl

theorem cell23_4122975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_4122975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122975 prefixEnd_4122975 := by exact prefixLift 4122975
  have htrace : WordTrace (prefixWord ++ tailWord_4122975) baseStart_4122975 baseEnd_4122975 := by
    simpa [prefixWord, tailWord_4122975, baseEnd_4122975] using wordTrace_append hprefix tailTrace_4122975
  have hstable : (prefixWord ++ tailWord_4122975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122975).length < 2 ^ (prefixWord ++ tailWord_4122975).sum := by decide
  have hdescent : baseEnd_4122975 < baseStart_4122975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122995 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 3]
def baseStart_4122995 : Nat := 118140960795 + 4122995 * 2 ^ 59
def prefixEnd_4122995 : Nat := 4983230072969 + 3 ^ 40 * 4122995 * 2
def baseEnd_4122995 : Nat := 2117078171084201496801197

theorem tailTrace_4122995 : CollatzResearch.WordTrace tailWord_4122995 prefixEnd_4122995 2117078171084201496801197 := by
  unfold tailWord_4122995
  simp only [CollatzResearch.WordTrace]
  refine ⟨150377981698100741330746439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100251987798733827553830959 150377981698100741330746439)
  ·
    refine ⟨225566972547151111996119659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150377981698100741330746439 225566972547151111996119659)
    ·
      refine ⟨338350458820726667994179489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225566972547151111996119659 338350458820726667994179489)
      ·
        refine ⟨253762844115545000995634617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338350458820726667994179489 253762844115545000995634617)
        ·
          refine ⟨190322133086658750746725963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253762844115545000995634617 190322133086658750746725963)
          ·
            refine ⟨285483199629988126120088945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190322133086658750746725963 285483199629988126120088945)
            ·
              refine ⟨214112399722491094590066709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285483199629988126120088945 214112399722491094590066709)
              ·
                refine ⟨10036518736991770058909377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214112399722491094590066709 10036518736991770058909377)
                ·
                  refine ⟨7527389052743827544182033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10036518736991770058909377 7527389052743827544182033)
                  ·
                    refine ⟨5645541789557870658136525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7527389052743827544182033 5645541789557870658136525)
                    ·
                      refine ⟨2117078171084201496801197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5645541789557870658136525 2117078171084201496801197)
                      ·
                        rfl

theorem cell23_4122995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 3].length) (baseStart_4122995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4122995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4122995 prefixEnd_4122995 := by exact prefixLift 4122995
  have htrace : WordTrace (prefixWord ++ tailWord_4122995) baseStart_4122995 baseEnd_4122995 := by
    simpa [prefixWord, tailWord_4122995, baseEnd_4122995] using wordTrace_append hprefix tailTrace_4122995
  have hstable : (prefixWord ++ tailWord_4122995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122995).length < 2 ^ (prefixWord ++ tailWord_4122995).sum := by decide
  have hdescent : baseEnd_4122995 < baseStart_4122995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123015 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 6]
def baseStart_4123015 : Nat := 118140960795 + 4123015 * 2 ^ 59
def prefixEnd_4123015 : Nat := 4983230072969 + 3 ^ 40 * 4123015 * 2
def baseEnd_4123015 : Nat := 235232048966365713172345

theorem tailTrace_4123015 : CollatzResearch.WordTrace tailWord_4123015 prefixEnd_4123015 235232048966365713172345 := by
  unfold tailWord_4123015
  simp only [CollatzResearch.WordTrace]
  refine ⟨150378711158028284746474499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100252474105352189830982999 150378711158028284746474499)
  ·
    refine ⟨225568066737042427119711749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150378711158028284746474499 225568066737042427119711749)
    ·
      refine ⟨42294012513195455084945953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225568066737042427119711749 42294012513195455084945953)
      ·
        refine ⟨31720509384896591313709465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42294012513195455084945953 31720509384896591313709465)
        ·
          refine ⟨23790382038672443485282099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31720509384896591313709465 23790382038672443485282099)
          ·
            refine ⟨35685573058008665227923149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23790382038672443485282099 35685573058008665227923149)
            ·
              refine ⟨13382089896753249460471181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35685573058008665227923149 13382089896753249460471181)
              ·
                refine ⟨5018283711282468547676693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13382089896753249460471181 5018283711282468547676693)
                ·
                  refine ⟨235232048966365713172345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5018283711282468547676693 235232048966365713172345)
                  ·
                    rfl

theorem cell23_4123015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 6].length) (baseStart_4123015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123015 prefixEnd_4123015 := by exact prefixLift 4123015
  have htrace : WordTrace (prefixWord ++ tailWord_4123015) baseStart_4123015 baseEnd_4123015 := by
    simpa [prefixWord, tailWord_4123015, baseEnd_4123015] using wordTrace_append hprefix tailTrace_4123015
  have hstable : (prefixWord ++ tailWord_4123015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123015).length < 2 ^ (prefixWord ++ tailWord_4123015).sum := by decide
  have hdescent : baseEnd_4123015 < baseStart_4123015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123075 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 6, 4]
def baseStart_4123075 : Nat := 118140960795 + 4123075 * 2 ^ 59
def prefixEnd_4123075 : Nat := 4983230072969 + 3 ^ 40 * 4123075 * 2
def baseEnd_4123075 : Nat := 705706416512187061266943

theorem tailTrace_4123075 : CollatzResearch.WordTrace tailWord_4123075 prefixEnd_4123075 705706416512187061266943 := by
  unfold tailWord_4123075
  simp only [CollatzResearch.WordTrace]
  refine ⟨150380899537810914993658679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100253933025207276662439119 150380899537810914993658679)
  ·
    refine ⟨225571349306716372490488019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150380899537810914993658679 225571349306716372490488019)
    ·
      refine ⟨338357023960074558735732029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225571349306716372490488019 338357023960074558735732029)
      ·
        refine ⟨126883883985027959525899511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338357023960074558735732029 126883883985027959525899511)
        ·
          refine ⟨190325825977541939288849267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126883883985027959525899511 190325825977541939288849267)
          ·
            refine ⟨285488738966312908933273901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190325825977541939288849267 285488738966312908933273901)
            ·
              refine ⟨107058277112367340849977713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285488738966312908933273901 107058277112367340849977713)
              ·
                refine ⟨80293707834275505637483285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107058277112367340849977713 80293707834275505637483285)
                ·
                  refine ⟨3763767554731664326757029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80293707834275505637483285 3763767554731664326757029)
                  ·
                    refine ⟨705706416512187061266943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763767554731664326757029 705706416512187061266943)
                    ·
                      rfl

theorem cell23_4123075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 4].length) (baseStart_4123075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123075 prefixEnd_4123075 := by exact prefixLift 4123075
  have htrace : WordTrace (prefixWord ++ tailWord_4123075) baseStart_4123075 baseEnd_4123075 := by
    simpa [prefixWord, tailWord_4123075, baseEnd_4123075] using wordTrace_append hprefix tailTrace_4123075
  have hstable : (prefixWord ++ tailWord_4123075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123075).length < 2 ^ (prefixWord ++ tailWord_4123075).sum := by decide
  have hdescent : baseEnd_4123075 < baseStart_4123075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123076 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4123076 : Nat := 118140960795 + 4123076 * 2 ^ 59
def prefixEnd_4123076 : Nat := 4983230072969 + 3 ^ 40 * 4123076 * 2
def baseEnd_4123076 : Nat := 2117119763017215679888325

theorem tailTrace_4123076 : CollatzResearch.WordTrace tailWord_4123076 prefixEnd_4123076 2117119763017215679888325 := by
  unfold tailWord_4123076
  simp only [CollatzResearch.WordTrace]
  refine ⟨75190468005403646082222541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100253957340538194776296721 75190468005403646082222541)
  ·
    refine ⟨28196425502026367280833453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75190468005403646082222541 28196425502026367280833453)
    ·
      refine ⟨10573659563259887730312545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28196425502026367280833453 10573659563259887730312545)
      ·
        refine ⟨7930244672444915797734409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10573659563259887730312545 7930244672444915797734409)
        ·
          refine ⟨5947683504333686848300807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7930244672444915797734409 5947683504333686848300807)
          ·
            refine ⟨8921525256500530272451211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947683504333686848300807 8921525256500530272451211)
            ·
              refine ⟨13382287884750795408676817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921525256500530272451211 13382287884750795408676817)
              ·
                refine ⟨10036715913563096556507613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13382287884750795408676817 10036715913563096556507613)
                ·
                  refine ⟨3763768467586161208690355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10036715913563096556507613 3763768467586161208690355)
                  ·
                    refine ⟨5645652701379241813035533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3763768467586161208690355 5645652701379241813035533)
                    ·
                      refine ⟨2117119763017215679888325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5645652701379241813035533 2117119763017215679888325)
                      ·
                        rfl

theorem cell23_4123076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4123076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123076 prefixEnd_4123076 := by exact prefixLift 4123076
  have htrace : WordTrace (prefixWord ++ tailWord_4123076) baseStart_4123076 baseEnd_4123076 := by
    simpa [prefixWord, tailWord_4123076, baseEnd_4123076] using wordTrace_append hprefix tailTrace_4123076
  have hstable : (prefixWord ++ tailWord_4123076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123076).length < 2 ^ (prefixWord ++ tailWord_4123076).sum := by decide
  have hdescent : baseEnd_4123076 < baseStart_4123076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123082 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_4123082 : Nat := 118140960795 + 4123082 * 2 ^ 59
def prefixEnd_4123082 : Nat := 4983230072969 + 3 ^ 40 * 4123082 * 2
def baseEnd_4123082 : Nat := 2117122843901142656413297

theorem tailTrace_4123082 : CollatzResearch.WordTrace tailWord_4123082 prefixEnd_4123082 2117122843901142656413297 := by
  unfold tailWord_4123082
  simp only [CollatzResearch.WordTrace]
  refine ⟨37595288712196388797290875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100254103232523703459442333 37595288712196388797290875)
  ·
    refine ⟨56392933068294583195936313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37595288712196388797290875 56392933068294583195936313)
    ·
      refine ⟨42294699801220937396952235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56392933068294583195936313 42294699801220937396952235)
      ·
        refine ⟨63442049701831406095428353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42294699801220937396952235 63442049701831406095428353)
        ·
          refine ⟨47581537276373554571571265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63442049701831406095428353 47581537276373554571571265)
          ·
            refine ⟨35686152957280165928678449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47581537276373554571571265 35686152957280165928678449)
            ·
              refine ⟨26764614717960124446508837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35686152957280165928678449 26764614717960124446508837)
              ·
                refine ⟨5018365259617523333720407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26764614717960124446508837 5018365259617523333720407)
                ·
                  refine ⟨7527547889426285000580611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5018365259617523333720407 7527547889426285000580611)
                  ·
                    refine ⟨11291321834139427500870917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7527547889426285000580611 11291321834139427500870917)
                    ·
                      refine ⟨2117122843901142656413297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11291321834139427500870917 2117122843901142656413297)
                      ·
                        rfl

theorem cell23_4123082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_4123082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123082 prefixEnd_4123082 := by exact prefixLift 4123082
  have htrace : WordTrace (prefixWord ++ tailWord_4123082) baseStart_4123082 baseEnd_4123082 := by
    simpa [prefixWord, tailWord_4123082, baseEnd_4123082] using wordTrace_append hprefix tailTrace_4123082
  have hstable : (prefixWord ++ tailWord_4123082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123082).length < 2 ^ (prefixWord ++ tailWord_4123082).sum := by decide
  have hdescent : baseEnd_4123082 < baseStart_4123082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123092 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_4123092 : Nat := 118140960795 + 4123092 * 2 ^ 59
def prefixEnd_4123092 : Nat := 4983230072969 + 3 ^ 40 * 4123092 * 2
def baseEnd_4123092 : Nat := 705709326235895872429417

theorem tailTrace_4123092 : CollatzResearch.WordTrace tailWord_4123092 prefixEnd_4123092 705709326235895872429417 := by
  unfold tailWord_4123092
  simp only [CollatzResearch.WordTrace]
  refine ⟨75190759789374663448513765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100254346385832884598018353 75190759789374663448513765)
  ·
    refine ⟨14098267460507749396596331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75190759789374663448513765 14098267460507749396596331)
    ·
      refine ⟨21147401190761624094894497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14098267460507749396596331 21147401190761624094894497)
      ·
        refine ⟨15860550893071218071170873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21147401190761624094894497 15860550893071218071170873)
        ·
          refine ⟨11895413169803413553378155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15860550893071218071170873 11895413169803413553378155)
          ·
            refine ⟨17843119754705120330067233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11895413169803413553378155 17843119754705120330067233)
            ·
              refine ⟨13382339816028840247550425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17843119754705120330067233 13382339816028840247550425)
              ·
                refine ⟨10036754862021630185662819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13382339816028840247550425 10036754862021630185662819)
                ·
                  refine ⟨15055132293032445278494229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10036754862021630185662819 15055132293032445278494229)
                  ·
                    refine ⟨705709326235895872429417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15055132293032445278494229 705709326235895872429417)
                    ·
                      rfl

theorem cell23_4123092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_4123092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123092 prefixEnd_4123092 := by exact prefixLift 4123092
  have htrace : WordTrace (prefixWord ++ tailWord_4123092) baseStart_4123092 baseEnd_4123092 := by
    simpa [prefixWord, tailWord_4123092, baseEnd_4123092] using wordTrace_append hprefix tailTrace_4123092
  have hstable : (prefixWord ++ tailWord_4123092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123092).length < 2 ^ (prefixWord ++ tailWord_4123092).sum := by decide
  have hdescent : baseEnd_4123092 < baseStart_4123092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123109 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_4123109 : Nat := 118140960795 + 4123109 * 2 ^ 59
def prefixEnd_4123109 : Nat := 4983230072969 + 3 ^ 40 * 4123109 * 2
def baseEnd_4123109 : Nat := 705712235959604683591891

theorem tailTrace_4123109 : CollatzResearch.WordTrace tailWord_4123109 prefixEnd_4123109 705712235959604683591891 := by
  unfold tailWord_4123109
  simp only [CollatzResearch.WordTrace]
  refine ⟨150382139619687738800396381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100254759746458492533597587 150382139619687738800396381)
  ·
    refine ⟨56393302357382902050148643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150382139619687738800396381 56393302357382902050148643)
    ·
      refine ⟨84589953536074353075222965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56393302357382902050148643 84589953536074353075222965)
      ·
        refine ⟨7930308144006970600802153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84589953536074353075222965 7930308144006970600802153)
        ·
          refine ⟨5947731108005227950601615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7930308144006970600802153 5947731108005227950601615)
          ·
            refine ⟨8921596662007841925902423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947731108005227950601615 8921596662007841925902423)
            ·
              refine ⟨13382394993011762888853635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921596662007841925902423 13382394993011762888853635)
              ·
                refine ⟨20073592489517644333280453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13382394993011762888853635 20073592489517644333280453)
                ·
                  refine ⟨3763798591784558312490085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20073592489517644333280453 3763798591784558312490085)
                  ·
                    refine ⟨705712235959604683591891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763798591784558312490085 705712235959604683591891)
                    ·
                      rfl

theorem cell23_4123109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_4123109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123109 prefixEnd_4123109 := by exact prefixLift 4123109
  have htrace : WordTrace (prefixWord ++ tailWord_4123109) baseStart_4123109 baseEnd_4123109 := by
    simpa [prefixWord, tailWord_4123109, baseEnd_4123109] using wordTrace_append hprefix tailTrace_4123109
  have hstable : (prefixWord ++ tailWord_4123109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123109).length < 2 ^ (prefixWord ++ tailWord_4123109).sum := by decide
  have hdescent : baseEnd_4123109 < baseStart_4123109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123116 : List Nat := [2, 2, 1, 1, 2, 1, 3, 6, 1, 2, 2]
def baseStart_4123116 : Nat := 118140960795 + 4123116 * 2 ^ 59
def prefixEnd_4123116 : Nat := 4983230072969 + 3 ^ 40 * 4123116 * 2
def baseEnd_4123116 : Nat := 2117140302243395523388141

theorem tailTrace_4123116 : CollatzResearch.WordTrace tailWord_4123116 prefixEnd_4123116 2117140302243395523388141 := by
  unfold tailWord_4123116
  simp only [CollatzResearch.WordTrace]
  refine ⟨75191197465331189497950601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100254929953774919330600801 75191197465331189497950601)
  ·
    refine ⟨56393398098998392123462951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75191197465331189497950601 56393398098998392123462951)
    ·
      refine ⟨84590097148497588185194427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56393398098998392123462951 84590097148497588185194427)
      ·
        refine ⟨126885145722746382277791641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84590097148497588185194427 126885145722746382277791641)
        ·
          refine ⟨95163859292059786708343731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126885145722746382277791641 95163859292059786708343731)
          ·
            refine ⟨142745788938089680062515597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95163859292059786708343731 142745788938089680062515597)
            ·
              refine ⟨53529670851783630023443349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142745788938089680062515597 53529670851783630023443349)
              ·
                refine ⟨2509203321177357657348907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53529670851783630023443349 2509203321177357657348907)
                ·
                  refine ⟨3763804981766036486023361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509203321177357657348907 3763804981766036486023361)
                  ·
                    refine ⟨2822853736324527364517521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3763804981766036486023361 2822853736324527364517521)
                    ·
                      refine ⟨2117140302243395523388141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822853736324527364517521 2117140302243395523388141)
                      ·
                        rfl

theorem cell23_4123116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 1, 2, 2].length) (baseStart_4123116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123116 prefixEnd_4123116 := by exact prefixLift 4123116
  have htrace : WordTrace (prefixWord ++ tailWord_4123116) baseStart_4123116 baseEnd_4123116 := by
    simpa [prefixWord, tailWord_4123116, baseEnd_4123116] using wordTrace_append hprefix tailTrace_4123116
  have hstable : (prefixWord ++ tailWord_4123116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123116).length < 2 ^ (prefixWord ++ tailWord_4123116).sum := by decide
  have hdescent : baseEnd_4123116 < baseStart_4123116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123126 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_4123126 : Nat := 118140960795 + 4123126 * 2 ^ 59
def prefixEnd_4123126 : Nat := 4983230072969 + 3 ^ 40 * 4123126 * 2
def baseEnd_4123126 : Nat := 705715145683313494754365

theorem tailTrace_4123126 : CollatzResearch.WordTrace tailWord_4123126 prefixEnd_4123126 705715145683313494754365 := by
  unfold tailWord_4123126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9398922478789134418985327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100255173107084100469176821 9398922478789134418985327)
  ·
    refine ⟨14098383718183701628477991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9398922478789134418985327 14098383718183701628477991)
    ·
      refine ⟨21147575577275552442716987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14098383718183701628477991 21147575577275552442716987)
      ·
        refine ⟨31721363365913328664075481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21147575577275552442716987 31721363365913328664075481)
        ·
          refine ⟨23791022524434996498056611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31721363365913328664075481 23791022524434996498056611)
          ·
            refine ⟨35686533786652494747084917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23791022524434996498056611 35686533786652494747084917)
            ·
              refine ⟨3345612542498671382539211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35686533786652494747084917 3345612542498671382539211)
              ·
                refine ⟨5018418813748007073808817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345612542498671382539211 5018418813748007073808817)
                ·
                  refine ⟨3763814110311005305356613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5018418813748007073808817 3763814110311005305356613)
                  ·
                    refine ⟨705715145683313494754365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763814110311005305356613 705715145683313494754365)
                    ·
                      rfl

theorem cell23_4123126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_4123126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123126 prefixEnd_4123126 := by exact prefixLift 4123126
  have htrace : WordTrace (prefixWord ++ tailWord_4123126) baseStart_4123126 baseEnd_4123126 := by
    simpa [prefixWord, tailWord_4123126, baseEnd_4123126] using wordTrace_append hprefix tailTrace_4123126
  have hstable : (prefixWord ++ tailWord_4123126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123126).length < 2 ^ (prefixWord ++ tailWord_4123126).sum := by decide
  have hdescent : baseEnd_4123126 < baseStart_4123126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123150 : List Nat := [4, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2]
def baseStart_4123150 : Nat := 118140960795 + 4123150 * 2 ^ 59
def prefixEnd_4123150 : Nat := 4983230072969 + 3 ^ 40 * 4123150 * 2
def baseEnd_4123150 : Nat := 2117157760585648390362985

theorem tailTrace_4123150 : CollatzResearch.WordTrace tailWord_4123150 prefixEnd_4123150 2117157760585648390362985 := by
  unfold tailWord_4123150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18797954376567400350329863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100255756675026135201759269 18797954376567400350329863)
  ·
    refine ⟨28196931564851100525494795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18797954376567400350329863 28196931564851100525494795)
    ·
      refine ⟨42295397347276650788242193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28196931564851100525494795 42295397347276650788242193)
      ·
        refine ⟨31721548010457488091181645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42295397347276650788242193 31721548010457488091181645)
        ·
          refine ⟨11895580503921558034193117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31721548010457488091181645 11895580503921558034193117)
          ·
            refine ⟨4460842688970584262822419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11895580503921558034193117 4460842688970584262822419)
            ·
              refine ⟨6691264033455876394233629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4460842688970584262822419 6691264033455876394233629)
              ·
                refine ⟨2509224012545953647837611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6691264033455876394233629 2509224012545953647837611)
                ·
                  refine ⟨3763836018818930471756417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509224012545953647837611 3763836018818930471756417)
                  ·
                    refine ⟨2822877014114197853817313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3763836018818930471756417 2822877014114197853817313)
                    ·
                      refine ⟨2117157760585648390362985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822877014114197853817313 2117157760585648390362985)
                      ·
                        rfl

theorem cell23_4123150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_4123150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123150 prefixEnd_4123150 := by exact prefixLift 4123150
  have htrace : WordTrace (prefixWord ++ tailWord_4123150) baseStart_4123150 baseEnd_4123150 := by
    simpa [prefixWord, tailWord_4123150, baseEnd_4123150] using wordTrace_append hprefix tailTrace_4123150
  have hstable : (prefixWord ++ tailWord_4123150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123150).length < 2 ^ (prefixWord ++ tailWord_4123150).sum := by decide
  have hdescent : baseEnd_4123150 < baseStart_4123150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123189 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_4123189 : Nat := 118140960795 + 4123189 * 2 ^ 59
def prefixEnd_4123189 : Nat := 4983230072969 + 3 ^ 40 * 4123189 * 2
def baseEnd_4123189 : Nat := 2117177786331173737775305

theorem tailTrace_4123189 : CollatzResearch.WordTrace tailWord_4123189 prefixEnd_4123189 2117177786331173737775305 := by
  unfold tailWord_4123189
  simp only [CollatzResearch.WordTrace]
  refine ⟨150385057459397912463308621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100256704972931941642205747 150385057459397912463308621)
  ·
    refine ⟨56394396547274217173740733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150385057459397912463308621 56394396547274217173740733)
    ·
      refine ⟨21147898705227831440152775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56394396547274217173740733 21147898705227831440152775)
      ·
        refine ⟨31721848057841747160229163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21147898705227831440152775 31721848057841747160229163)
        ·
          refine ⟨47582772086762620740343745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31721848057841747160229163 47582772086762620740343745)
          ·
            refine ⟨35687079065071965555257809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47582772086762620740343745 35687079065071965555257809)
            ·
              refine ⟨26765309298803974166443357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35687079065071965555257809 26765309298803974166443357)
              ·
                refine ⟨10036990987051490312416259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26765309298803974166443357 10036990987051490312416259)
                ·
                  refine ⟨15055486480577235468624389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10036990987051490312416259 15055486480577235468624389)
                  ·
                    refine ⟨2822903715108231650367073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15055486480577235468624389 2822903715108231650367073)
                    ·
                      refine ⟨2117177786331173737775305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2822903715108231650367073 2117177786331173737775305)
                      ·
                        rfl

theorem cell23_4123189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_4123189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123189 prefixEnd_4123189 := by exact prefixLift 4123189
  have htrace : WordTrace (prefixWord ++ tailWord_4123189) baseStart_4123189 baseEnd_4123189 := by
    simpa [prefixWord, tailWord_4123189, baseEnd_4123189] using wordTrace_append hprefix tailTrace_4123189
  have hstable : (prefixWord ++ tailWord_4123189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123189).length < 2 ^ (prefixWord ++ tailWord_4123189).sum := by decide
  have hdescent : baseEnd_4123189 < baseStart_4123189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123225 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 5, 7]
def baseStart_4123225 : Nat := 118140960795 + 4123225 * 2 ^ 59
def prefixEnd_4123225 : Nat := 4983230072969 + 3 ^ 40 * 4123225 * 2
def baseEnd_4123225 : Nat := 705732090544911865641713

theorem tailTrace_4123225 : CollatzResearch.WordTrace tailWord_4123225 prefixEnd_4123225 705732090544911865641713 := by
  unfold tailWord_4123225
  simp only [CollatzResearch.WordTrace]
  refine ⟨150386370487267490611619129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100257580324844993741079419 150386370487267490611619129)
  ·
    refine ⟨112789777865450617958714347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150386370487267490611619129 112789777865450617958714347)
    ·
      refine ⟨169184666798175926938071521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112789777865450617958714347 169184666798175926938071521)
      ·
        refine ⟨126888500098631945203553641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169184666798175926938071521 126888500098631945203553641)
        ·
          refine ⟨95166375073973958902665231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126888500098631945203553641 95166375073973958902665231)
          ·
            refine ⟨142749562610960938353997847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95166375073973958902665231 142749562610960938353997847)
            ·
              refine ⟨214124343916441407530996771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142749562610960938353997847 214124343916441407530996771)
              ·
                refine ⟨321186515874662111296495157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214124343916441407530996771 321186515874662111296495157)
                ·
                  refine ⟨30111235863249572934046421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321186515874662111296495157 30111235863249572934046421)
                  ·
                    refine ⟨705732090544911865641713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30111235863249572934046421 705732090544911865641713)
                    ·
                      rfl

theorem cell23_4123225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_4123225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123225 prefixEnd_4123225 := by exact prefixLift 4123225
  have htrace : WordTrace (prefixWord ++ tailWord_4123225) baseStart_4123225 baseEnd_4123225 := by
    simpa [prefixWord, tailWord_4123225, baseEnd_4123225] using wordTrace_append hprefix tailTrace_4123225
  have hstable : (prefixWord ++ tailWord_4123225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123225).length < 2 ^ (prefixWord ++ tailWord_4123225).sum := by decide
  have hdescent : baseEnd_4123225 < baseStart_4123225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123242 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_4123242 : Nat := 118140960795 + 4123242 * 2 ^ 59
def prefixEnd_4123242 : Nat := 4983230072969 + 3 ^ 40 * 4123242 * 2
def baseEnd_4123242 : Nat := 705735000268620676804187

theorem tailTrace_4123242 : CollatzResearch.WordTrace tailWord_4123242 prefixEnd_4123242 705735000268620676804187 := by
  unfold tailWord_4123242
  simp only [CollatzResearch.WordTrace]
  refine ⟨37596747632051475628746995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100257993685470601676658653 37596747632051475628746995)
  ·
    refine ⟨56395121448077213443120493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37596747632051475628746995 56395121448077213443120493)
    ·
      refine ⟨21148170543028955041170185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56395121448077213443120493 21148170543028955041170185)
      ·
        refine ⟨15861127907271716280877639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21148170543028955041170185 15861127907271716280877639)
        ·
          refine ⟨23791691860907574421316459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15861127907271716280877639 23791691860907574421316459)
          ·
            refine ⟨35687537791361361631974689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23791691860907574421316459 35687537791361361631974689)
            ·
              refine ⟨26765653343521021223981017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35687537791361361631974689 26765653343521021223981017)
              ·
                refine ⟨20074240007640765917985763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26765653343521021223981017 20074240007640765917985763)
                ·
                  refine ⟨30111360011461148876978645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20074240007640765917985763 30111360011461148876978645)
                  ·
                    refine ⟨705735000268620676804187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30111360011461148876978645 705735000268620676804187)
                    ·
                      rfl

theorem cell23_4123242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_4123242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123242 prefixEnd_4123242 := by exact prefixLift 4123242
  have htrace : WordTrace (prefixWord ++ tailWord_4123242) baseStart_4123242 baseEnd_4123242 := by
    simpa [prefixWord, tailWord_4123242, baseEnd_4123242] using wordTrace_append hprefix tailTrace_4123242
  have hstable : (prefixWord ++ tailWord_4123242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123242).length < 2 ^ (prefixWord ++ tailWord_4123242).sum := by decide
  have hdescent : baseEnd_4123242 < baseStart_4123242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123289 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 3, 4]
def baseStart_4123289 : Nat := 118140960795 + 4123289 * 2 ^ 59
def prefixEnd_4123289 : Nat := 4983230072969 + 3 ^ 40 * 4123289 * 2
def baseEnd_4123289 : Nat := 705743044798874448841615

theorem tailTrace_4123289 : CollatzResearch.WordTrace tailWord_4123289 prefixEnd_4123289 705743044798874448841615 := by
  unfold tailWord_4123289
  simp only [CollatzResearch.WordTrace]
  refine ⟨150388704759035629541948921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100259136506023753027965947 150388704759035629541948921)
  ·
    refine ⟨112791528569276722156461691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150388704759035629541948921 112791528569276722156461691)
    ·
      refine ⟨169187292853915083234692537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112791528569276722156461691 169187292853915083234692537)
      ·
        refine ⟨126890469640436312426019403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169187292853915083234692537 126890469640436312426019403)
        ·
          refine ⟨190335704460654468639029105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126890469640436312426019403 190335704460654468639029105)
          ·
            refine ⟨142751778345490851479271829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190335704460654468639029105 142751778345490851479271829)
            ·
              refine ⟨6691489609944883663090867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142751778345490851479271829 6691489609944883663090867)
              ·
                refine ⟨10037234414917325494636301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691489609944883663090867 10037234414917325494636301)
                ·
                  refine ⟨3763962905593997060488613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10037234414917325494636301 3763962905593997060488613)
                  ·
                    refine ⟨705743044798874448841615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763962905593997060488613 705743044798874448841615)
                    ·
                      rfl

theorem cell23_4123289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 4].length) (baseStart_4123289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123289 prefixEnd_4123289 := by exact prefixLift 4123289
  have htrace : WordTrace (prefixWord ++ tailWord_4123289) baseStart_4123289 baseEnd_4123289 := by
    simpa [prefixWord, tailWord_4123289, baseEnd_4123289] using wordTrace_append hprefix tailTrace_4123289
  have hstable : (prefixWord ++ tailWord_4123289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123289).length < 2 ^ (prefixWord ++ tailWord_4123289).sum := by decide
  have hdescent : baseEnd_4123289 < baseStart_4123289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123312 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 3]
def baseStart_4123312 : Nat := 118140960795 + 4123312 * 2 ^ 59
def prefixEnd_4123312 : Nat := 4983230072969 + 3 ^ 40 * 4123312 * 2
def baseEnd_4123312 : Nat := 2117240944451676756537239

theorem tailTrace_4123312 : CollatzResearch.WordTrace tailWord_4123312 prefixEnd_4123312 2117240944451676756537239 := by
  unfold tailWord_4123312
  simp only [CollatzResearch.WordTrace]
  refine ⟨75194771818976152235018095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100259695758634869646690793 75194771818976152235018095)
  ·
    refine ⟨112792157728464228352527143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75194771818976152235018095 112792157728464228352527143)
    ·
      refine ⟨169188236592696342528790715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112792157728464228352527143 169188236592696342528790715)
      ·
        refine ⟨253782354889044513793186073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169188236592696342528790715 253782354889044513793186073)
        ·
          refine ⟨190336766166783385344889555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253782354889044513793186073 190336766166783385344889555)
          ·
            refine ⟨285505149250175078017334333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190336766166783385344889555 285505149250175078017334333)
            ·
              refine ⟨107064430968815654256500375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285505149250175078017334333 107064430968815654256500375)
              ·
                refine ⟨160596646453223481384750563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107064430968815654256500375 160596646453223481384750563)
                ·
                  refine ⟨240894969679835222077125845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160596646453223481384750563 240894969679835222077125845)
                  ·
                    refine ⟨5645975851871138017432637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 240894969679835222077125845 5645975851871138017432637)
                    ·
                      refine ⟨2117240944451676756537239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5645975851871138017432637 2117240944451676756537239)
                      ·
                        rfl

theorem cell23_4123312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 3].length) (baseStart_4123312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123312 prefixEnd_4123312 := by exact prefixLift 4123312
  have htrace : WordTrace (prefixWord ++ tailWord_4123312) baseStart_4123312 baseEnd_4123312 := by
    simpa [prefixWord, tailWord_4123312, baseEnd_4123312] using wordTrace_append hprefix tailTrace_4123312
  have hstable : (prefixWord ++ tailWord_4123312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123312).length < 2 ^ (prefixWord ++ tailWord_4123312).sum := by decide
  have hdescent : baseEnd_4123312 < baseStart_4123312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123340 : List Nat := [2, 2, 1, 5, 1, 2, 3, 2, 1, 4]
def baseStart_4123340 : Nat := 118140960795 + 4123340 * 2 ^ 59
def prefixEnd_4123340 : Nat := 4983230072969 + 3 ^ 40 * 4123340 * 2
def baseEnd_4123340 : Nat := 705751773970000882329037

theorem tailTrace_4123340 : CollatzResearch.WordTrace tailWord_4123340 prefixEnd_4123340 705751773970000882329037 := by
  unfold tailWord_4123340
  simp only [CollatzResearch.WordTrace]
  refine ⟨75195282440925432626027737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100260376587900576834703649 75195282440925432626027737)
  ·
    refine ⟨56396461830694074469520803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75195282440925432626027737 56396461830694074469520803)
    ·
      refine ⟨84594692746041111704281205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56396461830694074469520803 84594692746041111704281205)
      ·
        refine ⟨7930752444941354222276363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84594692746041111704281205 7930752444941354222276363)
        ·
          refine ⟨11896128667412031333414545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7930752444941354222276363 11896128667412031333414545)
          ·
            refine ⟨8922096500559023500060909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11896128667412031333414545 8922096500559023500060909)
            ·
              refine ⟨3345786187709633812522841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8922096500559023500060909 3345786187709633812522841)
              ·
                refine ⟨2509339640782225359392131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3345786187709633812522841 2509339640782225359392131)
                ·
                  refine ⟨3764009461173338039088197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509339640782225359392131 3764009461173338039088197)
                  ·
                    refine ⟨705751773970000882329037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3764009461173338039088197 705751773970000882329037)
                    ·
                      rfl

theorem cell23_4123340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_4123340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123340 prefixEnd_4123340 := by exact prefixLift 4123340
  have htrace : WordTrace (prefixWord ++ tailWord_4123340) baseStart_4123340 baseEnd_4123340 := by
    simpa [prefixWord, tailWord_4123340, baseEnd_4123340] using wordTrace_append hprefix tailTrace_4123340
  have hstable : (prefixWord ++ tailWord_4123340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123340).length < 2 ^ (prefixWord ++ tailWord_4123340).sum := by decide
  have hdescent : baseEnd_4123340 < baseStart_4123340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123369 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 2, 6, 2]
def baseStart_4123369 : Nat := 118140960795 + 4123369 * 2 ^ 59
def prefixEnd_4123369 : Nat := 4983230072969 + 3 ^ 40 * 4123369 * 2
def baseEnd_4123369 : Nat := 2117270212848983033524477

theorem tailTrace_4123369 : CollatzResearch.WordTrace tailWord_4123369 prefixEnd_4123369 2117270212848983033524477 := by
  unfold tailWord_4123369
  simp only [CollatzResearch.WordTrace]
  refine ⟨150391622598745803204861161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100261081732497202136574107 150391622598745803204861161)
  ·
    refine ⟨112793716949059352403645871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150391622598745803204861161 112793716949059352403645871)
    ·
      refine ⟨169190575423589028605468807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112793716949059352403645871 169190575423589028605468807)
      ·
        refine ⟨253785863135383542908203211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169190575423589028605468807 253785863135383542908203211)
        ·
          refine ⟨380678794703075314362304817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253785863135383542908203211 380678794703075314362304817)
          ·
            refine ⟨285509096027306485771728613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380678794703075314362304817 285509096027306485771728613)
            ·
              refine ⟨53532955505119966082199115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285509096027306485771728613 53532955505119966082199115)
              ·
                refine ⟨80299433257679949123298673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53532955505119966082199115 80299433257679949123298673)
                ·
                  refine ⟨60224574943259961842474005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80299433257679949123298673 60224574943259961842474005)
                  ·
                    refine ⟨2823026950465310711365969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60224574943259961842474005 2823026950465310711365969)
                    ·
                      refine ⟨2117270212848983033524477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823026950465310711365969 2117270212848983033524477)
                      ·
                        rfl

theorem cell23_4123369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 6, 2].length) (baseStart_4123369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123369 prefixEnd_4123369 := by exact prefixLift 4123369
  have htrace : WordTrace (prefixWord ++ tailWord_4123369) baseStart_4123369 baseEnd_4123369 := by
    simpa [prefixWord, tailWord_4123369, baseEnd_4123369] using wordTrace_append hprefix tailTrace_4123369
  have hstable : (prefixWord ++ tailWord_4123369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123369).length < 2 ^ (prefixWord ++ tailWord_4123369).sum := by decide
  have hdescent : baseEnd_4123369 < baseStart_4123369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123373 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_4123373 : Nat := 118140960795 + 4123373 * 2 ^ 59
def prefixEnd_4123373 : Nat := 4983230072969 + 3 ^ 40 * 4123373 * 2
def baseEnd_4123373 : Nat := 2117272266771601017874459

theorem tailTrace_4123373 : CollatzResearch.WordTrace tailWord_4123373 prefixEnd_4123373 2117272266771601017874459 := by
  unfold tailWord_4123373
  simp only [CollatzResearch.WordTrace]
  refine ⟨150391768490731311888006773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100261178993820874592004515 150391768490731311888006773)
  ·
    refine ⟨14099228296006060489500635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150391768490731311888006773 14099228296006060489500635)
    ·
      refine ⟨21148842444009090734250953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14099228296006060489500635 21148842444009090734250953)
      ·
        refine ⟨15861631833006818050688215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21148842444009090734250953 15861631833006818050688215)
        ·
          refine ⟨23792447749510227076032323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15861631833006818050688215 23792447749510227076032323)
          ·
            refine ⟨35688671624265340614048485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23792447749510227076032323 35688671624265340614048485)
            ·
              refine ⟨6691625929549751365134091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35688671624265340614048485 6691625929549751365134091)
              ·
                refine ⟨10037438894324627047701137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691625929549751365134091 10037438894324627047701137)
                ·
                  refine ⟨7528079170743470285775853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10037438894324627047701137 7528079170743470285775853)
                  ·
                    refine ⟨2823029689028801357165945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7528079170743470285775853 2823029689028801357165945)
                    ·
                      refine ⟨2117272266771601017874459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823029689028801357165945 2117272266771601017874459)
                      ·
                        rfl

theorem cell23_4123373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_4123373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123373 prefixEnd_4123373 := by exact prefixLift 4123373
  have htrace : WordTrace (prefixWord ++ tailWord_4123373) baseStart_4123373 baseEnd_4123373 := by
    simpa [prefixWord, tailWord_4123373, baseEnd_4123373] using wordTrace_append hprefix tailTrace_4123373
  have hstable : (prefixWord ++ tailWord_4123373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123373).length < 2 ^ (prefixWord ++ tailWord_4123373).sum := by decide
  have hdescent : baseEnd_4123373 < baseStart_4123373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123426 : List Nat := [3, 3, 1, 1, 2, 3, 3, 7]
def baseStart_4123426 : Nat := 118140960795 + 4123426 * 2 ^ 59
def prefixEnd_4123426 : Nat := 4983230072969 + 3 ^ 40 * 4123426 * 2
def baseEnd_4123426 : Nat := 78418499305418122611545

theorem tailTrace_4123426 : CollatzResearch.WordTrace tailWord_4123426 prefixEnd_4123426 78418499305418122611545 := by
  unfold tailWord_4123426
  simp only [CollatzResearch.WordTrace]
  refine ⟨37598425389884825484921533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100262467706359534626457421 37598425389884825484921533)
  ·
    refine ⟨14099409521206809556845575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37598425389884825484921533 14099409521206809556845575)
    ·
      refine ⟨21149114281810214335268363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14099409521206809556845575 21149114281810214335268363)
      ·
        refine ⟨31723671422715321502902545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21149114281810214335268363 31723671422715321502902545)
        ·
          refine ⟨23792753567036491127176909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31723671422715321502902545 23792753567036491127176909)
          ·
            refine ⟨8922282587638684172691341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23792753567036491127176909 8922282587638684172691341)
            ·
              refine ⟨3345855970364506564759253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8922282587638684172691341 3345855970364506564759253)
              ·
                refine ⟨78418499305418122611545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3345855970364506564759253 78418499305418122611545)
                ·
                  rfl

theorem cell23_4123426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 7].length) (baseStart_4123426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123426 prefixEnd_4123426 := by exact prefixLift 4123426
  have htrace : WordTrace (prefixWord ++ tailWord_4123426) baseStart_4123426 baseEnd_4123426 := by
    simpa [prefixWord, tailWord_4123426, baseEnd_4123426] using wordTrace_append hprefix tailTrace_4123426
  have hstable : (prefixWord ++ tailWord_4123426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123426).length < 2 ^ (prefixWord ++ tailWord_4123426).sum := by decide
  have hdescent : baseEnd_4123426 < baseStart_4123426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123436 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 3]
def baseStart_4123436 : Nat := 118140960795 + 4123436 * 2 ^ 59
def prefixEnd_4123436 : Nat := 4983230072969 + 3 ^ 40 * 4123436 * 2
def baseEnd_4123436 : Nat := 2117304616052834271386669

theorem tailTrace_4123436 : CollatzResearch.WordTrace tailWord_4123436 prefixEnd_4123436 2117304616052834271386669 := by
  unfold tailWord_4123436
  simp only [CollatzResearch.WordTrace]
  refine ⟨75197033144751536823775081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100262710859668715765033441 75197033144751536823775081)
  ·
    refine ⟨56397774858563652617831311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75197033144751536823775081 56397774858563652617831311)
    ·
      refine ⟨84596662287845478926746967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56397774858563652617831311 84596662287845478926746967)
      ·
        refine ⟨126894993431768218390120451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84596662287845478926746967 126894993431768218390120451)
        ·
          refine ⟨190342490147652327585180677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126894993431768218390120451 190342490147652327585180677)
          ·
            refine ⟨35689216902684811422221377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190342490147652327585180677 35689216902684811422221377)
            ·
              refine ⟨26766912677013608566666033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35689216902684811422221377 26766912677013608566666033)
              ·
                refine ⟨20075184507760206424999525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26766912677013608566666033 20075184507760206424999525)
                ·
                  refine ⟨3764097095205038704687411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20075184507760206424999525 3764097095205038704687411)
                  ·
                    refine ⟨5646145642807558057031117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3764097095205038704687411 5646145642807558057031117)
                    ·
                      refine ⟨2117304616052834271386669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5646145642807558057031117 2117304616052834271386669)
                      ·
                        rfl

theorem cell23_4123436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_4123436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123436 prefixEnd_4123436 := by exact prefixLift 4123436
  have htrace : WordTrace (prefixWord ++ tailWord_4123436) baseStart_4123436 baseEnd_4123436 := by
    simpa [prefixWord, tailWord_4123436, baseEnd_4123436] using wordTrace_append hprefix tailTrace_4123436
  have hstable : (prefixWord ++ tailWord_4123436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123436).length < 2 ^ (prefixWord ++ tailWord_4123436).sum := by decide
  have hdescent : baseEnd_4123436 < baseStart_4123436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123489 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_4123489 : Nat := 118140960795 + 4123489 * 2 ^ 59
def prefixEnd_4123489 : Nat := 4983230072969 + 3 ^ 40 * 4123489 * 2
def baseEnd_4123489 : Nat := 2117331830527522564023925

theorem tailTrace_4123489 : CollatzResearch.WordTrace tailWord_4123489 prefixEnd_4123489 2117331830527522564023925 := by
  unfold tailWord_4123489
  simp only [CollatzResearch.WordTrace]
  refine ⟨150395999358311063699229521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100263999572207375799486347 150395999358311063699229521)
  ·
    refine ⟨112796999518733297774422141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150395999358311063699229521 112796999518733297774422141)
    ·
      refine ⟨42298874819524986665408303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112796999518733297774422141 42298874819524986665408303)
      ·
        refine ⟨63448312229287479998112455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42298874819524986665408303 63448312229287479998112455)
        ·
          refine ⟨95172468343931219997168683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63448312229287479998112455 95172468343931219997168683)
          ·
            refine ⟨142758702515896829995753025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95172468343931219997168683 142758702515896829995753025)
            ·
              refine ⟨107069026886922622496814769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142758702515896829995753025 107069026886922622496814769)
              ·
                refine ⟨80301770165191966872611077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107069026886922622496814769 80301770165191966872611077)
                ·
                  refine ⟨15056581905973493788614577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80301770165191966872611077 15056581905973493788614577)
                  ·
                    refine ⟨11292436429480120341460933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15056581905973493788614577 11292436429480120341460933)
                    ·
                      refine ⟨2117331830527522564023925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11292436429480120341460933 2117331830527522564023925)
                      ·
                        rfl

theorem cell23_4123489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_4123489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123489 prefixEnd_4123489 := by exact prefixLift 4123489
  have htrace : WordTrace (prefixWord ++ tailWord_4123489) baseStart_4123489 baseEnd_4123489 := by
    simpa [prefixWord, tailWord_4123489, baseEnd_4123489] using wordTrace_append hprefix tailTrace_4123489
  have hstable : (prefixWord ++ tailWord_4123489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123489).length < 2 ^ (prefixWord ++ tailWord_4123489).sum := by decide
  have hdescent : baseEnd_4123489 < baseStart_4123489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123493 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 4, 2, 2]
def baseStart_4123493 : Nat := 118140960795 + 4123493 * 2 ^ 59
def prefixEnd_4123493 : Nat := 4983230072969 + 3 ^ 40 * 4123493 * 2
def baseEnd_4123493 : Nat := 2117333884450140548373907

theorem tailTrace_4123493 : CollatzResearch.WordTrace tailWord_4123493 prefixEnd_4123493 2117333884450140548373907 := by
  unfold tailWord_4123493
  simp only [CollatzResearch.WordTrace]
  refine ⟨150396145250296572382375133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100264096833531048254916755 150396145250296572382375133)
  ·
    refine ⟨56398554468861214643390675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150396145250296572382375133 56398554468861214643390675)
    ·
      refine ⟨84597831703291821965086013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56398554468861214643390675 84597831703291821965086013)
      ·
        refine ⟨31724186888734433236907255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84597831703291821965086013 31724186888734433236907255)
        ·
          refine ⟨47586280333101649855360883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31724186888734433236907255 47586280333101649855360883)
          ·
            refine ⟨71379420499652474783041325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47586280333101649855360883 71379420499652474783041325)
            ·
              refine ⟨26767282687369678043640497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71379420499652474783041325 26767282687369678043640497)
              ·
                refine ⟨20075462015527258532730373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26767282687369678043640497 20075462015527258532730373)
                ·
                  refine ⟨3764149127911360974886945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20075462015527258532730373 3764149127911360974886945)
                  ·
                    refine ⟨2823111845933520731165209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3764149127911360974886945 2823111845933520731165209)
                    ·
                      refine ⟨2117333884450140548373907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823111845933520731165209 2117333884450140548373907)
                      ·
                        rfl

theorem cell23_4123493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_4123493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123493 prefixEnd_4123493 := by exact prefixLift 4123493
  have htrace : WordTrace (prefixWord ++ tailWord_4123493) baseStart_4123493 baseEnd_4123493 := by
    simpa [prefixWord, tailWord_4123493, baseEnd_4123493] using wordTrace_append hprefix tailTrace_4123493
  have hstable : (prefixWord ++ tailWord_4123493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123493).length < 2 ^ (prefixWord ++ tailWord_4123493).sum := by decide
  have hdescent : baseEnd_4123493 < baseStart_4123493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123496 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4123496 : Nat := 118140960795 + 4123496 * 2 ^ 59
def prefixEnd_4123496 : Nat := 4983230072969 + 3 ^ 40 * 4123496 * 2
def baseEnd_4123496 : Nat := 2117335424892104036636393

theorem tailTrace_4123496 : CollatzResearch.WordTrace tailWord_4123496 prefixEnd_4123496 2117335424892104036636393 := by
  unfold tailWord_4123496
  simp only [CollatzResearch.WordTrace]
  refine ⟨75198127334642851947367171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100264169779523802596489561 75198127334642851947367171)
  ·
    refine ⟨112797191001964277921050757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75198127334642851947367171 112797191001964277921050757)
    ·
      refine ⟨21149473312868302110197017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112797191001964277921050757 21149473312868302110197017)
      ·
        refine ⟨15862104984651226582647763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21149473312868302110197017 15862104984651226582647763)
        ·
          refine ⟨23793157476976839873971645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15862104984651226582647763 23793157476976839873971645)
          ·
            refine ⟨8922434053866314952739367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23793157476976839873971645 8922434053866314952739367)
            ·
              refine ⟨13383651080799472429109051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922434053866314952739367 13383651080799472429109051)
              ·
                refine ⟨20075476621199208643663577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13383651080799472429109051 20075476621199208643663577)
                ·
                  refine ⟨15056607465899406482747683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20075476621199208643663577 15056607465899406482747683)
                  ·
                    refine ⟨22584911198849109724121525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15056607465899406482747683 22584911198849109724121525)
                    ·
                      refine ⟨2117335424892104036636393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22584911198849109724121525 2117335424892104036636393)
                      ·
                        rfl

theorem cell23_4123496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4123496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123496 prefixEnd_4123496 := by exact prefixLift 4123496
  have htrace : WordTrace (prefixWord ++ tailWord_4123496) baseStart_4123496 baseEnd_4123496 := by
    simpa [prefixWord, tailWord_4123496, baseEnd_4123496] using wordTrace_append hprefix tailTrace_4123496
  have hstable : (prefixWord ++ tailWord_4123496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123496).length < 2 ^ (prefixWord ++ tailWord_4123496).sum := by decide
  have hdescent : baseEnd_4123496 < baseStart_4123496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123516 : List Nat := [2, 2, 2, 1, 1, 1, 1, 8, 5]
def baseStart_4123516 : Nat := 118140960795 + 4123516 * 2 ^ 59
def prefixEnd_4123516 : Nat := 4983230072969 + 3 ^ 40 * 4123516 * 2
def baseEnd_4123516 : Nat := 235260632722799328709589

theorem tailTrace_4123516 : CollatzResearch.WordTrace tailWord_4123516 prefixEnd_4123516 235260632722799328709589 := by
  unfold tailWord_4123516
  simp only [CollatzResearch.WordTrace]
  refine ⟨75198492064606623655231201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100264656086142164873641601 75198492064606623655231201)
  ·
    refine ⟨56398869048454967741423401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75198492064606623655231201 56398869048454967741423401)
    ·
      refine ⟨42299151786341225806067551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56398869048454967741423401 42299151786341225806067551)
      ·
        refine ⟨63448727679511838709101327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42299151786341225806067551 63448727679511838709101327)
        ·
          refine ⟨95173091519267758063651991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63448727679511838709101327 95173091519267758063651991)
          ·
            refine ⟨142759637278901637095477987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95173091519267758063651991 142759637278901637095477987)
            ·
              refine ⟨214139455918352455643216981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142759637278901637095477987 214139455918352455643216981)
              ·
                refine ⟨2509446749043192839568949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 214139455918352455643216981 2509446749043192839568949)
                ·
                  refine ⟨235260632722799328709589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2509446749043192839568949 235260632722799328709589)
                  ·
                    rfl

theorem cell23_4123516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_4123516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123516 prefixEnd_4123516 := by exact prefixLift 4123516
  have htrace : WordTrace (prefixWord ++ tailWord_4123516) baseStart_4123516 baseEnd_4123516 := by
    simpa [prefixWord, tailWord_4123516, baseEnd_4123516] using wordTrace_append hprefix tailTrace_4123516
  have hstable : (prefixWord ++ tailWord_4123516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123516).length < 2 ^ (prefixWord ++ tailWord_4123516).sum := by decide
  have hdescent : baseEnd_4123516 < baseStart_4123516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123527 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 2, 2, 2]
def baseStart_4123527 : Nat := 118140960795 + 4123527 * 2 ^ 59
def prefixEnd_4123527 : Nat := 4983230072969 + 3 ^ 40 * 4123527 * 2
def baseEnd_4123527 : Nat := 2117351342792393415348751

theorem tailTrace_4123527 : CollatzResearch.WordTrace tailWord_4123527 prefixEnd_4123527 2117351342792393415348751 := by
  unfold tailWord_4123527
  simp only [CollatzResearch.WordTrace]
  refine ⟨150397385332173396189112835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100264923554782264126075223 150397385332173396189112835)
  ·
    refine ⟨225596077998260094283669253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150397385332173396189112835 225596077998260094283669253)
    ·
      refine ⟨42299264624673767678187985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225596077998260094283669253 42299264624673767678187985)
      ·
        refine ⟨31724448468505325758640989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42299264624673767678187985 31724448468505325758640989)
        ·
          refine ⟨11896668175689497159490371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31724448468505325758640989 11896668175689497159490371)
          ·
            refine ⟨17845002263534245739235557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11896668175689497159490371 17845002263534245739235557)
            ·
              refine ⟨3345937924412671076106667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17845002263534245739235557 3345937924412671076106667)
              ·
                refine ⟨5018906886619006614160001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345937924412671076106667 5018906886619006614160001)
                ·
                  refine ⟨3764180164964254960620001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5018906886619006614160001 3764180164964254960620001)
                  ·
                    refine ⟨2823135123723191220465001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3764180164964254960620001 2823135123723191220465001)
                    ·
                      refine ⟨2117351342792393415348751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823135123723191220465001 2117351342792393415348751)
                      ·
                        rfl

theorem cell23_4123527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_4123527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123527 prefixEnd_4123527 := by exact prefixLift 4123527
  have htrace : WordTrace (prefixWord ++ tailWord_4123527) baseStart_4123527 baseEnd_4123527 := by
    simpa [prefixWord, tailWord_4123527, baseEnd_4123527] using wordTrace_append hprefix tailTrace_4123527
  have hstable : (prefixWord ++ tailWord_4123527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123527).length < 2 ^ (prefixWord ++ tailWord_4123527).sum := by decide
  have hdescent : baseEnd_4123527 < baseStart_4123527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123597 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4123597 : Nat := 118140960795 + 4123597 * 2 ^ 59
def prefixEnd_4123597 : Nat := 4983230072969 + 3 ^ 40 * 4123597 * 2
def baseEnd_4123597 : Nat := 705795762146069380491143

theorem tailTrace_4123597 : CollatzResearch.WordTrace tailWord_4123597 prefixEnd_4123597 705795762146069380491143 := by
  unfold tailWord_4123597
  simp only [CollatzResearch.WordTrace]
  refine ⟨150399938441919798144161045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100266625627946532096107363 150399938441919798144161045)
  ·
    refine ⟨7049997114464990538007549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150399938441919798144161045 7049997114464990538007549)
    ·
      refine ⟨2643748917924371451752831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7049997114464990538007549 2643748917924371451752831)
      ·
        refine ⟨3965623376886557177629247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643748917924371451752831 3965623376886557177629247)
        ·
          refine ⟨5948435065329835766443871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3965623376886557177629247 5948435065329835766443871)
          ·
            refine ⟨8922652597994753649665807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948435065329835766443871 8922652597994753649665807)
            ·
              refine ⟨13383978896992130474498711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922652597994753649665807 13383978896992130474498711)
              ·
                refine ⟨20075968345488195711748067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13383978896992130474498711 20075968345488195711748067)
                ·
                  refine ⟨30113952518232293567622101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20075968345488195711748067 30113952518232293567622101)
                  ·
                    refine ⟨705795762146069380491143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30113952518232293567622101 705795762146069380491143)
                    ·
                      rfl

theorem cell23_4123597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4123597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123597 prefixEnd_4123597 := by exact prefixLift 4123597
  have htrace : WordTrace (prefixWord ++ tailWord_4123597) baseStart_4123597 baseEnd_4123597 := by
    simpa [prefixWord, tailWord_4123597, baseEnd_4123597] using wordTrace_append hprefix tailTrace_4123597
  have hstable : (prefixWord ++ tailWord_4123597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123597).length < 2 ^ (prefixWord ++ tailWord_4123597).sum := by decide
  have hdescent : baseEnd_4123597 < baseStart_4123597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123610 : List Nat := [3, 1, 1, 2, 4, 1, 1, 5, 1, 4]
def baseStart_4123610 : Nat := 118140960795 + 4123610 * 2 ^ 59
def prefixEnd_4123610 : Nat := 4983230072969 + 3 ^ 40 * 4123610 * 2
def baseEnd_4123610 : Nat := 705797987228905530203623

theorem tailTrace_4123610 : CollatzResearch.WordTrace tailWord_4123610 prefixEnd_4123610 705797987228905530203623 := by
  unfold tailWord_4123610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37600103147718175341096071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100266941727248467576256189 37600103147718175341096071)
  ·
    refine ⟨56400154721577263011644107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37600103147718175341096071 56400154721577263011644107)
    ·
      refine ⟨84600232082365894517466161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56400154721577263011644107 84600232082365894517466161)
      ·
        refine ⟨63450174061774420888099621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84600232082365894517466161 63450174061774420888099621)
        ·
          refine ⟨11896907636582703916518679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63450174061774420888099621 11896907636582703916518679)
          ·
            refine ⟨17845361454874055874778019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11896907636582703916518679 17845361454874055874778019)
            ·
              refine ⟨26768042182311083812167029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17845361454874055874778019 26768042182311083812167029)
              ·
                refine ⟨2509503954591664107390659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26768042182311083812167029 2509503954591664107390659)
                ·
                  refine ⟨3764255931887496161085989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509503954591664107390659 3764255931887496161085989)
                  ·
                    refine ⟨705797987228905530203623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3764255931887496161085989 705797987228905530203623)
                    ·
                      rfl

theorem cell23_4123610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_4123610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123610 prefixEnd_4123610 := by exact prefixLift 4123610
  have htrace : WordTrace (prefixWord ++ tailWord_4123610) baseStart_4123610 baseEnd_4123610 := by
    simpa [prefixWord, tailWord_4123610, baseEnd_4123610] using wordTrace_append hprefix tailTrace_4123610
  have hstable : (prefixWord ++ tailWord_4123610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123610).length < 2 ^ (prefixWord ++ tailWord_4123610).sum := by decide
  have hdescent : baseEnd_4123610 < baseStart_4123610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123623 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 6]
def baseStart_4123623 : Nat := 118140960795 + 4123623 * 2 ^ 59
def prefixEnd_4123623 : Nat := 4983230072969 + 3 ^ 40 * 4123623 * 2
def baseEnd_4123623 : Nat := 235266737437247226638701

theorem tailTrace_4123623 : CollatzResearch.WordTrace tailWord_4123623 prefixEnd_4123623 235266737437247226638701 := by
  unfold tailWord_4123623
  simp only [CollatzResearch.WordTrace]
  refine ⟨150400886739825604584607523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100267257826550403056405015 150400886739825604584607523)
  ·
    refine ⟨225601330109738406876911285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150400886739825604584607523 225601330109738406876911285)
    ·
      refine ⟨21150124697787975644710433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225601330109738406876911285 21150124697787975644710433)
      ·
        refine ⟨15862593523340981733532825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21150124697787975644710433 15862593523340981733532825)
        ·
          refine ⟨11896945142505736300149619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15862593523340981733532825 11896945142505736300149619)
          ·
            refine ⟨17845417713758604450224429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11896945142505736300149619 17845417713758604450224429)
            ·
              refine ⟨6692031642659476668834161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17845417713758604450224429 6692031642659476668834161)
              ·
                refine ⟨5019023731994607501625621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6692031642659476668834161 5019023731994607501625621)
                ·
                  refine ⟨235266737437247226638701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5019023731994607501625621 235266737437247226638701)
                  ·
                    rfl

theorem cell23_4123623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 6].length) (baseStart_4123623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123623 prefixEnd_4123623 := by exact prefixLift 4123623
  have htrace : WordTrace (prefixWord ++ tailWord_4123623) baseStart_4123623 baseEnd_4123623 := by
    simpa [prefixWord, tailWord_4123623, baseEnd_4123623] using wordTrace_append hprefix tailTrace_4123623
  have hstable : (prefixWord ++ tailWord_4123623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123623).length < 2 ^ (prefixWord ++ tailWord_4123623).sum := by decide
  have hdescent : baseEnd_4123623 < baseStart_4123623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123626 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_4123626 : Nat := 118140960795 + 4123626 * 2 ^ 59
def prefixEnd_4123626 : Nat := 4983230072969 + 3 ^ 40 * 4123626 * 2
def baseEnd_4123626 : Nat := 2117402177377188528010795

theorem tailTrace_4123626 : CollatzResearch.WordTrace tailWord_4123626 prefixEnd_4123626 2117402177377188528010795 := by
  unfold tailWord_4123626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37600249039703684024241683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100267330772543157397977821 37600249039703684024241683)
  ·
    refine ⟨56400373559555526036362525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37600249039703684024241683 56400373559555526036362525)
    ·
      refine ⟨21150140084833322263635947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56400373559555526036362525 21150140084833322263635947)
      ·
        refine ⟨31725210127249983395453921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21150140084833322263635947 31725210127249983395453921)
        ·
          refine ⟨23793907595437487546590441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31725210127249983395453921 23793907595437487546590441)
          ·
            refine ⟨17845430696578115659942831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23793907595437487546590441 17845430696578115659942831)
            ·
              refine ⟨26768146044867173489914247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17845430696578115659942831 26768146044867173489914247)
              ·
                refine ⟨40152219067300760234871371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26768146044867173489914247 40152219067300760234871371)
                ·
                  refine ⟨60228328600951140352307057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40152219067300760234871371 60228328600951140352307057)
                  ·
                    refine ⟨45171246450713355264230293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60228328600951140352307057 45171246450713355264230293)
                    ·
                      refine ⟨2117402177377188528010795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45171246450713355264230293 2117402177377188528010795)
                      ·
                        rfl

theorem cell23_4123626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_4123626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123626 prefixEnd_4123626 := by exact prefixLift 4123626
  have htrace : WordTrace (prefixWord ++ tailWord_4123626) baseStart_4123626 baseEnd_4123626 := by
    simpa [prefixWord, tailWord_4123626, baseEnd_4123626] using wordTrace_append hprefix tailTrace_4123626
  have hstable : (prefixWord ++ tailWord_4123626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123626).length < 2 ^ (prefixWord ++ tailWord_4123626).sum := by decide
  have hdescent : baseEnd_4123626 < baseStart_4123626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123653 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_4123653 : Nat := 118140960795 + 4123653 * 2 ^ 59
def prefixEnd_4123653 : Nat := 4983230072969 + 3 ^ 40 * 4123653 * 2
def baseEnd_4123653 : Nat := 705805347118286640791057

theorem tailTrace_4123653 : CollatzResearch.WordTrace tailWord_4123653 prefixEnd_4123653 705805347118286640791057 := by
  unfold tailWord_4123653
  simp only [CollatzResearch.WordTrace]
  refine ⟨150401980929716919708199613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100267987286477946472133075 150401980929716919708199613)
  ·
    refine ⟨56400742848643844890574855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150401980929716919708199613 56400742848643844890574855)
    ·
      refine ⟨84601114272965767335862283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56400742848643844890574855 84601114272965767335862283)
      ·
        refine ⟨126901671409448651003793425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84601114272965767335862283 126901671409448651003793425)
        ·
          refine ⟨95176253557086488252845069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126901671409448651003793425 95176253557086488252845069)
          ·
            refine ⟨35691095083907433094816901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95176253557086488252845069 35691095083907433094816901)
            ·
              refine ⟨6692080328232643705278169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35691095083907433094816901 6692080328232643705278169)
              ·
                refine ⟨5019060246174482778958627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6692080328232643705278169 5019060246174482778958627)
                ·
                  refine ⟨7528590369261724168437941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019060246174482778958627 7528590369261724168437941)
                  ·
                    refine ⟨705805347118286640791057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7528590369261724168437941 705805347118286640791057)
                    ·
                      rfl

theorem cell23_4123653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_4123653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123653 prefixEnd_4123653 := by exact prefixLift 4123653
  have htrace : WordTrace (prefixWord ++ tailWord_4123653) baseStart_4123653 baseEnd_4123653 := by
    simpa [prefixWord, tailWord_4123653, baseEnd_4123653] using wordTrace_append hprefix tailTrace_4123653
  have hstable : (prefixWord ++ tailWord_4123653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123653).length < 2 ^ (prefixWord ++ tailWord_4123653).sum := by decide
  have hdescent : baseEnd_4123653 < baseStart_4123653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123673 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 4]
def baseStart_4123673 : Nat := 118140960795 + 4123673 * 2 ^ 59
def prefixEnd_4123673 : Nat := 4983230072969 + 3 ^ 40 * 4123673 * 2
def baseEnd_4123673 : Nat := 2117426310967949844123079

theorem tailTrace_4123673 : CollatzResearch.WordTrace tailWord_4123673 prefixEnd_4123673 2117426310967949844123079 := by
  unfold tailWord_4123673
  simp only [CollatzResearch.WordTrace]
  refine ⟨150402710389644463123927673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100268473593096308749285115 150402710389644463123927673)
  ·
    refine ⟨112802032792233347342945755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150402710389644463123927673 112802032792233347342945755)
    ·
      refine ⟨169203049188350021014418633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112802032792233347342945755 169203049188350021014418633)
      ·
        refine ⟨126902286891262515760813975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169203049188350021014418633 126902286891262515760813975)
        ·
          refine ⟨190353430336893773641220963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126902286891262515760813975 190353430336893773641220963)
          ·
            refine ⟨285530145505340660461831445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190353430336893773641220963 285530145505340660461831445)
            ·
              refine ⟨13384225570562843459148349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 285530145505340660461831445 13384225570562843459148349)
              ·
                refine ⟨5019084588961066297180631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13384225570562843459148349 5019084588961066297180631)
                ·
                  refine ⟨7528626883441599445770947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019084588961066297180631 7528626883441599445770947)
                  ·
                    refine ⟨11292940325162399168656421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7528626883441599445770947 11292940325162399168656421)
                    ·
                      refine ⟨2117426310967949844123079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11292940325162399168656421 2117426310967949844123079)
                      ·
                        rfl

theorem cell23_4123673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_4123673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123673 prefixEnd_4123673 := by exact prefixLift 4123673
  have htrace : WordTrace (prefixWord ++ tailWord_4123673) baseStart_4123673 baseEnd_4123673 := by
    simpa [prefixWord, tailWord_4123673, baseEnd_4123673] using wordTrace_append hprefix tailTrace_4123673
  have hstable : (prefixWord ++ tailWord_4123673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123673).length < 2 ^ (prefixWord ++ tailWord_4123673).sum := by decide
  have hdescent : baseEnd_4123673 < baseStart_4123673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123677 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_4123677 : Nat := 118140960795 + 4123677 * 2 ^ 59
def prefixEnd_4123677 : Nat := 4983230072969 + 3 ^ 40 * 4123677 * 2
def baseEnd_4123677 : Nat := 2117428364890567828473061

theorem tailTrace_4123677 : CollatzResearch.WordTrace tailWord_4123677 prefixEnd_4123677 2117428364890567828473061 := by
  unfold tailWord_4123677
  simp only [CollatzResearch.WordTrace]
  refine ⟨150402856281629971807073285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100268570854419981204715523 150402856281629971807073285)
  ·
    refine ⟨28200535552805619713826241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150402856281629971807073285 28200535552805619713826241)
    ·
      refine ⟨21150401664604214785369681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28200535552805619713826241 21150401664604214785369681)
      ·
        refine ⟨15862801248453161089027261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21150401664604214785369681 15862801248453161089027261)
        ·
          refine ⟨5948550468169935408385223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15862801248453161089027261 5948550468169935408385223)
          ·
            refine ⟨8922825702254903112577835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948550468169935408385223 8922825702254903112577835)
            ·
              refine ⟨13384238553382354668866753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922825702254903112577835 13384238553382354668866753)
              ·
                refine ⟨10038178915036766001650065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13384238553382354668866753 10038178915036766001650065)
                ·
                  refine ⟨7528634186277574501237549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10038178915036766001650065 7528634186277574501237549)
                  ·
                    refine ⟨2823237819854090437964081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7528634186277574501237549 2823237819854090437964081)
                    ·
                      refine ⟨2117428364890567828473061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823237819854090437964081 2117428364890567828473061)
                      ·
                        rfl

theorem cell23_4123677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_4123677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123677 prefixEnd_4123677 := by exact prefixLift 4123677
  have htrace : WordTrace (prefixWord ++ tailWord_4123677) baseStart_4123677 baseEnd_4123677 := by
    simpa [prefixWord, tailWord_4123677, baseEnd_4123677] using wordTrace_append hprefix tailTrace_4123677
  have hstable : (prefixWord ++ tailWord_4123677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123677).length < 2 ^ (prefixWord ++ tailWord_4123677).sum := by decide
  have hdescent : baseEnd_4123677 < baseStart_4123677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123683 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 4, 4]
def baseStart_4123683 : Nat := 118140960795 + 4123683 * 2 ^ 59
def prefixEnd_4123683 : Nat := 4983230072969 + 3 ^ 40 * 4123683 * 2
def baseEnd_4123683 : Nat := 705810481924831601666011

theorem tailTrace_4123683 : CollatzResearch.WordTrace tailWord_4123683 prefixEnd_4123683 705810481924831601666011 := by
  unfold tailWord_4123683
  simp only [CollatzResearch.WordTrace]
  refine ⟨150403075119608234831791703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100268716746405489887861135 150403075119608234831791703)
  ·
    refine ⟨225604612679412352247687555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150403075119608234831791703 225604612679412352247687555)
    ·
      refine ⟨338406919019118528371531333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225604612679412352247687555 338406919019118528371531333)
      ·
        refine ⟨63451297316084724069662125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338406919019118528371531333 63451297316084724069662125)
        ·
          refine ⟨23794236493531771526123297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63451297316084724069662125 23794236493531771526123297)
          ·
            refine ⟨17845677370148828644592473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23794236493531771526123297 17845677370148828644592473)
            ·
              refine ⟨13384258027611621483444355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17845677370148828644592473 13384258027611621483444355)
              ·
                refine ⟨20076387041417432225166533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13384258027611621483444355 20076387041417432225166533)
                ·
                  refine ⟨3764322570265768542218725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20076387041417432225166533 3764322570265768542218725)
                  ·
                    refine ⟨705810481924831601666011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3764322570265768542218725 705810481924831601666011)
                    ·
                      rfl

theorem cell23_4123683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 4].length) (baseStart_4123683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123683 prefixEnd_4123683 := by exact prefixLift 4123683
  have htrace : WordTrace (prefixWord ++ tailWord_4123683) baseStart_4123683 baseEnd_4123683 := by
    simpa [prefixWord, tailWord_4123683, baseEnd_4123683] using wordTrace_append hprefix tailTrace_4123683
  have hstable : (prefixWord ++ tailWord_4123683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123683).length < 2 ^ (prefixWord ++ tailWord_4123683).sum := by decide
  have hdescent : baseEnd_4123683 < baseStart_4123683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123696 : List Nat := [2, 1, 1, 1, 2, 4, 4, 8]
def baseStart_4123696 : Nat := 118140960795 + 4123696 * 2 ^ 59
def prefixEnd_4123696 : Nat := 4983230072969 + 3 ^ 40 * 4123696 * 2
def baseEnd_4123696 : Nat := 78423634111963083486499

theorem tailTrace_4123696 : CollatzResearch.WordTrace tailWord_4123696 prefixEnd_4123696 78423634111963083486499 := by
  unfold tailWord_4123696
  simp only [CollatzResearch.WordTrace]
  refine ⟨75201774634280569026007471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100269032845707425368009961 75201774634280569026007471)
  ·
    refine ⟨112802661951420853539011207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75201774634280569026007471 112802661951420853539011207)
    ·
      refine ⟨169203992927131280308516811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112802661951420853539011207 169203992927131280308516811)
      ·
        refine ⟨253805989390696920462775217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169203992927131280308516811 253805989390696920462775217)
        ·
          refine ⟨190354492043022690347081413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253805989390696920462775217 190354492043022690347081413)
          ·
            refine ⟨35691467258066754440077765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190354492043022690347081413 35691467258066754440077765)
            ·
              refine ⟨6692150110887516457514581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35691467258066754440077765 6692150110887516457514581)
              ·
                refine ⟨78423634111963083486499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6692150110887516457514581 78423634111963083486499)
                ·
                  rfl

theorem cell23_4123696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 8].length) (baseStart_4123696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123696 prefixEnd_4123696 := by exact prefixLift 4123696
  have htrace : WordTrace (prefixWord ++ tailWord_4123696) baseStart_4123696 baseEnd_4123696 := by
    simpa [prefixWord, tailWord_4123696, baseEnd_4123696] using wordTrace_append hprefix tailTrace_4123696
  have hstable : (prefixWord ++ tailWord_4123696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123696).length < 2 ^ (prefixWord ++ tailWord_4123696).sum := by decide
  have hdescent : baseEnd_4123696 < baseStart_4123696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123757 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_4123757 : Nat := 118140960795 + 4123757 * 2 ^ 59
def prefixEnd_4123757 : Nat := 4983230072969 + 3 ^ 40 * 4123757 * 2
def baseEnd_4123757 : Nat := 2117469443342927515472693

theorem tailTrace_4123757 : CollatzResearch.WordTrace tailWord_4123757 prefixEnd_4123757 2117469443342927515472693 := by
  unfold tailWord_4123757
  simp only [CollatzResearch.WordTrace]
  refine ⟨150405774121340145469985525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100270516080893430313323683 150405774121340145469985525)
  ·
    refine ⟨14100541323875638637811143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150405774121340145469985525 14100541323875638637811143)
    ·
      refine ⟨21150811985813457956716715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14100541323875638637811143 21150811985813457956716715)
      ·
        refine ⟨31726217978720186935075073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21150811985813457956716715 31726217978720186935075073)
        ·
          refine ⟨23794663484040140201306305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31726217978720186935075073 23794663484040140201306305)
          ·
            refine ⟨17845997613030105150979729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23794663484040140201306305 17845997613030105150979729)
            ·
              refine ⟨13384498209772578863234797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17845997613030105150979729 13384498209772578863234797)
              ·
                refine ⟨5019186828664717073713049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13384498209772578863234797 5019186828664717073713049)
                ·
                  refine ⟨3764390121498537805284787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5019186828664717073713049 3764390121498537805284787)
                  ·
                    refine ⟨5646585182247806707927181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3764390121498537805284787 5646585182247806707927181)
                    ·
                      refine ⟨2117469443342927515472693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5646585182247806707927181 2117469443342927515472693)
                      ·
                        rfl

theorem cell23_4123757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_4123757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123757 prefixEnd_4123757 := by exact prefixLift 4123757
  have htrace : WordTrace (prefixWord ++ tailWord_4123757) baseStart_4123757 baseEnd_4123757 := by
    simpa [prefixWord, tailWord_4123757, baseEnd_4123757] using wordTrace_append hprefix tailTrace_4123757
  have hstable : (prefixWord ++ tailWord_4123757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123757).length < 2 ^ (prefixWord ++ tailWord_4123757).sum := by decide
  have hdescent : baseEnd_4123757 < baseStart_4123757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123784 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 1, 3, 2]
def baseStart_4123784 : Nat := 118140960795 + 4123784 * 2 ^ 59
def prefixEnd_4123784 : Nat := 4983230072969 + 3 ^ 40 * 4123784 * 2
def baseEnd_4123784 : Nat := 2117483307320598909835069

theorem tailTrace_4123784 : CollatzResearch.WordTrace tailWord_4123784 prefixEnd_4123784 2117483307320598909835069 := by
  unfold tailWord_4123784
  simp only [CollatzResearch.WordTrace]
  refine ⟨75203379446121164540609203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100271172594828219387478937 75203379446121164540609203)
  ·
    refine ⟨112805069169181746810913805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75203379446121164540609203 112805069169181746810913805)
    ·
      refine ⟨42301900938443155054092677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112805069169181746810913805 42301900938443155054092677)
      ·
        refine ⟨7931606425958091572642377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42301900938443155054092677 7931606425958091572642377)
        ·
          refine ⟨5948704819468568679481783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7931606425958091572642377 5948704819468568679481783)
          ·
            refine ⟨8923057229202853019222675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948704819468568679481783 8923057229202853019222675)
            ·
              refine ⟨13384585843804279528834013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8923057229202853019222675 13384585843804279528834013)
              ·
                refine ⟨5019219691426604823312755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13384585843804279528834013 5019219691426604823312755)
                ·
                  refine ⟨7528829537139907234969133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019219691426604823312755 7528829537139907234969133)
                  ·
                    refine ⟨2823311076427465213113425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7528829537139907234969133 2823311076427465213113425)
                    ·
                      refine ⟨2117483307320598909835069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823311076427465213113425 2117483307320598909835069)
                      ·
                        rfl

theorem cell23_4123784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_4123784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123784 prefixEnd_4123784 := by exact prefixLift 4123784
  have htrace : WordTrace (prefixWord ++ tailWord_4123784) baseStart_4123784 baseEnd_4123784 := by
    simpa [prefixWord, tailWord_4123784, baseEnd_4123784] using wordTrace_append hprefix tailTrace_4123784
  have hstable : (prefixWord ++ tailWord_4123784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123784).length < 2 ^ (prefixWord ++ tailWord_4123784).sum := by decide
  have hdescent : baseEnd_4123784 < baseStart_4123784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123797 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 2, 2, 2]
def baseStart_4123797 : Nat := 118140960795 + 4123797 * 2 ^ 59
def prefixEnd_4123797 : Nat := 4983230072969 + 3 ^ 40 * 4123797 * 2
def baseEnd_4123797 : Nat := 2117489982569107358972509

theorem tailTrace_4123797 : CollatzResearch.WordTrace tailWord_4123797 prefixEnd_4123797 2117489982569107358972509 := by
  unfold tailWord_4123797
  simp only [CollatzResearch.WordTrace]
  refine ⟨150407233041195232301441645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100271488694130154867627763 150407233041195232301441645)
  ·
    refine ⟨56402712390448212113040617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150407233041195232301441645 56402712390448212113040617)
    ·
      refine ⟨42302034292836159084780463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56402712390448212113040617 42302034292836159084780463)
      ·
        refine ⟨63453051439254238627170695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42302034292836159084780463 63453051439254238627170695)
        ·
          refine ⟨95179577158881357940756043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63453051439254238627170695 95179577158881357940756043)
          ·
            refine ⟨142769365738322036911134065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95179577158881357940756043 142769365738322036911134065)
            ·
              refine ⟨107077024303741527683350549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142769365738322036911134065 107077024303741527683350549)
              ·
                refine ⟨5019235514237884110157057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107077024303741527683350549 5019235514237884110157057)
                ·
                  refine ⟨3764426635678413082617793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5019235514237884110157057 3764426635678413082617793)
                  ·
                    refine ⟨2823319976758809811963345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3764426635678413082617793 2823319976758809811963345)
                    ·
                      refine ⟨2117489982569107358972509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823319976758809811963345 2117489982569107358972509)
                      ·
                        rfl

theorem cell23_4123797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_4123797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123797 prefixEnd_4123797 := by exact prefixLift 4123797
  have htrace : WordTrace (prefixWord ++ tailWord_4123797) baseStart_4123797 baseEnd_4123797 := by
    simpa [prefixWord, tailWord_4123797, baseEnd_4123797] using wordTrace_append hprefix tailTrace_4123797
  have hstable : (prefixWord ++ tailWord_4123797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123797).length < 2 ^ (prefixWord ++ tailWord_4123797).sum := by decide
  have hdescent : baseEnd_4123797 < baseStart_4123797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123833 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 1, 7]
def baseStart_4123833 : Nat := 118140960795 + 4123833 * 2 ^ 59
def prefixEnd_4123833 : Nat := 4983230072969 + 3 ^ 40 * 4123833 * 2
def baseEnd_4123833 : Nat := 705836155957556406040781

theorem tailTrace_4123833 : CollatzResearch.WordTrace tailWord_4123833 prefixEnd_4123833 705836155957556406040781 := by
  unfold tailWord_4123833
  simp only [CollatzResearch.WordTrace]
  refine ⟨150408546069064810449752153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100272364046043206966501435 150408546069064810449752153)
  ·
    refine ⟨112806409551798607837314115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150408546069064810449752153 112806409551798607837314115)
    ·
      refine ⟨169209614327697911755971173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112806409551798607837314115 169209614327697911755971173)
      ·
        refine ⟨31726802686443358454244595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169209614327697911755971173 31726802686443358454244595)
        ·
          refine ⟨47590204029665037681366893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31726802686443358454244595 47590204029665037681366893)
          ·
            refine ⟨17846326511124389130512585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47590204029665037681366893 17846326511124389130512585)
            ·
              refine ⟨13384744883343291847884439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17846326511124389130512585 13384744883343291847884439)
              ·
                refine ⟨20077117325014937771826659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13384744883343291847884439 20077117325014937771826659)
                ·
                  refine ⟨30115675987522406657739989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20077117325014937771826659 30115675987522406657739989)
                  ·
                    refine ⟨705836155957556406040781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30115675987522406657739989 705836155957556406040781)
                    ·
                      rfl

theorem cell23_4123833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_4123833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123833 prefixEnd_4123833 := by exact prefixLift 4123833
  have htrace : WordTrace (prefixWord ++ tailWord_4123833) baseStart_4123833 baseEnd_4123833 := by
    simpa [prefixWord, tailWord_4123833, baseEnd_4123833] using wordTrace_append hprefix tailTrace_4123833
  have hstable : (prefixWord ++ tailWord_4123833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123833).length < 2 ^ (prefixWord ++ tailWord_4123833).sum := by decide
  have hdescent : baseEnd_4123833 < baseStart_4123833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123850 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_4123850 : Nat := 118140960795 + 4123850 * 2 ^ 59
def prefixEnd_4123850 : Nat := 4983230072969 + 3 ^ 40 * 4123850 * 2
def baseEnd_4123850 : Nat := 705839065681265217203255

theorem tailTrace_4123850 : CollatzResearch.WordTrace tailWord_4123850 prefixEnd_4123850 705839065681265217203255 := by
  unfold tailWord_4123850
  simp only [CollatzResearch.WordTrace]
  refine ⟨37602291527500805588280251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100272777406668814902080669 37602291527500805588280251)
  ·
    refine ⟨56403437291251208382420377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37602291527500805588280251 56403437291251208382420377)
    ·
      refine ⟨42302577968438406286815283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56403437291251208382420377 42302577968438406286815283)
      ·
        refine ⟨63453866952657609430222925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42302577968438406286815283 63453866952657609430222925)
        ·
          refine ⟨23795200107246603536333597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63453866952657609430222925 23795200107246603536333597)
          ·
            refine ⟨8923200040217476326125099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23795200107246603536333597 8923200040217476326125099)
            ·
              refine ⟨13384800060326214489187649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8923200040217476326125099 13384800060326214489187649)
              ·
                refine ⟨10038600045244660866890737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13384800060326214489187649 10038600045244660866890737)
                ·
                  refine ⟨7528950033933495650168053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10038600045244660866890737 7528950033933495650168053)
                  ·
                    refine ⟨705839065681265217203255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7528950033933495650168053 705839065681265217203255)
                    ·
                      rfl

theorem cell23_4123850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_4123850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123850 prefixEnd_4123850 := by exact prefixLift 4123850
  have htrace : WordTrace (prefixWord ++ tailWord_4123850) baseStart_4123850 baseEnd_4123850 := by
    simpa [prefixWord, tailWord_4123850, baseEnd_4123850] using wordTrace_append hprefix tailTrace_4123850
  have hstable : (prefixWord ++ tailWord_4123850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123850).length < 2 ^ (prefixWord ++ tailWord_4123850).sum := by decide
  have hdescent : baseEnd_4123850 < baseStart_4123850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123854 : List Nat := [4, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_4123854 : Nat := 118140960795 + 4123854 * 2 ^ 59
def prefixEnd_4123854 : Nat := 4983230072969 + 3 ^ 40 * 4123854 * 2
def baseEnd_4123854 : Nat := 235279916774045959551083

theorem tailTrace_4123854 : CollatzResearch.WordTrace tailWord_4123854 prefixEnd_4123854 235279916774045959551083 := by
  unfold tailWord_4123854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18801164000248591379533327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100272874667992487357511077 18801164000248591379533327)
  ·
    refine ⟨28201746000372887069299991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18801164000248591379533327 28201746000372887069299991)
    ·
      refine ⟨42302619000559330603949987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28201746000372887069299991 42302619000559330603949987)
      ·
        refine ⟨63453928500838995905924981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42302619000559330603949987 63453928500838995905924981)
        ·
          refine ⟨5948805796953655866180467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63453928500838995905924981 5948805796953655866180467)
          ·
            refine ⟨8923208695430483799270701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948805796953655866180467 8923208695430483799270701)
            ·
              refine ⟨3346203260786431424726513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8923208695430483799270701 3346203260786431424726513)
              ·
                refine ⟨2509652445589823568544885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3346203260786431424726513 2509652445589823568544885)
                ·
                  refine ⟨235279916774045959551083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2509652445589823568544885 235279916774045959551083)
                  ·
                    rfl

theorem cell23_4123854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_4123854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123854 prefixEnd_4123854 := by exact prefixLift 4123854
  have htrace : WordTrace (prefixWord ++ tailWord_4123854) baseStart_4123854 baseEnd_4123854 := by
    simpa [prefixWord, tailWord_4123854, baseEnd_4123854] using wordTrace_append hprefix tailTrace_4123854
  have hstable : (prefixWord ++ tailWord_4123854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123854).length < 2 ^ (prefixWord ++ tailWord_4123854).sum := by decide
  have hdescent : baseEnd_4123854 < baseStart_4123854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123880 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 5, 4]
def baseStart_4123880 : Nat := 118140960795 + 4123880 * 2 ^ 59
def prefixEnd_4123880 : Nat := 4983230072969 + 3 ^ 40 * 4123880 * 2
def baseEnd_4123880 : Nat := 705844200487810178078209

theorem tailTrace_4123880 : CollatzResearch.WordTrace tailWord_4123880 prefixEnd_4123880 705844200487810178078209 := by
  unfold tailWord_4123880
  simp only [CollatzResearch.WordTrace]
  refine ⟨75205130149947268738356547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100273506866596358317808729 75205130149947268738356547)
  ·
    refine ⟨112807695224920903107534821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75205130149947268738356547 112807695224920903107534821)
    ·
      refine ⟨21151442854672669332662779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112807695224920903107534821 21151442854672669332662779)
      ·
        refine ⟨31727164282009003998994169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21151442854672669332662779 31727164282009003998994169)
        ·
          refine ⟨23795373211506752999245627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31727164282009003998994169 23795373211506752999245627)
          ·
            refine ⟨35693059817260129498868441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23795373211506752999245627 35693059817260129498868441)
            ·
              refine ⟨26769794862945097124151331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35693059817260129498868441 26769794862945097124151331)
              ·
                refine ⟨40154692294417645686226997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26769794862945097124151331 40154692294417645686226997)
                ·
                  refine ⟨3764502402601654283083781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40154692294417645686226997 3764502402601654283083781)
                  ·
                    refine ⟨705844200487810178078209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3764502402601654283083781 705844200487810178078209)
                    ·
                      rfl

theorem cell23_4123880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_4123880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123880 prefixEnd_4123880 := by exact prefixLift 4123880
  have htrace : WordTrace (prefixWord ++ tailWord_4123880) baseStart_4123880 baseEnd_4123880 := by
    simpa [prefixWord, tailWord_4123880, baseEnd_4123880] using wordTrace_append hprefix tailTrace_4123880
  have hstable : (prefixWord ++ tailWord_4123880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123880).length < 2 ^ (prefixWord ++ tailWord_4123880).sum := by decide
  have hdescent : baseEnd_4123880 < baseStart_4123880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123887 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 4]
def baseStart_4123887 : Nat := 118140960795 + 4123887 * 2 ^ 59
def prefixEnd_4123887 : Nat := 4983230072969 + 3 ^ 40 * 4123887 * 2
def baseEnd_4123887 : Nat := 2117536195828012006847095

theorem tailTrace_4123887 : CollatzResearch.WordTrace tailWord_4123887 prefixEnd_4123887 2117536195828012006847095 := by
  unfold tailWord_4123887
  simp only [CollatzResearch.WordTrace]
  refine ⟨150410515610869177672217915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100273677073912785114811943 150410515610869177672217915)
  ·
    refine ⟨225615773416303766508326873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150410515610869177672217915 225615773416303766508326873)
    ·
      refine ⟨169211830062227824881245155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225615773416303766508326873 169211830062227824881245155)
      ·
        refine ⟨253817745093341737321867733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169211830062227824881245155 253817745093341737321867733)
        ·
          refine ⟨5948853400625196968481275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 253817745093341737321867733 5948853400625196968481275)
          ·
            refine ⟨8923280100937795452721913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948853400625196968481275 8923280100937795452721913)
            ·
              refine ⟨6692460075703346589541435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8923280100937795452721913 6692460075703346589541435)
              ·
                refine ⟨10038690113555019884312153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6692460075703346589541435 10038690113555019884312153)
                ·
                  refine ⟨7529017585166264913234115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10038690113555019884312153 7529017585166264913234115)
                  ·
                    refine ⟨11293526377749397369851173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7529017585166264913234115 11293526377749397369851173)
                    ·
                      refine ⟨2117536195828012006847095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11293526377749397369851173 2117536195828012006847095)
                      ·
                        rfl

theorem cell23_4123887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 4].length) (baseStart_4123887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123887 prefixEnd_4123887 := by exact prefixLift 4123887
  have htrace : WordTrace (prefixWord ++ tailWord_4123887) baseStart_4123887 baseEnd_4123887 := by
    simpa [prefixWord, tailWord_4123887, baseEnd_4123887] using wordTrace_append hprefix tailTrace_4123887
  have hstable : (prefixWord ++ tailWord_4123887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123887).length < 2 ^ (prefixWord ++ tailWord_4123887).sum := by decide
  have hdescent : baseEnd_4123887 < baseStart_4123887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123897 : List Nat := [1, 2, 1, 3, 1, 1, 4, 5, 1, 4]
def baseStart_4123897 : Nat := 118140960795 + 4123897 * 2 ^ 59
def prefixEnd_4123897 : Nat := 4983230072969 + 3 ^ 40 * 4123897 * 2
def baseEnd_4123897 : Nat := 705847110211518989240683

theorem tailTrace_4123897 : CollatzResearch.WordTrace tailWord_4123897 prefixEnd_4123897 705847110211518989240683 := by
  unfold tailWord_4123897
  simp only [CollatzResearch.WordTrace]
  refine ⟨150410880340832949380081945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100273920227221966253387963 150410880340832949380081945)
  ·
    refine ⟨112808160255624712035061459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150410880340832949380081945 112808160255624712035061459)
    ·
      refine ⟨169212240383437068052592189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112808160255624712035061459 169212240383437068052592189)
      ·
        refine ⟨63454590143788900519722071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169212240383437068052592189 63454590143788900519722071)
        ·
          refine ⟨95181885215683350779583107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63454590143788900519722071 95181885215683350779583107)
          ·
            refine ⟨142772827823525026169374661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95181885215683350779583107 142772827823525026169374661)
            ·
              refine ⟨26769905216910942406757749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142772827823525026169374661 26769905216910942406757749)
              ·
                refine ⟨2509678614085400850633539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26769905216910942406757749 2509678614085400850633539)
                ·
                  refine ⟨3764517921128101275950309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509678614085400850633539 3764517921128101275950309)
                  ·
                    refine ⟨705847110211518989240683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3764517921128101275950309 705847110211518989240683)
                    ·
                      rfl

theorem cell23_4123897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 1, 4].length) (baseStart_4123897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123897 prefixEnd_4123897 := by exact prefixLift 4123897
  have htrace : WordTrace (prefixWord ++ tailWord_4123897) baseStart_4123897 baseEnd_4123897 := by
    simpa [prefixWord, tailWord_4123897, baseEnd_4123897] using wordTrace_append hprefix tailTrace_4123897
  have hstable : (prefixWord ++ tailWord_4123897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123897).length < 2 ^ (prefixWord ++ tailWord_4123897).sum := by decide
  have hdescent : baseEnd_4123897 < baseStart_4123897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123913 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_4123913 : Nat := 118140960795 + 4123913 * 2 ^ 59
def prefixEnd_4123913 : Nat := 4983230072969 + 3 ^ 40 * 4123913 * 2
def baseEnd_4123913 : Nat := 2117549546325028905121975

theorem tailTrace_4123913 : CollatzResearch.WordTrace tailWord_4123913 prefixEnd_4123913 2117549546325028905121975 := by
  unfold tailWord_4123913
  simp only [CollatzResearch.WordTrace]
  refine ⟨150411463908774984112664393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100274309272516656075109595 150411463908774984112664393)
  ·
    refine ⟨112808597931581238084498295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150411463908774984112664393 112808597931581238084498295)
    ·
      refine ⟨169212896897371857126747443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112808597931581238084498295 169212896897371857126747443)
      ·
        refine ⟨253819345346057785690121165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169212896897371857126747443 253819345346057785690121165)
        ·
          refine ⟨95182254504771669633795437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253819345346057785690121165 95182254504771669633795437)
          ·
            refine ⟨35693345439289376112673289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95182254504771669633795437 35693345439289376112673289)
            ·
              refine ⟨26770009079467032084504967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35693345439289376112673289 26770009079467032084504967)
              ·
                refine ⟨40155013619200548126757451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26770009079467032084504967 40155013619200548126757451)
                ·
                  refine ⟨60232520428800822190136177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40155013619200548126757451 60232520428800822190136177)
                  ·
                    refine ⟨45174390321600616642602133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60232520428800822190136177 45174390321600616642602133)
                    ·
                      refine ⟨2117549546325028905121975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45174390321600616642602133 2117549546325028905121975)
                      ·
                        rfl

theorem cell23_4123913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_4123913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123913 prefixEnd_4123913 := by exact prefixLift 4123913
  have htrace : WordTrace (prefixWord ++ tailWord_4123913) baseStart_4123913 baseEnd_4123913 := by
    simpa [prefixWord, tailWord_4123913, baseEnd_4123913] using wordTrace_append hprefix tailTrace_4123913
  have hstable : (prefixWord ++ tailWord_4123913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123913).length < 2 ^ (prefixWord ++ tailWord_4123913).sum := by decide
  have hdescent : baseEnd_4123913 < baseStart_4123913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123940 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_4123940 : Nat := 118140960795 + 4123940 * 2 ^ 59
def prefixEnd_4123940 : Nat := 4983230072969 + 3 ^ 40 * 4123940 * 2
def baseEnd_4123940 : Nat := 705854470100900099828117

theorem tailTrace_4123940 : CollatzResearch.WordTrace tailWord_4123940 prefixEnd_4123940 705854470100900099828117 := by
  unfold tailWord_4123940
  simp only [CollatzResearch.WordTrace]
  refine ⟨75206224339838583861948637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100274965786451445149264849 75206224339838583861948637)
  ·
    refine ⟨28202334127439468948230739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75206224339838583861948637 28202334127439468948230739)
    ·
      refine ⟨42303501191159203422346109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28202334127439468948230739 42303501191159203422346109)
      ·
        refine ⟨15863812946684701283379791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42303501191159203422346109 15863812946684701283379791)
        ·
          refine ⟨23795719420027051925069687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15863812946684701283379791 23795719420027051925069687)
          ·
            refine ⟨35693579130040577887604531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23795719420027051925069687 35693579130040577887604531)
            ·
              refine ⟨53540368695060866831406797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35693579130040577887604531 53540368695060866831406797)
              ·
                refine ⟨20077638260647825061777549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53540368695060866831406797 20077638260647825061777549)
                ·
                  refine ⟨7529114347742934398166581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20077638260647825061777549 7529114347742934398166581)
                  ·
                    refine ⟨705854470100900099828117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7529114347742934398166581 705854470100900099828117)
                    ·
                      rfl

theorem cell23_4123940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_4123940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123940 prefixEnd_4123940 := by exact prefixLift 4123940
  have htrace : WordTrace (prefixWord ++ tailWord_4123940) baseStart_4123940 baseEnd_4123940 := by
    simpa [prefixWord, tailWord_4123940, baseEnd_4123940] using wordTrace_append hprefix tailTrace_4123940
  have hstable : (prefixWord ++ tailWord_4123940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123940).length < 2 ^ (prefixWord ++ tailWord_4123940).sum := by decide
  have hdescent : baseEnd_4123940 < baseStart_4123940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123957 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_4123957 : Nat := 118140960795 + 4123957 * 2 ^ 59
def prefixEnd_4123957 : Nat := 4983230072969 + 3 ^ 40 * 4123957 * 2
def baseEnd_4123957 : Nat := 705857379824608910990591

theorem tailTrace_4123957 : CollatzResearch.WordTrace tailWord_4123957 prefixEnd_4123957 705857379824608910990591 := by
  unfold tailWord_4123957
  simp only [CollatzResearch.WordTrace]
  refine ⟨150413068720615579627266125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100275379147077053084844083 150413068720615579627266125)
  ·
    refine ⟨56404900770230842360224797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150413068720615579627266125 56404900770230842360224797)
    ·
      refine ⟨21151837788836565885084299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56404900770230842360224797 21151837788836565885084299)
      ·
        refine ⟨31727756683254848827626449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21151837788836565885084299 31727756683254848827626449)
        ·
          refine ⟨23795817512441136620719837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31727756683254848827626449 23795817512441136620719837)
          ·
            refine ⟨8923431567165426232769939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23795817512441136620719837 8923431567165426232769939)
            ·
              refine ⟨13385147350748139349154909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8923431567165426232769939 13385147350748139349154909)
              ·
                refine ⟨5019430256530552255933091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13385147350748139349154909 5019430256530552255933091)
                ·
                  refine ⟨7529145384795828383899637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019430256530552255933091 7529145384795828383899637)
                  ·
                    refine ⟨705857379824608910990591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7529145384795828383899637 705857379824608910990591)
                    ·
                      rfl

theorem cell23_4123957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_4123957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123957 prefixEnd_4123957 := by exact prefixLift 4123957
  have htrace : WordTrace (prefixWord ++ tailWord_4123957) baseStart_4123957 baseEnd_4123957 := by
    simpa [prefixWord, tailWord_4123957, baseEnd_4123957] using wordTrace_append hprefix tailTrace_4123957
  have hstable : (prefixWord ++ tailWord_4123957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123957).length < 2 ^ (prefixWord ++ tailWord_4123957).sum := by decide
  have hdescent : baseEnd_4123957 < baseStart_4123957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123980 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_4123980 : Nat := 118140960795 + 4123980 * 2 ^ 59
def prefixEnd_4123980 : Nat := 4983230072969 + 3 ^ 40 * 4123980 * 2
def baseEnd_4123980 : Nat := 2117583949528880142984167

theorem tailTrace_4123980 : CollatzResearch.WordTrace tailWord_4123980 prefixEnd_4123980 2117583949528880142984167 := by
  unfold tailWord_4123980
  simp only [CollatzResearch.WordTrace]
  refine ⟨75206953799766127277676697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100275938399688169703568929 75206953799766127277676697)
  ·
    refine ⟨56405215349824595458257523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75206953799766127277676697 56405215349824595458257523)
    ·
      refine ⟨84607823024736893187386285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56405215349824595458257523 84607823024736893187386285)
      ·
        refine ⟨31727933634276334945269857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84607823024736893187386285 31727933634276334945269857)
        ·
          refine ⟨23795950225707251208952393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31727933634276334945269857 23795950225707251208952393)
          ·
            refine ⟨17846962669280438406714295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23795950225707251208952393 17846962669280438406714295)
            ·
              refine ⟨26770444003920657610071443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17846962669280438406714295 26770444003920657610071443)
              ·
                refine ⟨40155666005880986415107165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26770444003920657610071443 40155666005880986415107165)
                ·
                  refine ⟨15058374752205369905665187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40155666005880986415107165 15058374752205369905665187)
                  ·
                    refine ⟨22587562128308054858497781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15058374752205369905665187 22587562128308054858497781)
                    ·
                      refine ⟨2117583949528880142984167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22587562128308054858497781 2117583949528880142984167)
                      ·
                        rfl

theorem cell23_4123980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_4123980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123980 prefixEnd_4123980 := by exact prefixLift 4123980
  have htrace : WordTrace (prefixWord ++ tailWord_4123980) baseStart_4123980 baseEnd_4123980 := by
    simpa [prefixWord, tailWord_4123980, baseEnd_4123980] using wordTrace_append hprefix tailTrace_4123980
  have hstable : (prefixWord ++ tailWord_4123980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123980).length < 2 ^ (prefixWord ++ tailWord_4123980).sum := by decide
  have hdescent : baseEnd_4123980 < baseStart_4123980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123994 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2]
def baseStart_4123994 : Nat := 118140960795 + 4123994 * 2 ^ 59
def prefixEnd_4123994 : Nat := 4983230072969 + 3 ^ 40 * 4123994 * 2
def baseEnd_4123994 : Nat := 2117591138258043088209103

theorem tailTrace_4123994 : CollatzResearch.WordTrace tailWord_4123994 prefixEnd_4123994 2117591138258043088209103 := by
  unfold tailWord_4123994
  simp only [CollatzResearch.WordTrace]
  refine ⟨37603604555370383736590759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100276278814321023297575357 37603604555370383736590759)
  ·
    refine ⟨56405406833055575604886139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37603604555370383736590759 56405406833055575604886139)
    ·
      refine ⟨84608110249583363407329209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56405406833055575604886139 84608110249583363407329209)
      ·
        refine ⟨63456082687187522555496907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84608110249583363407329209 63456082687187522555496907)
        ·
          refine ⟨95184124030781283833245361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63456082687187522555496907 95184124030781283833245361)
          ·
            refine ⟨71388093023085962874934021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95184124030781283833245361 71388093023085962874934021)
            ·
              refine ⟨13385267441828618039050129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71388093023085962874934021 13385267441828618039050129)
              ·
                refine ⟨10038950581371463529287597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13385267441828618039050129 10038950581371463529287597)
                ·
                  refine ⟨3764606468014298823482849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10038950581371463529287597 3764606468014298823482849)
                  ·
                    refine ⟨2823454851010724117612137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3764606468014298823482849 2823454851010724117612137)
                    ·
                      refine ⟨2117591138258043088209103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823454851010724117612137 2117591138258043088209103)
                      ·
                        rfl

theorem cell23_4123994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_4123994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4123994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4123994 prefixEnd_4123994 := by exact prefixLift 4123994
  have htrace : WordTrace (prefixWord ++ tailWord_4123994) baseStart_4123994 baseEnd_4123994 := by
    simpa [prefixWord, tailWord_4123994, baseEnd_4123994] using wordTrace_append hprefix tailTrace_4123994
  have hstable : (prefixWord ++ tailWord_4123994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123994).length < 2 ^ (prefixWord ++ tailWord_4123994).sum := by decide
  have hdescent : baseEnd_4123994 < baseStart_4123994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124000 : List Nat := [2, 1, 1, 3, 4, 2, 1, 9]
def baseStart_4124000 : Nat := 118140960795 + 4124000 * 2 ^ 59
def prefixEnd_4124000 : Nat := 4983230072969 + 3 ^ 40 * 4124000 * 2
def baseEnd_4124000 : Nat := 78429415523776669064225

theorem tailTrace_4124000 : CollatzResearch.WordTrace tailWord_4124000 prefixEnd_4124000 78429415523776669064225 := by
  unfold tailWord_4124000
  simp only [CollatzResearch.WordTrace]
  refine ⟨75207318529729898985540727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100276424706306531980720969 75207318529729898985540727)
  ·
    refine ⟨112810977794594848478311091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75207318529729898985540727 112810977794594848478311091)
    ·
      refine ⟨169216466691892272717466637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112810977794594848478311091 169216466691892272717466637)
      ·
        refine ⟨63456175009459602269049989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169216466691892272717466637 63456175009459602269049989)
        ·
          refine ⟨11898032814273675425446873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63456175009459602269049989 11898032814273675425446873)
          ·
            refine ⟨8923524610705256569085155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11898032814273675425446873 8923524610705256569085155)
            ·
              refine ⟨13385286916057884853627733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8923524610705256569085155 13385286916057884853627733)
              ·
                refine ⟨78429415523776669064225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13385286916057884853627733 78429415523776669064225)
                ·
                  rfl

theorem cell23_4124000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 9].length) (baseStart_4124000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124000 prefixEnd_4124000 := by exact prefixLift 4124000
  have htrace : WordTrace (prefixWord ++ tailWord_4124000) baseStart_4124000 baseEnd_4124000 := by
    simpa [prefixWord, tailWord_4124000, baseEnd_4124000] using wordTrace_append hprefix tailTrace_4124000
  have hstable : (prefixWord ++ tailWord_4124000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124000).length < 2 ^ (prefixWord ++ tailWord_4124000).sum := by decide
  have hdescent : baseEnd_4124000 < baseStart_4124000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124027 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 4, 1, 3]
def baseStart_4124027 : Nat := 118140960795 + 4124027 * 2 ^ 59
def prefixEnd_4124027 : Nat := 4983230072969 + 3 ^ 40 * 4124027 * 2
def baseEnd_4124027 : Nat := 2117608083119641459096451

theorem tailTrace_4124027 : CollatzResearch.WordTrace tailWord_4124027 prefixEnd_4124027 2117608083119641459096451 := by
  unfold tailWord_4124027
  simp only [CollatzResearch.WordTrace]
  refine ⟨150415621830361981582314335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100277081220241321054876223 150415621830361981582314335)
  ·
    refine ⟨225623432745542972373471503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150415621830361981582314335 225623432745542972373471503)
    ·
      refine ⟨338435149118314458560207255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225623432745542972373471503 338435149118314458560207255)
      ·
        refine ⟨507652723677471687840310883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338435149118314458560207255 507652723677471687840310883)
        ·
          refine ⟨761479085516207531760466325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507652723677471687840310883 761479085516207531760466325)
          ·
            refine ⟨35694332133572228051271859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 761479085516207531760466325 35694332133572228051271859)
            ·
              refine ⟨53541498200358342076907789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35694332133572228051271859 53541498200358342076907789)
              ·
                refine ⟨20078061825134378278840421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53541498200358342076907789 20078061825134378278840421)
                ·
                  refine ⟨3764636592212695927282579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20078061825134378278840421 3764636592212695927282579)
                  ·
                    refine ⟨5646954888319043890923869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3764636592212695927282579 5646954888319043890923869)
                    ·
                      refine ⟨2117608083119641459096451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5646954888319043890923869 2117608083119641459096451)
                      ·
                        rfl

theorem cell23_4124027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 1, 3].length) (baseStart_4124027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124027 prefixEnd_4124027 := by exact prefixLift 4124027
  have htrace : WordTrace (prefixWord ++ tailWord_4124027) baseStart_4124027 baseEnd_4124027 := by
    simpa [prefixWord, tailWord_4124027, baseEnd_4124027] using wordTrace_append hprefix tailTrace_4124027
  have hstable : (prefixWord ++ tailWord_4124027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124027).length < 2 ^ (prefixWord ++ tailWord_4124027).sum := by decide
  have hdescent : baseEnd_4124027 < baseStart_4124027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124028 : List Nat := [2, 2, 2, 1, 1, 1, 7, 2, 1, 2, 2]
def baseStart_4124028 : Nat := 118140960795 + 4124028 * 2 ^ 59
def prefixEnd_4124028 : Nat := 4983230072969 + 3 ^ 40 * 4124028 * 2
def baseEnd_4124028 : Nat := 2117608596600295955183947

theorem tailTrace_4124028 : CollatzResearch.WordTrace tailWord_4124028 prefixEnd_4124028 2117608596600295955183947 := by
  unfold tailWord_4124028
  simp only [CollatzResearch.WordTrace]
  refine ⟨75207829151679179376550369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100277105535572239168733825 75207829151679179376550369)
  ·
    refine ⟨56405871863759384532412777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75207829151679179376550369 56405871863759384532412777)
    ·
      refine ⟨42304403897819538399309583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56405871863759384532412777 42304403897819538399309583)
      ·
        refine ⟨63456605846729307598964375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42304403897819538399309583 63456605846729307598964375)
        ·
          refine ⟨95184908770093961398446563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63456605846729307598964375 95184908770093961398446563)
          ·
            refine ⟨142777363155140942097669845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95184908770093961398446563 142777363155140942097669845)
            ·
              refine ⟨3346344448948615830414137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142777363155140942097669845 3346344448948615830414137)
              ·
                refine ⟨2509758336711461872810603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3346344448948615830414137 2509758336711461872810603)
                ·
                  refine ⟨3764637505067192809215905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509758336711461872810603 3764637505067192809215905)
                  ·
                    refine ⟨2823478128800394606911929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3764637505067192809215905 2823478128800394606911929)
                    ·
                      refine ⟨2117608596600295955183947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823478128800394606911929 2117608596600295955183947)
                      ·
                        rfl

theorem cell23_4124028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_4124028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124028 prefixEnd_4124028 := by exact prefixLift 4124028
  have htrace : WordTrace (prefixWord ++ tailWord_4124028) baseStart_4124028 baseEnd_4124028 := by
    simpa [prefixWord, tailWord_4124028, baseEnd_4124028] using wordTrace_append hprefix tailTrace_4124028
  have hstable : (prefixWord ++ tailWord_4124028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124028).length < 2 ^ (prefixWord ++ tailWord_4124028).sum := by decide
  have hdescent : baseEnd_4124028 < baseStart_4124028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124034 : List Nat := [3, 4, 2, 1, 1, 2, 2, 8]
def baseStart_4124034 : Nat := 118140960795 + 4124034 * 2 ^ 59
def prefixEnd_4124034 : Nat := 4983230072969 + 3 ^ 40 * 4124034 * 2
def baseEnd_4124034 : Nat := 78430062129045293766997

theorem tailTrace_4124034 : CollatzResearch.WordTrace tailWord_4124034 prefixEnd_4124034 78430062129045293766997 := by
  unfold tailWord_4124034
  simp only [CollatzResearch.WordTrace]
  refine ⟨37603969285334155444454789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100277251427557747851879437 37603969285334155444454789)
  ·
    refine ⟨7050744241000154145835273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37603969285334155444454789 7050744241000154145835273)
    ·
      refine ⟨5288058180750115609376455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7050744241000154145835273 5288058180750115609376455)
      ·
        refine ⟨7932087271125173414064683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5288058180750115609376455 7932087271125173414064683)
        ·
          refine ⟨11898130906687760121097025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7932087271125173414064683 11898130906687760121097025)
          ·
            refine ⟨8923598180015820090822769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11898130906687760121097025 8923598180015820090822769)
            ·
              refine ⟨6692698635011865068117077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8923598180015820090822769 6692698635011865068117077)
              ·
                refine ⟨78430062129045293766997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6692698635011865068117077 78430062129045293766997)
                ·
                  rfl

theorem cell23_4124034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 8].length) (baseStart_4124034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124034 prefixEnd_4124034 := by exact prefixLift 4124034
  have htrace : WordTrace (prefixWord ++ tailWord_4124034) baseStart_4124034 baseEnd_4124034 := by
    simpa [prefixWord, tailWord_4124034, baseEnd_4124034] using wordTrace_append hprefix tailTrace_4124034
  have hstable : (prefixWord ++ tailWord_4124034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124034).length < 2 ^ (prefixWord ++ tailWord_4124034).sum := by decide
  have hdescent : baseEnd_4124034 < baseStart_4124034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124044 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 2, 1, 3]
def baseStart_4124044 : Nat := 118140960795 + 4124044 * 2 ^ 59
def prefixEnd_4124044 : Nat := 4983230072969 + 3 ^ 40 * 4124044 * 2
def baseEnd_4124044 : Nat := 2117616812290767892583873

theorem tailTrace_4124044 : CollatzResearch.WordTrace tailWord_4124044 prefixEnd_4124044 2117616812290767892583873 := by
  unfold tailWord_4124044
  simp only [CollatzResearch.WordTrace]
  refine ⟨75208120935650196742841593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100277494580866928990455457 75208120935650196742841593)
  ·
    refine ⟨56406090701737647557131195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75208120935650196742841593 56406090701737647557131195)
    ·
      refine ⟨84609136052606471335696793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56406090701737647557131195 84609136052606471335696793)
      ·
        refine ⟨63456852039454853501772595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84609136052606471335696793 63456852039454853501772595)
        ·
          refine ⟨95185278059182280252658893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63456852039454853501772595 95185278059182280252658893)
          ·
            refine ⟨35694479272193355094747085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95185278059182280252658893 35694479272193355094747085)
            ·
              refine ⟨13385429727072508160530157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35694479272193355094747085 13385429727072508160530157)
              ·
                refine ⟨5019536147652190560198809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13385429727072508160530157 5019536147652190560198809)
                ·
                  refine ⟨3764652110739142920149107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5019536147652190560198809 3764652110739142920149107)
                  ·
                    refine ⟨5646978166108714380223661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3764652110739142920149107 5646978166108714380223661)
                    ·
                      refine ⟨2117616812290767892583873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5646978166108714380223661 2117616812290767892583873)
                      ·
                        rfl

theorem cell23_4124044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_4124044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124044 prefixEnd_4124044 := by exact prefixLift 4124044
  have htrace : WordTrace (prefixWord ++ tailWord_4124044) baseStart_4124044 baseEnd_4124044 := by
    simpa [prefixWord, tailWord_4124044, baseEnd_4124044] using wordTrace_append hprefix tailTrace_4124044
  have hstable : (prefixWord ++ tailWord_4124044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124044).length < 2 ^ (prefixWord ++ tailWord_4124044).sum := by decide
  have hdescent : baseEnd_4124044 < baseStart_4124044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124117 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_4124117 : Nat := 118140960795 + 4124117 * 2 ^ 59
def prefixEnd_4124117 : Nat := 4983230072969 + 3 ^ 40 * 4124117 * 2
def baseEnd_4124117 : Nat := 2117654296378546106971037

theorem tailTrace_4124117 : CollatzResearch.WordTrace tailWord_4124117 prefixEnd_4124117 2117654296378546106971037 := by
  unfold tailWord_4124117
  simp only [CollatzResearch.WordTrace]
  refine ⟨150418904400035926953090605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100279269600023951302060403 150418904400035926953090605)
  ·
    refine ⟨56407089150013472607408977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150418904400035926953090605 56407089150013472607408977)
    ·
      refine ⟨42305316862510104455556733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56407089150013472607408977 42305316862510104455556733)
      ·
        refine ⟨15864493823441289170833775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42305316862510104455556733 15864493823441289170833775)
        ·
          refine ⟨23796740735161933756250663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15864493823441289170833775 23796740735161933756250663)
          ·
            refine ⟨35695111102742900634375995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23796740735161933756250663 35695111102742900634375995)
            ·
              refine ⟨53542666654114350951563993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35695111102742900634375995 53542666654114350951563993)
              ·
                refine ⟨40156999990585763213672995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53542666654114350951563993 40156999990585763213672995)
                ·
                  refine ⟨60235499985878644820509493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40156999990585763213672995 60235499985878644820509493)
                  ·
                    refine ⟨5647078123676122951922765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60235499985878644820509493 5647078123676122951922765)
                    ·
                      refine ⟨2117654296378546106971037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5647078123676122951922765 2117654296378546106971037)
                      ·
                        rfl

theorem cell23_4124117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_4124117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124117 prefixEnd_4124117 := by exact prefixLift 4124117
  have htrace : WordTrace (prefixWord ++ tailWord_4124117) baseStart_4124117 baseEnd_4124117 := by
    simpa [prefixWord, tailWord_4124117, baseEnd_4124117] using wordTrace_append hprefix tailTrace_4124117
  have hstable : (prefixWord ++ tailWord_4124117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124117).length < 2 ^ (prefixWord ++ tailWord_4124117).sum := by decide
  have hdescent : baseEnd_4124117 < baseStart_4124117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124157 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_4124157 : Nat := 118140960795 + 4124157 * 2 ^ 59
def prefixEnd_4124157 : Nat := 4983230072969 + 3 ^ 40 * 4124157 * 2
def baseEnd_4124157 : Nat := 2117674835604725950470853

theorem tailTrace_4124157 : CollatzResearch.WordTrace tailWord_4124157 prefixEnd_4124157 2117674835604725950470853 := by
  unfold tailWord_4124157
  simp only [CollatzResearch.WordTrace]
  refine ⟨150420363319891013784546725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100280242213260675856364483 150420363319891013784546725)
  ·
    refine ⟨28203818122479565084602511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150420363319891013784546725 28203818122479565084602511)
    ·
      refine ⟨42305727183719347626903767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28203818122479565084602511 42305727183719347626903767)
      ·
        refine ⟨63458590775579021440355651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42305727183719347626903767 63458590775579021440355651)
        ·
          refine ⟨95187886163368532160533477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63458590775579021440355651 95187886163368532160533477)
          ·
            refine ⟨17847728655631599780100027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95187886163368532160533477 17847728655631599780100027)
            ·
              refine ⟨26771592983447399670150041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17847728655631599780100027 26771592983447399670150041)
              ·
                refine ⟨20078694737585549752612531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26771592983447399670150041 20078694737585549752612531)
                ·
                  refine ⟨30118042106378324628918797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20078694737585549752612531 30118042106378324628918797)
                  ·
                    refine ⟨11294265789891871735844549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30118042106378324628918797 11294265789891871735844549)
                    ·
                      refine ⟨2117674835604725950470853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11294265789891871735844549 2117674835604725950470853)
                      ·
                        rfl

theorem cell23_4124157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_4124157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124157 prefixEnd_4124157 := by exact prefixLift 4124157
  have htrace : WordTrace (prefixWord ++ tailWord_4124157) baseStart_4124157 baseEnd_4124157 := by
    simpa [prefixWord, tailWord_4124157, baseEnd_4124157] using wordTrace_append hprefix tailTrace_4124157
  have hstable : (prefixWord ++ tailWord_4124157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124157).length < 2 ^ (prefixWord ++ tailWord_4124157).sum := by decide
  have hdescent : baseEnd_4124157 < baseStart_4124157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124177 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 3]
def baseStart_4124177 : Nat := 118140960795 + 4124177 * 2 ^ 59
def prefixEnd_4124177 : Nat := 4983230072969 + 3 ^ 40 * 4124177 * 2
def baseEnd_4124177 : Nat := 2117685105217815872220761

theorem tailTrace_4124177 : CollatzResearch.WordTrace tailWord_4124177 prefixEnd_4124177 2117685105217815872220761 := by
  unfold tailWord_4124177
  simp only [CollatzResearch.WordTrace]
  refine ⟨150421092779818557200274785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100280728519879038133516523 150421092779818557200274785)
  ·
    refine ⟨112815819584863917900206089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150421092779818557200274785 112815819584863917900206089)
    ·
      refine ⟨84611864688647938425154567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112815819584863917900206089 84611864688647938425154567)
      ·
        refine ⟨126917797032971907637731851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84611864688647938425154567 126917797032971907637731851)
        ·
          refine ⟨190376695549457861456597777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126917797032971907637731851 190376695549457861456597777)
          ·
            refine ⟨142782521662093396092448333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190376695549457861456597777 142782521662093396092448333)
            ·
              refine ⟨53543445623285023534668125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142782521662093396092448333 53543445623285023534668125)
              ·
                refine ⟨20078792108731883825500547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53543445623285023534668125 20078792108731883825500547)
                ·
                  refine ⟨30118188163097825738250821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20078792108731883825500547 30118188163097825738250821)
                  ·
                    refine ⟨5647160280580842325922029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30118188163097825738250821 5647160280580842325922029)
                    ·
                      refine ⟨2117685105217815872220761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5647160280580842325922029 2117685105217815872220761)
                      ·
                        rfl

theorem cell23_4124177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_4124177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124177 prefixEnd_4124177 := by exact prefixLift 4124177
  have htrace : WordTrace (prefixWord ++ tailWord_4124177) baseStart_4124177 baseEnd_4124177 := by
    simpa [prefixWord, tailWord_4124177, baseEnd_4124177] using wordTrace_append hprefix tailTrace_4124177
  have hstable : (prefixWord ++ tailWord_4124177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124177).length < 2 ^ (prefixWord ++ tailWord_4124177).sum := by decide
  have hdescent : baseEnd_4124177 < baseStart_4124177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124194 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_4124194 : Nat := 118140960795 + 4124194 * 2 ^ 59
def prefixEnd_4124194 : Nat := 4983230072969 + 3 ^ 40 * 4124194 * 2
def baseEnd_4124194 : Nat := 2117693834388942305708183

theorem tailTrace_4124194 : CollatzResearch.WordTrace tailWord_4124194 prefixEnd_4124194 2117693834388942305708183 := by
  unfold tailWord_4124194
  simp only [CollatzResearch.WordTrace]
  refine ⟨37605428205189242275910909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100281141880504646069095757 37605428205189242275910909)
  ·
    refine ⟨14102035576945965853466591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37605428205189242275910909 14102035576945965853466591)
    ·
      refine ⟨21153053365418948780199887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14102035576945965853466591 21153053365418948780199887)
      ·
        refine ⟨31729580048128423170299831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21153053365418948780199887 31729580048128423170299831)
        ·
          refine ⟨47594370072192634755449747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31729580048128423170299831 47594370072192634755449747)
          ·
            refine ⟨71391555108288952133174621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47594370072192634755449747 71391555108288952133174621)
            ·
              refine ⟨26771833165608357049940483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71391555108288952133174621 26771833165608357049940483)
              ·
                refine ⟨40157749748412535574910725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26771833165608357049940483 40157749748412535574910725)
                ·
                  refine ⟨7529578077827350420295761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40157749748412535574910725 7529578077827350420295761)
                  ·
                    refine ⟨5647183558370512815221821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7529578077827350420295761 5647183558370512815221821)
                    ·
                      refine ⟨2117693834388942305708183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5647183558370512815221821 2117693834388942305708183)
                      ·
                        rfl

theorem cell23_4124194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_4124194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124194 prefixEnd_4124194 := by exact prefixLift 4124194
  have htrace : WordTrace (prefixWord ++ tailWord_4124194) baseStart_4124194 baseEnd_4124194 := by
    simpa [prefixWord, tailWord_4124194, baseEnd_4124194] using wordTrace_append hprefix tailTrace_4124194
  have hstable : (prefixWord ++ tailWord_4124194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124194).length < 2 ^ (prefixWord ++ tailWord_4124194).sum := by decide
  have hdescent : baseEnd_4124194 < baseStart_4124194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124197 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 6]
def baseStart_4124197 : Nat := 118140960795 + 4124197 * 2 ^ 59
def prefixEnd_4124197 : Nat := 4983230072969 + 3 ^ 40 * 4124197 * 2
def baseEnd_4124197 : Nat := 235299486092322865996741

theorem tailTrace_4124197 : CollatzResearch.WordTrace tailWord_4124197 prefixEnd_4124197 235299486092322865996741 := by
  unfold tailWord_4124197
  simp only [CollatzResearch.WordTrace]
  refine ⟨150421822239746100616002845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100281214826497400410668563 150421822239746100616002845)
  ·
    refine ⟨56408183339904787731001067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150421822239746100616002845 56408183339904787731001067)
    ·
      refine ⟨84612275009857181596501601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56408183339904787731001067 84612275009857181596501601)
      ·
        refine ⟨63459206257392886197376201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84612275009857181596501601 63459206257392886197376201)
        ·
          refine ⟨47594404693044664648032151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63459206257392886197376201 47594404693044664648032151)
          ·
            refine ⟨71391607039566996972048227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47594404693044664648032151 71391607039566996972048227)
            ·
              refine ⟨107087410559350495458072341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71391607039566996972048227 107087410559350495458072341)
              ·
                refine ⟨5019722369969554474597141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107087410559350495458072341 5019722369969554474597141)
                ·
                  refine ⟨235299486092322865996741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5019722369969554474597141 235299486092322865996741)
                  ·
                    rfl

theorem cell23_4124197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_4124197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124197 prefixEnd_4124197 := by exact prefixLift 4124197
  have htrace : WordTrace (prefixWord ++ tailWord_4124197) baseStart_4124197 baseEnd_4124197 := by
    simpa [prefixWord, tailWord_4124197, baseEnd_4124197] using wordTrace_append hprefix tailTrace_4124197
  have hstable : (prefixWord ++ tailWord_4124197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124197).length < 2 ^ (prefixWord ++ tailWord_4124197).sum := by decide
  have hdescent : baseEnd_4124197 < baseStart_4124197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124224 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 5, 1, 3]
def baseStart_4124224 : Nat := 118140960795 + 4124224 * 2 ^ 59
def prefixEnd_4124224 : Nat := 4983230072969 + 3 ^ 40 * 4124224 * 2
def baseEnd_4124224 : Nat := 2117709238808577188333045

theorem tailTrace_4124224 : CollatzResearch.WordTrace tailWord_4124224 prefixEnd_4124224 2117709238808577188333045 := by
  unfold tailWord_4124224
  simp only [CollatzResearch.WordTrace]
  refine ⟨75211403505324142113617863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100281871340432189484823817 75211403505324142113617863)
  ·
    refine ⟨112817105257986213170426795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75211403505324142113617863 112817105257986213170426795)
    ·
      refine ⟨169225657886979319755640193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112817105257986213170426795 169225657886979319755640193)
      ·
        refine ⟨126919243415234489816730145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169225657886979319755640193 126919243415234489816730145)
        ·
          refine ⟨95189432561425867362547609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126919243415234489816730145 95189432561425867362547609)
          ·
            refine ⟨71392074421069400521910707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95189432561425867362547609 71392074421069400521910707)
            ·
              refine ⟨107088111631604100782866061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71392074421069400521910707 107088111631604100782866061)
              ·
                refine ⟨40158041861851537793574773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107088111631604100782866061 40158041861851537793574773)
                ·
                  refine ⟨3764816424548581668147635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40158041861851537793574773 3764816424548581668147635)
                  ·
                    refine ⟨5647224636822872502221453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3764816424548581668147635 5647224636822872502221453)
                    ·
                      refine ⟨2117709238808577188333045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5647224636822872502221453 2117709238808577188333045)
                      ·
                        rfl

theorem cell23_4124224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_4124224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124224 prefixEnd_4124224 := by exact prefixLift 4124224
  have htrace : WordTrace (prefixWord ++ tailWord_4124224) baseStart_4124224 baseEnd_4124224 := by
    simpa [prefixWord, tailWord_4124224, baseEnd_4124224] using wordTrace_append hprefix tailTrace_4124224
  have hstable : (prefixWord ++ tailWord_4124224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124224).length < 2 ^ (prefixWord ++ tailWord_4124224).sum := by decide
  have hdescent : baseEnd_4124224 < baseStart_4124224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124257 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 3, 6]
def baseStart_4124257 : Nat := 118140960795 + 4124257 * 2 ^ 59
def prefixEnd_4124257 : Nat := 4983230072969 + 3 ^ 40 * 4124257 * 2
def baseEnd_4124257 : Nat := 705908727890058519740131

theorem tailTrace_4124257 : CollatzResearch.WordTrace tailWord_4124257 prefixEnd_4124257 705908727890058519740131 := by
  unfold tailWord_4124257
  simp only [CollatzResearch.WordTrace]
  refine ⟨150424010619528730863187025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100282673746352487242124683 150424010619528730863187025)
  ·
    refine ⟨112818007964646548147390269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150424010619528730863187025 112818007964646548147390269)
    ·
      refine ⟨42306752986742455555271351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112818007964646548147390269 42306752986742455555271351)
      ·
        refine ⟨63460129480113683332907027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42306752986742455555271351 63460129480113683332907027)
        ·
          refine ⟨95190194220170524999360541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63460129480113683332907027 95190194220170524999360541)
          ·
            refine ⟨35696322832563946874760203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95190194220170524999360541 35696322832563946874760203)
            ·
              refine ⟨53544484248845920312140305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35696322832563946874760203 53544484248845920312140305)
              ·
                refine ⟨40158363186634440234105229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53544484248845920312140305 40158363186634440234105229)
                ·
                  refine ⟨15059386194987915087789461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40158363186634440234105229 15059386194987915087789461)
                  ·
                    refine ⟨705908727890058519740131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15059386194987915087789461 705908727890058519740131)
                    ·
                      rfl

theorem cell23_4124257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_4124257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124257 prefixEnd_4124257 := by exact prefixLift 4124257
  have htrace : WordTrace (prefixWord ++ tailWord_4124257) baseStart_4124257 baseEnd_4124257 := by
    simpa [prefixWord, tailWord_4124257, baseEnd_4124257] using wordTrace_append hprefix tailTrace_4124257
  have hstable : (prefixWord ++ tailWord_4124257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124257).length < 2 ^ (prefixWord ++ tailWord_4124257).sum := by decide
  have hdescent : baseEnd_4124257 < baseStart_4124257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124274 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_4124274 : Nat := 118140960795 + 4124274 * 2 ^ 59
def prefixEnd_4124274 : Nat := 4983230072969 + 3 ^ 40 * 4124274 * 2
def baseEnd_4124274 : Nat := 705911637613767330902605

theorem tailTrace_4124274 : CollatzResearch.WordTrace tailWord_4124274 prefixEnd_4124274 705911637613767330902605 := by
  unfold tailWord_4124274
  simp only [CollatzResearch.WordTrace]
  refine ⟨37606157665116785691638969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100283087106978095177703917 37606157665116785691638969)
  ·
    refine ⟨28204618248837589268729227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37606157665116785691638969 28204618248837589268729227)
    ·
      refine ⟨42306927373256383903093841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28204618248837589268729227 42306927373256383903093841)
      ·
        refine ⟨31730195529942287927320381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42306927373256383903093841 31730195529942287927320381)
        ·
          refine ⟨11898823323728357972745143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31730195529942287927320381 11898823323728357972745143)
          ·
            refine ⟨17848234985592536959117715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11898823323728357972745143 17848234985592536959117715)
            ·
              refine ⟨26772352478388805438676573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17848234985592536959117715 26772352478388805438676573)
              ·
                refine ⟨10039632179395802039503715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26772352478388805438676573 10039632179395802039503715)
                ·
                  refine ⟨15059448269093703059255573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10039632179395802039503715 15059448269093703059255573)
                  ·
                    refine ⟨705911637613767330902605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15059448269093703059255573 705911637613767330902605)
                    ·
                      rfl

theorem cell23_4124274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_4124274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124274 prefixEnd_4124274 := by exact prefixLift 4124274
  have htrace : WordTrace (prefixWord ++ tailWord_4124274) baseStart_4124274 baseEnd_4124274 := by
    simpa [prefixWord, tailWord_4124274, baseEnd_4124274] using wordTrace_append hprefix tailTrace_4124274
  have hstable : (prefixWord ++ tailWord_4124274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124274).length < 2 ^ (prefixWord ++ tailWord_4124274).sum := by decide
  have hdescent : baseEnd_4124274 < baseStart_4124274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124298 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4]
def baseStart_4124298 : Nat := 118140960795 + 4124298 * 2 ^ 59
def prefixEnd_4124298 : Nat := 4983230072969 + 3 ^ 40 * 4124298 * 2
def baseEnd_4124298 : Nat := 2117747236377009898807705

theorem tailTrace_4124298 : CollatzResearch.WordTrace tailWord_4124298 prefixEnd_4124298 2117747236377009898807705 := by
  unfold tailWord_4124298
  simp only [CollatzResearch.WordTrace]
  refine ⟨37606376503095048716357387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100283670674920129910286365 37606376503095048716357387)
  ·
    refine ⟨56409564754642573074536081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37606376503095048716357387 56409564754642573074536081)
    ·
      refine ⟨42307173565981929805902061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56409564754642573074536081 42307173565981929805902061)
      ·
        refine ⟨15865190087243223677213273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42307173565981929805902061 15865190087243223677213273)
        ·
          refine ⟨11898892565432417757909955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15865190087243223677213273 11898892565432417757909955)
          ·
            refine ⟨17848338848148626636864933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11898892565432417757909955 17848338848148626636864933)
            ·
              refine ⟨3346563534027867494412175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17848338848148626636864933 3346563534027867494412175)
              ·
                refine ⟨5019845301041801241618263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3346563534027867494412175 5019845301041801241618263)
                ·
                  refine ⟨7529767951562701862427395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019845301041801241618263 7529767951562701862427395)
                  ·
                    refine ⟨11294651927344052793641093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7529767951562701862427395 11294651927344052793641093)
                    ·
                      refine ⟨2117747236377009898807705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11294651927344052793641093 2117747236377009898807705)
                      ·
                        rfl

theorem cell23_4124298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_4124298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124298 prefixEnd_4124298 := by exact prefixLift 4124298
  have htrace : WordTrace (prefixWord ++ tailWord_4124298) baseStart_4124298 baseEnd_4124298 := by
    simpa [prefixWord, tailWord_4124298, baseEnd_4124298] using wordTrace_append hprefix tailTrace_4124298
  have hstable : (prefixWord ++ tailWord_4124298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124298).length < 2 ^ (prefixWord ++ tailWord_4124298).sum := by decide
  have hdescent : baseEnd_4124298 < baseStart_4124298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124308 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_4124308 : Nat := 118140960795 + 4124308 * 2 ^ 59
def prefixEnd_4124308 : Nat := 4983230072969 + 3 ^ 40 * 4124308 * 2
def baseEnd_4124308 : Nat := 705917457061184953227553

theorem tailTrace_4124308 : CollatzResearch.WordTrace tailWord_4124308 prefixEnd_4124308 705917457061184953227553 := by
  unfold tailWord_4124308
  simp only [CollatzResearch.WordTrace]
  refine ⟨75212935371171983286646789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100283913828229311048862385 75212935371171983286646789)
  ·
    refine ⟨14102425382094746866246273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75212935371171983286646789 14102425382094746866246273)
    ·
      refine ⟨10576819036571060149684705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14102425382094746866246273 10576819036571060149684705)
      ·
        refine ⟨7932614277428295112263529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10576819036571060149684705 7932614277428295112263529)
        ·
          refine ⟨5949460708071221334197647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7932614277428295112263529 5949460708071221334197647)
          ·
            refine ⟨8924191062106832001296471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949460708071221334197647 8924191062106832001296471)
            ·
              refine ⟨13386286593160248001944707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8924191062106832001296471 13386286593160248001944707)
              ·
                refine ⟨20079429889740372002917061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13386286593160248001944707 20079429889740372002917061)
                ·
                  refine ⟨3764893104326319750546949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20079429889740372002917061 3764893104326319750546949)
                  ·
                    refine ⟨705917457061184953227553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3764893104326319750546949 705917457061184953227553)
                    ·
                      rfl

theorem cell23_4124308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_4124308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124308 prefixEnd_4124308 := by exact prefixLift 4124308
  have htrace : WordTrace (prefixWord ++ tailWord_4124308) baseStart_4124308 baseEnd_4124308 := by
    simpa [prefixWord, tailWord_4124308, baseEnd_4124308] using wordTrace_append hprefix tailTrace_4124308
  have hstable : (prefixWord ++ tailWord_4124308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124308).length < 2 ^ (prefixWord ++ tailWord_4124308).sum := by decide
  have hdescent : baseEnd_4124308 < baseStart_4124308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124347 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 1, 8]
def baseStart_4124347 : Nat := 118140960795 + 4124347 * 2 ^ 59
def prefixEnd_4124347 : Nat := 4983230072969 + 3 ^ 40 * 4124347 * 2
def baseEnd_4124347 : Nat := 705924132309693402364993

theorem tailTrace_4124347 : CollatzResearch.WordTrace tailWord_4124347 prefixEnd_4124347 705924132309693402364993 := by
  unfold tailWord_4124347
  simp only [CollatzResearch.WordTrace]
  refine ⟨150427293189202676233963295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100284862126135117489308863 150427293189202676233963295)
  ·
    refine ⟨225640939783804014350944943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150427293189202676233963295 225640939783804014350944943)
    ·
      refine ⟨338461409675706021526417415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225640939783804014350944943 338461409675706021526417415)
      ·
        refine ⟨507692114513559032289626123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338461409675706021526417415 507692114513559032289626123)
        ·
          refine ⟨761538171770338548434439185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507692114513559032289626123 761538171770338548434439185)
          ·
            refine ⟨571153628827753911325829389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761538171770338548434439185 571153628827753911325829389)
            ·
              refine ⟨214182610810407716747186021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 571153628827753911325829389 214182610810407716747186021)
              ·
                refine ⟨40159239526951446890097379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214182610810407716747186021 40159239526951446890097379)
                ·
                  refine ⟨60238859290427170335146069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40159239526951446890097379 60238859290427170335146069)
                  ·
                    refine ⟨705924132309693402364993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60238859290427170335146069 705924132309693402364993)
                    ·
                      rfl

theorem cell23_4124347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 8].length) (baseStart_4124347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124347 prefixEnd_4124347 := by exact prefixLift 4124347
  have htrace : WordTrace (prefixWord ++ tailWord_4124347) baseStart_4124347 baseEnd_4124347 := by
    simpa [prefixWord, tailWord_4124347, baseEnd_4124347] using wordTrace_append hprefix tailTrace_4124347
  have hstable : (prefixWord ++ tailWord_4124347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124347).length < 2 ^ (prefixWord ++ tailWord_4124347).sum := by decide
  have hdescent : baseEnd_4124347 < baseStart_4124347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124365 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4124365 : Nat := 118140960795 + 4124365 * 2 ^ 59
def prefixEnd_4124365 : Nat := 4983230072969 + 3 ^ 40 * 4124365 * 2
def baseEnd_4124365 : Nat := 2117781639580861136669897

theorem tailTrace_4124365 : CollatzResearch.WordTrace tailWord_4124365 prefixEnd_4124365 2117781639580861136669897 := by
  unfold tailWord_4124365
  simp only [CollatzResearch.WordTrace]
  refine ⟨150427949703137465308118549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100285299802091643538745699 150427949703137465308118549)
  ·
    refine ⟨7051310142334568686318057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150427949703137465308118549 7051310142334568686318057)
    ·
      refine ⟨5288482606750926514738543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7051310142334568686318057 5288482606750926514738543)
      ·
        refine ⟨7932723910126389772107815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5288482606750926514738543 7932723910126389772107815)
        ·
          refine ⟨11899085865189584658161723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7932723910126389772107815 11899085865189584658161723)
          ·
            refine ⟨17848628797784376987242585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11899085865189584658161723 17848628797784376987242585)
            ·
              refine ⟨13386471598338282740431939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17848628797784376987242585 13386471598338282740431939)
              ·
                refine ⟨20079707397507424110647909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13386471598338282740431939 20079707397507424110647909)
                ·
                  refine ⟨3764945137032642020746483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20079707397507424110647909 3764945137032642020746483)
                  ·
                    refine ⟨5647417705548963031119725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3764945137032642020746483 5647417705548963031119725)
                    ·
                      refine ⟨2117781639580861136669897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5647417705548963031119725 2117781639580861136669897)
                      ·
                        rfl

theorem cell23_4124365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4124365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124365 prefixEnd_4124365 := by exact prefixLift 4124365
  have htrace : WordTrace (prefixWord ++ tailWord_4124365) baseStart_4124365 baseEnd_4124365 := by
    simpa [prefixWord, tailWord_4124365, baseEnd_4124365] using wordTrace_append hprefix tailTrace_4124365
  have hstable : (prefixWord ++ tailWord_4124365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124365).length < 2 ^ (prefixWord ++ tailWord_4124365).sum := by decide
  have hdescent : baseEnd_4124365 < baseStart_4124365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124384 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_4124384 : Nat := 118140960795 + 4124384 * 2 ^ 59
def prefixEnd_4124384 : Nat := 4983230072969 + 3 ^ 40 * 4124384 * 2
def baseEnd_4124384 : Nat := 2117791395713296562332309

theorem tailTrace_4124384 : CollatzResearch.WordTrace tailWord_4124384 prefixEnd_4124384 2117791395713296562332309 := by
  unfold tailWord_4124384
  simp only [CollatzResearch.WordTrace]
  refine ⟨75214321345034315776530103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100285761793379087702040137 75214321345034315776530103)
  ·
    refine ⟨112821482017551473664795155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75214321345034315776530103 112821482017551473664795155)
    ·
      refine ⟨169232223026327210497192733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112821482017551473664795155 169232223026327210497192733)
      ·
        refine ⟨63462083634872703936447275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169232223026327210497192733 63462083634872703936447275)
        ·
          refine ⟨95193125452309055904670913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63462083634872703936447275 95193125452309055904670913)
          ·
            refine ⟨71394844089231791928503185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95193125452309055904670913 71394844089231791928503185)
            ·
              refine ⟨53546133066923843946377389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71394844089231791928503185 53546133066923843946377389)
              ·
                refine ⟨20079799900096441479891521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53546133066923843946377389 20079799900096441479891521)
                ·
                  refine ⟨15059849925072331109918641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20079799900096441479891521 15059849925072331109918641)
                  ·
                    refine ⟨11294887443804248332438981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15059849925072331109918641 11294887443804248332438981)
                    ·
                      refine ⟨2117791395713296562332309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11294887443804248332438981 2117791395713296562332309)
                      ·
                        rfl

theorem cell23_4124384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_4124384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124384 prefixEnd_4124384 := by exact prefixLift 4124384
  have htrace : WordTrace (prefixWord ++ tailWord_4124384) baseStart_4124384 baseEnd_4124384 := by
    simpa [prefixWord, tailWord_4124384, baseEnd_4124384] using wordTrace_append hprefix tailTrace_4124384
  have hstable : (prefixWord ++ tailWord_4124384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124384).length < 2 ^ (prefixWord ++ tailWord_4124384).sum := by decide
  have hdescent : baseEnd_4124384 < baseStart_4124384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124394 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 7]
def baseStart_4124394 : Nat := 118140960795 + 4124394 * 2 ^ 59
def prefixEnd_4124394 : Nat := 4983230072969 + 3 ^ 40 * 4124394 * 2
def baseEnd_4124394 : Nat := 235310725613315724800807

theorem tailTrace_4124394 : CollatzResearch.WordTrace tailWord_4124394 prefixEnd_4124394 235310725613315724800807 := by
  unfold tailWord_4124394
  simp only [CollatzResearch.WordTrace]
  refine ⟨37607251855008100815231059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100286004946688268840616157 37607251855008100815231059)
  ·
    refine ⟨56410877782512151222846589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37607251855008100815231059 56410877782512151222846589)
    ·
      refine ⟨21154079168442056708567471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56410877782512151222846589 21154079168442056708567471)
      ·
        refine ⟨31731118752663085062851207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21154079168442056708567471 31731118752663085062851207)
        ·
          refine ⟨47596678128994627594276811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31731118752663085062851207 47596678128994627594276811)
          ·
            refine ⟨71395017193491941391415217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47596678128994627594276811 71395017193491941391415217)
            ·
              refine ⟨53546262895118956043561413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71395017193491941391415217 53546262895118956043561413)
              ·
                refine ⟨10039924292834804258167765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53546262895118956043561413 10039924292834804258167765)
                ·
                  refine ⟨235310725613315724800807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10039924292834804258167765 235310725613315724800807)
                  ·
                    rfl

theorem cell23_4124394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_4124394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124394 prefixEnd_4124394 := by exact prefixLift 4124394
  have htrace : WordTrace (prefixWord ++ tailWord_4124394) baseStart_4124394 baseEnd_4124394 := by
    simpa [prefixWord, tailWord_4124394, baseEnd_4124394] using wordTrace_append hprefix tailTrace_4124394
  have hstable : (prefixWord ++ tailWord_4124394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124394).length < 2 ^ (prefixWord ++ tailWord_4124394).sum := by decide
  have hdescent : baseEnd_4124394 < baseStart_4124394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124428 : List Nat := [2, 2, 1, 2, 2, 1, 6, 2, 5]
def baseStart_4124428 : Nat := 118140960795 + 4124428 * 2 ^ 59
def prefixEnd_4124428 : Nat := 4983230072969 + 3 ^ 40 * 4124428 * 2
def baseEnd_4124428 : Nat := 235312665429121598909123

theorem tailTrace_4124428 : CollatzResearch.WordTrace tailWord_4124428 prefixEnd_4124428 235312665429121598909123 := by
  unfold tailWord_4124428
  simp only [CollatzResearch.WordTrace]
  refine ⟨75215123750954613533830969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100286831667939484711774625 75215123750954613533830969)
  ·
    refine ⟨56411342813215960150373227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75215123750954613533830969 56411342813215960150373227)
    ·
      refine ⟨84617014219823940225559841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56411342813215960150373227 84617014219823940225559841)
      ·
        refine ⟨63462760664867955169169881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84617014219823940225559841 63462760664867955169169881)
        ·
          refine ⟨47597070498650966376877411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63462760664867955169169881 47597070498650966376877411)
          ·
            refine ⟨71395605747976449565316117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47597070498650966376877411 71395605747976449565316117)
            ·
              refine ⟨3346669019436396073374193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71395605747976449565316117 3346669019436396073374193)
              ·
                refine ⟨2510001764577297055030645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3346669019436396073374193 2510001764577297055030645)
                ·
                  refine ⟨235312665429121598909123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2510001764577297055030645 235312665429121598909123)
                  ·
                    rfl

theorem cell23_4124428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_4124428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124428 prefixEnd_4124428 := by exact prefixLift 4124428
  have htrace : WordTrace (prefixWord ++ tailWord_4124428) baseStart_4124428 baseEnd_4124428 := by
    simpa [prefixWord, tailWord_4124428, baseEnd_4124428] using wordTrace_append hprefix tailTrace_4124428
  have hstable : (prefixWord ++ tailWord_4124428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124428).length < 2 ^ (prefixWord ++ tailWord_4124428).sum := by decide
  have hdescent : baseEnd_4124428 < baseStart_4124428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124488 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 3, 4]
def baseStart_4124488 : Nat := 118140960795 + 4124488 * 2 ^ 59
def prefixEnd_4124488 : Nat := 4983230072969 + 3 ^ 40 * 4124488 * 2
def baseEnd_4124488 : Nat := 705948265900454718477277

theorem tailTrace_4124488 : CollatzResearch.WordTrace tailWord_4124488 prefixEnd_4124488 705948265900454718477277 := by
  unfold tailWord_4124488
  simp only [CollatzResearch.WordTrace]
  refine ⟨75216217940845928657423059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100288290587794571543230745 75216217940845928657423059)
  ·
    refine ⟨112824326911268892986134589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75216217940845928657423059 112824326911268892986134589)
    ·
      refine ⟨42309122591725834869800471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112824326911268892986134589 42309122591725834869800471)
      ·
        refine ⟨63463683887588752304700707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42309122591725834869800471 63463683887588752304700707)
        ·
          refine ⟨95195525831383128457051061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63463683887588752304700707 95195525831383128457051061)
          ·
            refine ⟨8924580546692168292848537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95195525831383128457051061 8924580546692168292848537)
            ·
              refine ⟨6693435410019126219636403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8924580546692168292848537 6693435410019126219636403)
              ·
                refine ⟨10040153115028689329454605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6693435410019126219636403 10040153115028689329454605)
                ·
                  refine ⟨3765057418135758498545477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10040153115028689329454605 3765057418135758498545477)
                  ·
                    refine ⟨705948265900454718477277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3765057418135758498545477 705948265900454718477277)
                    ·
                      rfl

theorem cell23_4124488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_4124488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124488 prefixEnd_4124488 := by exact prefixLift 4124488
  have htrace : WordTrace (prefixWord ++ tailWord_4124488) baseStart_4124488 baseEnd_4124488 := by
    simpa [prefixWord, tailWord_4124488, baseEnd_4124488] using wordTrace_append hprefix tailTrace_4124488
  have hstable : (prefixWord ++ tailWord_4124488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124488).length < 2 ^ (prefixWord ++ tailWord_4124488).sum := by decide
  have hdescent : baseEnd_4124488 < baseStart_4124488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124538 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2]
def baseStart_4124538 : Nat := 118140960795 + 4124538 * 2 ^ 59
def prefixEnd_4124538 : Nat := 4983230072969 + 3 ^ 40 * 4124538 * 2
def baseEnd_4124538 : Nat := 2117870471734088959806601

theorem tailTrace_4124538 : CollatzResearch.WordTrace tailWord_4124538 prefixEnd_4124538 2117870471734088959806601 := by
  unfold tailWord_4124538
  simp only [CollatzResearch.WordTrace]
  refine ⟨37608564882877678963541567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100289506354340477236110845 37608564882877678963541567)
  ·
    refine ⟨56412847324316518445312351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37608564882877678963541567 56412847324316518445312351)
    ·
      refine ⟨84619270986474777667968527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56412847324316518445312351 84619270986474777667968527)
      ·
        refine ⟨126928906479712166501952791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84619270986474777667968527 126928906479712166501952791)
        ·
          refine ⟨190393359719568249752929187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126928906479712166501952791 190393359719568249752929187)
          ·
            refine ⟨285590039579352374629393781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190393359719568249752929187 285590039579352374629393781)
            ·
              refine ⟨26774066210564285121505667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285590039579352374629393781 26774066210564285121505667)
              ·
                refine ⟨40161099315846427682258501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26774066210564285121505667 40161099315846427682258501)
                ·
                  refine ⟨7530206121721205190423469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40161099315846427682258501 7530206121721205190423469)
                  ·
                    refine ⟨2823827295645451946408801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7530206121721205190423469 2823827295645451946408801)
                    ·
                      refine ⟨2117870471734088959806601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823827295645451946408801 2117870471734088959806601)
                      ·
                        rfl

theorem cell23_4124538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_4124538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124538 prefixEnd_4124538 := by exact prefixLift 4124538
  have htrace : WordTrace (prefixWord ++ tailWord_4124538) baseStart_4124538 baseEnd_4124538 := by
    simpa [prefixWord, tailWord_4124538, baseEnd_4124538] using wordTrace_append hprefix tailTrace_4124538
  have hstable : (prefixWord ++ tailWord_4124538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124538).length < 2 ^ (prefixWord ++ tailWord_4124538).sum := by decide
  have hdescent : baseEnd_4124538 < baseStart_4124538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124552 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 6]
def baseStart_4124552 : Nat := 118140960795 + 4124552 * 2 ^ 59
def prefixEnd_4124552 : Nat := 4983230072969 + 3 ^ 40 * 4124552 * 2
def baseEnd_4124552 : Nat := 235319740051472433892393

theorem tailTrace_4124552 : CollatzResearch.WordTrace tailWord_4124552 prefixEnd_4124552 235319740051472433892393 := by
  unfold tailWord_4124552
  simp only [CollatzResearch.WordTrace]
  refine ⟨75217385076729998122587955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100289846768973330830117273 75217385076729998122587955)
  ·
    refine ⟨112826077615094997183881933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75217385076729998122587955 112826077615094997183881933)
    ·
      refine ⟨42309779105660623943955725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112826077615094997183881933 42309779105660623943955725)
      ·
        refine ⟨15866167164622733978983397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42309779105660623943955725 15866167164622733978983397)
        ·
          refine ⟨2974906343366762621059387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15866167164622733978983397 2974906343366762621059387)
          ·
            refine ⟨4462359515050143931589081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974906343366762621059387 4462359515050143931589081)
            ·
              refine ⟨3346769636287607948691811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4462359515050143931589081 3346769636287607948691811)
              ·
                refine ⟨5020154454431411923037717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3346769636287607948691811 5020154454431411923037717)
                ·
                  refine ⟨235319740051472433892393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5020154454431411923037717 235319740051472433892393)
                  ·
                    rfl

theorem cell23_4124552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 6].length) (baseStart_4124552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124552 prefixEnd_4124552 := by exact prefixLift 4124552
  have htrace : WordTrace (prefixWord ++ tailWord_4124552) baseStart_4124552 baseEnd_4124552 := by
    simpa [prefixWord, tailWord_4124552, baseEnd_4124552] using wordTrace_append hprefix tailTrace_4124552
  have hstable : (prefixWord ++ tailWord_4124552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124552).length < 2 ^ (prefixWord ++ tailWord_4124552).sum := by decide
  have hdescent : baseEnd_4124552 < baseStart_4124552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124572 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_4124572 : Nat := 118140960795 + 4124572 * 2 ^ 59
def prefixEnd_4124572 : Nat := 4983230072969 + 3 ^ 40 * 4124572 * 2
def baseEnd_4124572 : Nat := 2117887930076341826781445

theorem tailTrace_4124572 : CollatzResearch.WordTrace tailWord_4124572 prefixEnd_4124572 2117887930076341826781445 := by
  unfold tailWord_4124572
  simp only [CollatzResearch.WordTrace]
  refine ⟨75217749806693769830451985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100290333075591693107269313 75217749806693769830451985)
  ·
    refine ⟨56413312355020327372838989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75217749806693769830451985 56413312355020327372838989)
    ·
      refine ⟨21154992133132622764814621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56413312355020327372838989 21154992133132622764814621)
      ·
        refine ⟨7933122049924733536805483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21154992133132622764814621 7933122049924733536805483)
        ·
          refine ⟨11899683074887100305208225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7933122049924733536805483 11899683074887100305208225)
          ·
            refine ⟨8924762306165325228906169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11899683074887100305208225 8924762306165325228906169)
            ·
              refine ⟨6693571729623993921679627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8924762306165325228906169 6693571729623993921679627)
              ·
                refine ⟨10040357594435990882519441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6693571729623993921679627 10040357594435990882519441)
                ·
                  refine ⟨7530268195826993161889581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10040357594435990882519441 7530268195826993161889581)
                  ·
                    refine ⟨2823850573435122435708593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7530268195826993161889581 2823850573435122435708593)
                    ·
                      refine ⟨2117887930076341826781445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823850573435122435708593 2117887930076341826781445)
                      ·
                        rfl

theorem cell23_4124572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_4124572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124572 prefixEnd_4124572 := by exact prefixLift 4124572
  have htrace : WordTrace (prefixWord ++ tailWord_4124572) baseStart_4124572 baseEnd_4124572 := by
    simpa [prefixWord, tailWord_4124572, baseEnd_4124572] using wordTrace_append hprefix tailTrace_4124572
  have hstable : (prefixWord ++ tailWord_4124572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124572).length < 2 ^ (prefixWord ++ tailWord_4124572).sum := by decide
  have hdescent : baseEnd_4124572 < baseStart_4124572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124590 : List Nat := [4, 1, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_4124590 : Nat := 118140960795 + 4124590 * 2 ^ 59
def prefixEnd_4124590 : Nat := 4983230072969 + 3 ^ 40 * 4124590 * 2
def baseEnd_4124590 : Nat := 705965724242707585452121

theorem tailTrace_4124590 : CollatzResearch.WordTrace tailWord_4124590 prefixEnd_4124590 705965724242707585452121 := by
  unfold tailWord_4124590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18804519515915291091882403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100290770751548219156706149 18804519515915291091882403)
  ·
    refine ⟨28206779273872936637823605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18804519515915291091882403 28206779273872936637823605)
    ·
      refine ⟨2644385556925587809795963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28206779273872936637823605 2644385556925587809795963)
      ·
        refine ⟨3966578335388381714693945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644385556925587809795963 3966578335388381714693945)
        ·
          refine ⟨2974933751541286286020459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3966578335388381714693945 2974933751541286286020459)
          ·
            refine ⟨4462400627311929429030689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974933751541286286020459 4462400627311929429030689)
            ·
              refine ⟨3346800470483947071773017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4462400627311929429030689 3346800470483947071773017)
              ·
                refine ⟨2510100352862960303829763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3346800470483947071773017 2510100352862960303829763)
                ·
                  refine ⟨3765150529294440455744645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510100352862960303829763 3765150529294440455744645)
                  ·
                    refine ⟨705965724242707585452121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3765150529294440455744645 705965724242707585452121)
                    ·
                      rfl

theorem cell23_4124590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_4124590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124590 prefixEnd_4124590 := by exact prefixLift 4124590
  have htrace : WordTrace (prefixWord ++ tailWord_4124590) baseStart_4124590 baseEnd_4124590 := by
    simpa [prefixWord, tailWord_4124590, baseEnd_4124590] using wordTrace_append hprefix tailTrace_4124590
  have hstable : (prefixWord ++ tailWord_4124590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124590).length < 2 ^ (prefixWord ++ tailWord_4124590).sum := by decide
  have hdescent : baseEnd_4124590 < baseStart_4124590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124596 : List Nat := [2, 5, 2, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_4124596 : Nat := 118140960795 + 4124596 * 2 ^ 59
def prefixEnd_4124596 : Nat := 4983230072969 + 3 ^ 40 * 4124596 * 2
def baseEnd_4124596 : Nat := 2117900253612049732881335

theorem tailTrace_4124596 : CollatzResearch.WordTrace tailWord_4124596 prefixEnd_4124596 2117900253612049732881335 := by
  unfold tailWord_4124596
  simp only [CollatzResearch.WordTrace]
  refine ⟨75218187482650295879888821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100290916643533727839851761 75218187482650295879888821)
  ·
    refine ⟨7051705076498465238739577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75218187482650295879888821 7051705076498465238739577)
    ·
      refine ⟨5288778807373848929054683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7051705076498465238739577 5288778807373848929054683)
      ·
        refine ⟨7933168211060773393582025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5288778807373848929054683 7933168211060773393582025)
        ·
          refine ⟨5949876158295580045186519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7933168211060773393582025 5949876158295580045186519)
          ·
            refine ⟨8924814237443370067779779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949876158295580045186519 8924814237443370067779779)
            ·
              refine ⟨13387221356165055101669669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8924814237443370067779779 13387221356165055101669669)
              ·
                refine ⟨2510104004280947831563063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13387221356165055101669669 2510104004280947831563063)
                ·
                  refine ⟨3765156006421421747344595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510104004280947831563063 3765156006421421747344595)
                  ·
                    refine ⟨5647734009632132621016893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3765156006421421747344595 5647734009632132621016893)
                    ·
                      refine ⟨2117900253612049732881335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5647734009632132621016893 2117900253612049732881335)
                      ·
                        rfl

theorem cell23_4124596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_4124596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124596 prefixEnd_4124596 := by exact prefixLift 4124596
  have htrace : WordTrace (prefixWord ++ tailWord_4124596) baseStart_4124596 baseEnd_4124596 := by
    simpa [prefixWord, tailWord_4124596, baseEnd_4124596] using wordTrace_append hprefix tailTrace_4124596
  have hstable : (prefixWord ++ tailWord_4124596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124596).length < 2 ^ (prefixWord ++ tailWord_4124596).sum := by decide
  have hdescent : baseEnd_4124596 < baseStart_4124596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124618 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_4124618 : Nat := 118140960795 + 4124618 * 2 ^ 59
def prefixEnd_4124618 : Nat := 4983230072969 + 3 ^ 40 * 4124618 * 2
def baseEnd_4124618 : Nat := 2117911550186448646806233

theorem tailTrace_4124618 : CollatzResearch.WordTrace tailWord_4124618 prefixEnd_4124618 2117911550186448646806233 := by
  unfold tailWord_4124618
  simp only [CollatzResearch.WordTrace]
  refine ⟨37609294342805222379269627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100291451580813926344719005 37609294342805222379269627)
  ·
    refine ⟨56413941514207833568904441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37609294342805222379269627 56413941514207833568904441)
    ·
      refine ⟨42310456135655875176678331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56413941514207833568904441 42310456135655875176678331)
      ·
        refine ⟨63465684203483812765017497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42310456135655875176678331 63465684203483812765017497)
        ·
          refine ⟨47599263152612859573763123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63465684203483812765017497 47599263152612859573763123)
          ·
            refine ⟨71398894728919289360644685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47599263152612859573763123 71398894728919289360644685)
            ·
              refine ⟨26774585523344733510241757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71398894728919289360644685 26774585523344733510241757)
              ·
                refine ⟨10040469571254275066340659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26774585523344733510241757 10040469571254275066340659)
                ·
                  refine ⟨15060704356881412599510989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10040469571254275066340659 15060704356881412599510989)
                  ·
                    refine ⟨5647764133830529724816621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15060704356881412599510989 5647764133830529724816621)
                    ·
                      refine ⟨2117911550186448646806233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5647764133830529724816621 2117911550186448646806233)
                      ·
                        rfl

theorem cell23_4124618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_4124618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124618 prefixEnd_4124618 := by exact prefixLift 4124618
  have htrace : WordTrace (prefixWord ++ tailWord_4124618) baseStart_4124618 baseEnd_4124618 := by
    simpa [prefixWord, tailWord_4124618, baseEnd_4124618] using wordTrace_append hprefix tailTrace_4124618
  have hstable : (prefixWord ++ tailWord_4124618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124618).length < 2 ^ (prefixWord ++ tailWord_4124618).sum := by decide
  have hdescent : baseEnd_4124618 < baseStart_4124618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124631 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_4124631 : Nat := 118140960795 + 4124631 * 2 ^ 59
def prefixEnd_4124631 : Nat := 4983230072969 + 3 ^ 40 * 4124631 * 2
def baseEnd_4124631 : Nat := 2117918225434957095943673

theorem tailTrace_4124631 : CollatzResearch.WordTrace tailWord_4124631 prefixEnd_4124631 2117918225434957095943673 := by
  unfold tailWord_4124631
  simp only [CollatzResearch.WordTrace]
  refine ⟨150437651520173792737301747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100291767680115861824867831 150437651520173792737301747)
  ·
    refine ⟨225656477280260689105952621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150437651520173792737301747 225656477280260689105952621)
    ·
      refine ⟨84621178980097758414732233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225656477280260689105952621 84621178980097758414732233)
      ·
        refine ⟨63465884235073318811049175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84621178980097758414732233 63465884235073318811049175)
        ·
          refine ⟨95198826352609978216573763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63465884235073318811049175 95198826352609978216573763)
          ·
            refine ⟨142798239528914967324860645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95198826352609978216573763 142798239528914967324860645)
            ·
              refine ⟨26774669911671556373411371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142798239528914967324860645 26774669911671556373411371)
              ·
                refine ⟨40162004867507334560117057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26774669911671556373411371 40162004867507334560117057)
                ·
                  refine ⟨30121503650630500920087793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40162004867507334560117057 30121503650630500920087793)
                  ·
                    refine ⟨22591127737972875690065845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30121503650630500920087793 22591127737972875690065845)
                    ·
                      refine ⟨2117918225434957095943673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22591127737972875690065845 2117918225434957095943673)
                      ·
                        rfl

theorem cell23_4124631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_4124631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124631 prefixEnd_4124631 := by exact prefixLift 4124631
  have htrace : WordTrace (prefixWord ++ tailWord_4124631) baseStart_4124631 baseEnd_4124631 := by
    simpa [prefixWord, tailWord_4124631, baseEnd_4124631] using wordTrace_append hprefix tailTrace_4124631
  have hstable : (prefixWord ++ tailWord_4124631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124631).length < 2 ^ (prefixWord ++ tailWord_4124631).sum := by decide
  have hdescent : baseEnd_4124631 < baseStart_4124631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124695 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4124695 : Nat := 118140960795 + 4124695 * 2 ^ 59
def prefixEnd_4124695 : Nat := 4983230072969 + 3 ^ 40 * 4124695 * 2
def baseEnd_4124695 : Nat := 2117951088196844845543379

theorem tailTrace_4124695 : CollatzResearch.WordTrace tailWord_4124695 prefixEnd_4124695 2117951088196844845543379 := by
  unfold tailWord_4124695
  simp only [CollatzResearch.WordTrace]
  refine ⟨150439985791941931667631539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100293323861294621111754359 150439985791941931667631539)
  ·
    refine ⟨225659978687912897501447309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150439985791941931667631539 225659978687912897501447309)
    ·
      refine ⟨84622492007967336563042741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225659978687912897501447309 84622492007967336563042741)
      ·
        refine ⟨7933358625746937802785257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84622492007967336563042741 7933358625746937802785257)
        ·
          refine ⟨5950018969310203352088943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7933358625746937802785257 5950018969310203352088943)
          ·
            refine ⟨8925028453965305028133415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5950018969310203352088943 8925028453965305028133415)
            ·
              refine ⟨13387542680947957542200123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925028453965305028133415 13387542680947957542200123)
              ·
                refine ⟨20081314021421936313300185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13387542680947957542200123 20081314021421936313300185)
                ·
                  refine ⟨15060985516066452234975139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20081314021421936313300185 15060985516066452234975139)
                  ·
                    refine ⟨22591478274099678352462709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15060985516066452234975139 22591478274099678352462709)
                    ·
                      refine ⟨2117951088196844845543379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22591478274099678352462709 2117951088196844845543379)
                      ·
                        rfl

theorem cell23_4124695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4124695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124695 prefixEnd_4124695 := by exact prefixLift 4124695
  have htrace : WordTrace (prefixWord ++ tailWord_4124695) baseStart_4124695 baseEnd_4124695 := by
    simpa [prefixWord, tailWord_4124695, baseEnd_4124695] using wordTrace_append hprefix tailTrace_4124695
  have hstable : (prefixWord ++ tailWord_4124695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124695).length < 2 ^ (prefixWord ++ tailWord_4124695).sum := by decide
  have hdescent : baseEnd_4124695 < baseStart_4124695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124748 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_4124748 : Nat := 118140960795 + 4124748 * 2 ^ 59
def prefixEnd_4124748 : Nat := 4983230072969 + 3 ^ 40 * 4124748 * 2
def baseEnd_4124748 : Nat := 2117978302671533138180635

theorem tailTrace_4124748 : CollatzResearch.WordTrace tailWord_4124748 prefixEnd_4124748 2117978302671533138180635 := by
  unfold tailWord_4124748
  simp only [CollatzResearch.WordTrace]
  refine ⟨75220959430374960859655449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100294612573833281146207265 75220959430374960859655449)
  ·
    refine ⟨56415719572781220644741587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75220959430374960859655449 56415719572781220644741587)
    ·
      refine ⟨84623579359171830967112381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56415719572781220644741587 84623579359171830967112381)
      ·
        refine ⟨31733842259689436612667143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84623579359171830967112381 31733842259689436612667143)
        ·
          refine ⟨47600763389534154919000715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31733842259689436612667143 47600763389534154919000715)
          ·
            refine ⟨71401145084301232378501073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47600763389534154919000715 71401145084301232378501073)
            ·
              refine ⟨53550858813225924283875805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71401145084301232378501073 53550858813225924283875805)
              ·
                refine ⟨20081572054959721606453427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53550858813225924283875805 20081572054959721606453427)
                ·
                  refine ⟨30122358082439582409680141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20081572054959721606453427 30122358082439582409680141)
                  ·
                    refine ⟨11295884280914843403630053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30122358082439582409680141 11295884280914843403630053)
                    ·
                      refine ⟨2117978302671533138180635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11295884280914843403630053 2117978302671533138180635)
                      ·
                        rfl

theorem cell23_4124748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_4124748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124748 prefixEnd_4124748 := by exact prefixLift 4124748
  have htrace : WordTrace (prefixWord ++ tailWord_4124748) baseStart_4124748 baseEnd_4124748 := by
    simpa [prefixWord, tailWord_4124748, baseEnd_4124748] using wordTrace_append hprefix tailTrace_4124748
  have hstable : (prefixWord ++ tailWord_4124748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124748).length < 2 ^ (prefixWord ++ tailWord_4124748).sum := by decide
  have hdescent : baseEnd_4124748 < baseStart_4124748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124766 : List Nat := [4, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_4124766 : Nat := 118140960795 + 4124766 * 2 ^ 59
def prefixEnd_4124766 : Nat := 4983230072969 + 3 ^ 40 * 4124766 * 2
def baseEnd_4124766 : Nat := 235331949480368229750617

theorem tailTrace_4124766 : CollatzResearch.WordTrace tailWord_4124766 prefixEnd_4124766 235331949480368229750617 := by
  unfold tailWord_4124766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18805321921835588849183269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100295050249789807195644101 18805321921835588849183269)
  ·
    refine ⟨3525997860344172909221863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18805321921835588849183269 3525997860344172909221863)
    ·
      refine ⟨5288996790516259363832795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3525997860344172909221863 5288996790516259363832795)
      ·
        refine ⟨7933495185774389045749193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5288996790516259363832795 7933495185774389045749193)
        ·
          refine ⟨5950121389330791784311895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7933495185774389045749193 5950121389330791784311895)
          ·
            refine ⟨8925182083996187676467843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5950121389330791784311895 8925182083996187676467843)
            ·
              refine ⟨13387773125994281514701765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925182083996187676467843 13387773125994281514701765)
              ·
                refine ⟨2510207461123927784006581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13387773125994281514701765 2510207461123927784006581)
                ·
                  refine ⟨235331949480368229750617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2510207461123927784006581 235331949480368229750617)
                  ·
                    rfl

theorem cell23_4124766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_4124766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124766 prefixEnd_4124766 := by exact prefixLift 4124766
  have htrace : WordTrace (prefixWord ++ tailWord_4124766) baseStart_4124766 baseEnd_4124766 := by
    simpa [prefixWord, tailWord_4124766, baseEnd_4124766] using wordTrace_append hprefix tailTrace_4124766
  have hstable : (prefixWord ++ tailWord_4124766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124766).length < 2 ^ (prefixWord ++ tailWord_4124766).sum := by decide
  have hdescent : baseEnd_4124766 < baseStart_4124766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124775 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 3, 4]
def baseStart_4124775 : Nat := 118140960795 + 4124775 * 2 ^ 59
def prefixEnd_4124775 : Nat := 4983230072969 + 3 ^ 40 * 4124775 * 2
def baseEnd_4124775 : Nat := 705997388883068177514337

theorem tailTrace_4124775 : CollatzResearch.WordTrace tailWord_4124775 prefixEnd_4124775 705997388883068177514337 := by
  unfold tailWord_4124775
  simp only [CollatzResearch.WordTrace]
  refine ⟨150442903631652105330543779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100295269087768070220362519 150442903631652105330543779)
  ·
    refine ⟨225664355447478157995815669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150442903631652105330543779 225664355447478157995815669)
    ·
      refine ⟨21156033323201077312107719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225664355447478157995815669 21156033323201077312107719)
      ·
        refine ⟨31734049984801615968161579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21156033323201077312107719 31734049984801615968161579)
        ·
          refine ⟨47601074977202423952242369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31734049984801615968161579 47601074977202423952242369)
          ·
            refine ⟨35700806232901817964181777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47601074977202423952242369 35700806232901817964181777)
            ·
              refine ⟨26775604674676363473136333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35700806232901817964181777 26775604674676363473136333)
              ·
                refine ⟨10040851753003636302426125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26775604674676363473136333 10040851753003636302426125)
                ·
                  refine ⟨3765319407376363613409797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10040851753003636302426125 3765319407376363613409797)
                  ·
                    refine ⟨705997388883068177514337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3765319407376363613409797 705997388883068177514337)
                    ·
                      rfl

theorem cell23_4124775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_4124775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124775 prefixEnd_4124775 := by exact prefixLift 4124775
  have htrace : WordTrace (prefixWord ++ tailWord_4124775) baseStart_4124775 baseEnd_4124775 := by
    simpa [prefixWord, tailWord_4124775, baseEnd_4124775] using wordTrace_append hprefix tailTrace_4124775
  have hstable : (prefixWord ++ tailWord_4124775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124775).length < 2 ^ (prefixWord ++ tailWord_4124775).sum := by decide
  have hdescent : baseEnd_4124775 < baseStart_4124775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124782 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_4124782 : Nat := 118140960795 + 4124782 * 2 ^ 59
def prefixEnd_4124782 : Nat := 4983230072969 + 3 ^ 40 * 4124782 * 2
def baseEnd_4124782 : Nat := 2117995761013786005155479

theorem tailTrace_4124782 : CollatzResearch.WordTrace tailWord_4124782 prefixEnd_4124782 2117995761013786005155479 := by
  unfold tailWord_4124782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18805394867828343190756075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100295439295084497017365733 18805394867828343190756075)
  ·
    refine ⟨28208092301742514786134113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18805394867828343190756075 28208092301742514786134113)
    ·
      refine ⟨21156069226306886089600585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28208092301742514786134113 21156069226306886089600585)
      ·
        refine ⟨15867051919730164567200439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21156069226306886089600585 15867051919730164567200439)
        ·
          refine ⟨23800577879595246850800659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15867051919730164567200439 23800577879595246850800659)
          ·
            refine ⟨35700866819392870276200989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23800577879595246850800659 35700866819392870276200989)
            ·
              refine ⟨13387825057272326353575371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35700866819392870276200989 13387825057272326353575371)
              ·
                refine ⟨20081737585908489530363057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13387825057272326353575371 20081737585908489530363057)
                ·
                  refine ⟨15061303189431367147772293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20081737585908489530363057 15061303189431367147772293)
                  ·
                    refine ⟨2823994348018381340207305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15061303189431367147772293 2823994348018381340207305)
                    ·
                      refine ⟨2117995761013786005155479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2823994348018381340207305 2117995761013786005155479)
                      ·
                        rfl

theorem cell23_4124782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_4124782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124782 prefixEnd_4124782 := by exact prefixLift 4124782
  have htrace : WordTrace (prefixWord ++ tailWord_4124782) baseStart_4124782 baseEnd_4124782 := by
    simpa [prefixWord, tailWord_4124782, baseEnd_4124782] using wordTrace_append hprefix tailTrace_4124782
  have hstable : (prefixWord ++ tailWord_4124782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124782).length < 2 ^ (prefixWord ++ tailWord_4124782).sum := by decide
  have hdescent : baseEnd_4124782 < baseStart_4124782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124832 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 3, 1, 3]
def baseStart_4124832 : Nat := 118140960795 + 4124832 * 2 ^ 59
def prefixEnd_4124832 : Nat := 4983230072969 + 3 ^ 40 * 4124832 * 2
def baseEnd_4124832 : Nat := 2118021435046510809530249

theorem tailTrace_4124832 : CollatzResearch.WordTrace tailWord_4124832 prefixEnd_4124832 2118021435046510809530249 := by
  unfold tailWord_4124832
  simp only [CollatzResearch.WordTrace]
  refine ⟨75222491296222802032684375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100296655061630402710245833 75222491296222802032684375)
  ·
    refine ⟨112833736944334203049026563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75222491296222802032684375 112833736944334203049026563)
    ·
      refine ⟨169250605416501304573539845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112833736944334203049026563 169250605416501304573539845)
      ·
        refine ⟨31734488515593994607538721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169250605416501304573539845 31734488515593994607538721)
        ·
          refine ⟨23800866386695495955654041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31734488515593994607538721 23800866386695495955654041)
          ·
            refine ⟨17850649790021621966740531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23800866386695495955654041 17850649790021621966740531)
            ·
              refine ⟨26775974685032432950110797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17850649790021621966740531 26775974685032432950110797)
              ·
                refine ⟨10040990506887162356291549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26775974685032432950110797 10040990506887162356291549)
                ·
                  refine ⟨3765371440082685883609331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10040990506887162356291549 3765371440082685883609331)
                  ·
                    refine ⟨5648057160124028825413997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3765371440082685883609331 5648057160124028825413997)
                    ·
                      refine ⟨2118021435046510809530249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5648057160124028825413997 2118021435046510809530249)
                      ·
                        rfl

theorem cell23_4124832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_4124832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124832 prefixEnd_4124832 := by exact prefixLift 4124832
  have htrace : WordTrace (prefixWord ++ tailWord_4124832) baseStart_4124832 baseEnd_4124832 := by
    simpa [prefixWord, tailWord_4124832, baseEnd_4124832] using wordTrace_append hprefix tailTrace_4124832
  have hstable : (prefixWord ++ tailWord_4124832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124832).length < 2 ^ (prefixWord ++ tailWord_4124832).sum := by decide
  have hdescent : baseEnd_4124832 < baseStart_4124832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124839 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 6]
def baseStart_4124839 : Nat := 118140960795 + 4124839 * 2 ^ 59
def prefixEnd_4124839 : Nat := 4983230072969 + 3 ^ 40 * 4124839 * 2
def baseEnd_4124839 : Nat := 235336114379010253571413

theorem tailTrace_4124839 : CollatzResearch.WordTrace tailWord_4124839 prefixEnd_4124839 235336114379010253571413 := by
  unfold tailWord_4124839
  simp only [CollatzResearch.WordTrace]
  refine ⟨150445237903420244260873571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100296825268946829507249047 150445237903420244260873571)
  ·
    refine ⟨225667856855130366391310357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150445237903420244260873571 225667856855130366391310357)
    ·
      refine ⟨10578180790084235924592673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 225667856855130366391310357 10578180790084235924592673)
      ·
        refine ⟨7933635592563176943444505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10578180790084235924592673 7933635592563176943444505)
        ·
          refine ⟨5950226694422382707583379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7933635592563176943444505 5950226694422382707583379)
          ·
            refine ⟨8925340041633574061375069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5950226694422382707583379 8925340041633574061375069)
            ·
              refine ⟨3347002515612590273015651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8925340041633574061375069 3347002515612590273015651)
              ·
                refine ⟨5020503773418885409523477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347002515612590273015651 5020503773418885409523477)
                ·
                  refine ⟨235336114379010253571413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5020503773418885409523477 235336114379010253571413)
                  ·
                    rfl

theorem cell23_4124839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 6].length) (baseStart_4124839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124839 prefixEnd_4124839 := by exact prefixLift 4124839
  have htrace : WordTrace (prefixWord ++ tailWord_4124839) baseStart_4124839 baseEnd_4124839 := by
    simpa [prefixWord, tailWord_4124839, baseEnd_4124839] using wordTrace_append hprefix tailTrace_4124839
  have hstable : (prefixWord ++ tailWord_4124839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124839).length < 2 ^ (prefixWord ++ tailWord_4124839).sum := by decide
  have hdescent : baseEnd_4124839 < baseStart_4124839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124875 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 5]
def baseStart_4124875 : Nat := 118140960795 + 4124875 * 2 ^ 59
def prefixEnd_4124875 : Nat := 4983230072969 + 3 ^ 40 * 4124875 * 2
def baseEnd_4124875 : Nat := 2118043514714654141292551

theorem tailTrace_4124875 : CollatzResearch.WordTrace tailWord_4124875 prefixEnd_4124875 2118043514714654141292551 := by
  unfold tailWord_4124875
  simp only [CollatzResearch.WordTrace]
  refine ⟨150446550931289822409184079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100297700620859881606122719 150446550931289822409184079)
  ·
    refine ⟨225669826396934733613776119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150446550931289822409184079 225669826396934733613776119)
    ·
      refine ⟨338504739595402100420664179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225669826396934733613776119 338504739595402100420664179)
      ·
        refine ⟨507757109393103150630996269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338504739595402100420664179 507757109393103150630996269)
        ·
          refine ⟨190408916022413681486623601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507757109393103150630996269 190408916022413681486623601)
          ·
            refine ⟨142806687016810261114967701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190408916022413681486623601 142806687016810261114967701)
            ·
              refine ⟨6694063453912980989764111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142806687016810261114967701 6694063453912980989764111)
              ·
                refine ⟨10041095180869471484646167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6694063453912980989764111 10041095180869471484646167)
                ·
                  refine ⟨15061642771304207226969251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10041095180869471484646167 15061642771304207226969251)
                  ·
                    refine ⟨22592464156956310840453877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15061642771304207226969251 22592464156956310840453877)
                    ·
                      refine ⟨2118043514714654141292551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22592464156956310840453877 2118043514714654141292551)
                      ·
                        rfl

theorem cell23_4124875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 5].length) (baseStart_4124875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124875 prefixEnd_4124875 := by exact prefixLift 4124875
  have htrace : WordTrace (prefixWord ++ tailWord_4124875) baseStart_4124875 baseEnd_4124875 := by
    simpa [prefixWord, tailWord_4124875, baseEnd_4124875] using wordTrace_append hprefix tailTrace_4124875
  have hstable : (prefixWord ++ tailWord_4124875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124875).length < 2 ^ (prefixWord ++ tailWord_4124875).sum := by decide
  have hdescent : baseEnd_4124875 < baseStart_4124875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124876 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4124876 : Nat := 118140960795 + 4124876 * 2 ^ 59
def prefixEnd_4124876 : Nat := 4983230072969 + 3 ^ 40 * 4124876 * 2
def baseEnd_4124876 : Nat := 2118044028195308637380047

theorem tailTrace_4124876 : CollatzResearch.WordTrace tailWord_4124876 prefixEnd_4124876 2118044028195308637380047 := by
  unfold tailWord_4124876
  simp only [CollatzResearch.WordTrace]
  refine ⟨75223293702143099789985241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100297724936190799719980321 75223293702143099789985241)
  ·
    refine ⟨56417470276607324842488931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75223293702143099789985241 56417470276607324842488931)
    ·
      refine ⟨84626205414910987263733397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56417470276607324842488931 84626205414910987263733397)
      ·
        refine ⟨3966853378823952527987503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84626205414910987263733397 3966853378823952527987503)
        ·
          refine ⟨5950280068235928791981255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3966853378823952527987503 5950280068235928791981255)
          ·
            refine ⟨8925420102353893187971883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5950280068235928791981255 8925420102353893187971883)
            ·
              refine ⟨13388130153530839781957825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925420102353893187971883 13388130153530839781957825)
              ·
                refine ⟨10041097615148129836468369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13388130153530839781957825 10041097615148129836468369)
                ·
                  refine ⟨7530823211361097377351277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10041097615148129836468369 7530823211361097377351277)
                  ·
                    refine ⟨2824058704260411516506729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7530823211361097377351277 2824058704260411516506729)
                    ·
                      refine ⟨2118044028195308637380047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824058704260411516506729 2118044028195308637380047)
                      ·
                        rfl

theorem cell23_4124876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4124876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124876 prefixEnd_4124876 := by exact prefixLift 4124876
  have htrace : WordTrace (prefixWord ++ tailWord_4124876) baseStart_4124876 baseEnd_4124876 := by
    simpa [prefixWord, tailWord_4124876, baseEnd_4124876] using wordTrace_append hprefix tailTrace_4124876
  have hstable : (prefixWord ++ tailWord_4124876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124876).length < 2 ^ (prefixWord ++ tailWord_4124876).sum := by decide
  have hdescent : baseEnd_4124876 < baseStart_4124876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124882 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_4124882 : Nat := 118140960795 + 4124882 * 2 ^ 59
def prefixEnd_4124882 : Nat := 4983230072969 + 3 ^ 40 * 4124882 * 2
def baseEnd_4124882 : Nat := 706015703026411871301673

theorem tailTrace_4124882 : CollatzResearch.WordTrace tailWord_4124882 prefixEnd_4124882 706015703026411871301673 := by
  unfold tailWord_4124882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37611701560566115651172225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100297870828176308403125933 37611701560566115651172225)
  ·
    refine ⟨28208776170424586738379169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37611701560566115651172225 28208776170424586738379169)
    ·
      refine ⟨21156582127818440053784377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28208776170424586738379169 21156582127818440053784377)
      ·
        refine ⟨15867436595863830040338283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21156582127818440053784377 15867436595863830040338283)
        ·
          refine ⟨23801154893795745060507425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15867436595863830040338283 23801154893795745060507425)
          ·
            refine ⟨17850866170346808795380569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23801154893795745060507425 17850866170346808795380569)
            ·
              refine ⟨13388149627760106596535427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17850866170346808795380569 13388149627760106596535427)
              ·
                refine ⟨20082224441640159894803141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13388149627760106596535427 20082224441640159894803141)
                ·
                  refine ⟨3765417082807529980275589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20082224441640159894803141 3765417082807529980275589)
                  ·
                    refine ⟨706015703026411871301673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3765417082807529980275589 706015703026411871301673)
                    ·
                      rfl

theorem cell23_4124882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_4124882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124882 prefixEnd_4124882 := by exact prefixLift 4124882
  have htrace : WordTrace (prefixWord ++ tailWord_4124882) baseStart_4124882 baseEnd_4124882 := by
    simpa [prefixWord, tailWord_4124882, baseEnd_4124882] using wordTrace_append hprefix tailTrace_4124882
  have hstable : (prefixWord ++ tailWord_4124882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124882).length < 2 ^ (prefixWord ++ tailWord_4124882).sum := by decide
  have hdescent : baseEnd_4124882 < baseStart_4124882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124889 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 3, 2, 2]
def baseStart_4124889 : Nat := 118140960795 + 4124889 * 2 ^ 59
def prefixEnd_4124889 : Nat := 4983230072969 + 3 ^ 40 * 4124889 * 2
def baseEnd_4124889 : Nat := 2118050703443817086517487

theorem tailTrace_4124889 : CollatzResearch.WordTrace tailWord_4124889 prefixEnd_4124889 2118050703443817086517487 := by
  unfold tailWord_4124889
  simp only [CollatzResearch.WordTrace]
  refine ⟨150447061553239102800193721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100298041035492735200129147 150447061553239102800193721)
  ·
    refine ⟨112835296164929327100145291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150447061553239102800193721 112835296164929327100145291)
    ·
      refine ⟨169252944247393990650217937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112835296164929327100145291 169252944247393990650217937)
      ·
        refine ⟨126939708185545492987663453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169252944247393990650217937 126939708185545492987663453)
        ·
          refine ⟨47602390569579559870373795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126939708185545492987663453 47602390569579559870373795)
          ·
            refine ⟨71403585854369339805560693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47602390569579559870373795 71403585854369339805560693)
            ·
              refine ⟨6694086173847125606771315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71403585854369339805560693 6694086173847125606771315)
              ·
                refine ⟨10041129260770688410156973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6694086173847125606771315 10041129260770688410156973)
                ·
                  refine ⟨3765423472789008153808865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10041129260770688410156973 3765423472789008153808865)
                  ·
                    refine ⟨2824067604591756115356649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3765423472789008153808865 2824067604591756115356649)
                    ·
                      refine ⟨2118050703443817086517487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824067604591756115356649 2118050703443817086517487)
                      ·
                        rfl

theorem cell23_4124889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_4124889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124889 prefixEnd_4124889 := by exact prefixLift 4124889
  have htrace : WordTrace (prefixWord ++ tailWord_4124889) baseStart_4124889 baseEnd_4124889 := by
    simpa [prefixWord, tailWord_4124889, baseEnd_4124889] using wordTrace_append hprefix tailTrace_4124889
  have hstable : (prefixWord ++ tailWord_4124889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124889).length < 2 ^ (prefixWord ++ tailWord_4124889).sum := by decide
  have hdescent : baseEnd_4124889 < baseStart_4124889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124909 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_4124909 : Nat := 118140960795 + 4124909 * 2 ^ 59
def prefixEnd_4124909 : Nat := 4983230072969 + 3 ^ 40 * 4124909 * 2
def baseEnd_4124909 : Nat := 2118060973056907008267395

theorem tailTrace_4124909 : CollatzResearch.WordTrace tailWord_4124909 prefixEnd_4124909 2118060973056907008267395 := by
  unfold tailWord_4124909
  simp only [CollatzResearch.WordTrace]
  refine ⟨150447791013166646215921781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100298527342111097477281187 150447791013166646215921781)
  ·
    refine ⟨14104480407484373082742667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150447791013166646215921781 14104480407484373082742667)
    ·
      refine ⟨21156720611226559624114001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14104480407484373082742667 21156720611226559624114001)
      ·
        refine ⟨15867540458419919718085501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21156720611226559624114001 15867540458419919718085501)
        ·
          refine ⟨5950327671907469894282063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15867540458419919718085501 5950327671907469894282063)
          ·
            refine ⟨8925491507861204841423095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5950327671907469894282063 8925491507861204841423095)
            ·
              refine ⟨13388237261791807262134643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925491507861204841423095 13388237261791807262134643)
              ·
                refine ⟨20082355892687710893201965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13388237261791807262134643 20082355892687710893201965)
                ·
                  refine ⟨7530883459757891584950737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20082355892687710893201965 7530883459757891584950737)
                  ·
                    refine ⟨5648162594818418688713053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7530883459757891584950737 5648162594818418688713053)
                    ·
                      refine ⟨2118060973056907008267395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5648162594818418688713053 2118060973056907008267395)
                      ·
                        rfl

theorem cell23_4124909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_4124909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124909 prefixEnd_4124909 := by exact prefixLift 4124909
  have htrace : WordTrace (prefixWord ++ tailWord_4124909) baseStart_4124909 baseEnd_4124909 := by
    simpa [prefixWord, tailWord_4124909, baseEnd_4124909] using wordTrace_append hprefix tailTrace_4124909
  have hstable : (prefixWord ++ tailWord_4124909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124909).length < 2 ^ (prefixWord ++ tailWord_4124909).sum := by decide
  have hdescent : baseEnd_4124909 < baseStart_4124909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124922 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3]
def baseStart_4124922 : Nat := 118140960795 + 4124922 * 2 ^ 59
def prefixEnd_4124922 : Nat := 4983230072969 + 3 ^ 40 * 4124922 * 2
def baseEnd_4124922 : Nat := 2118067648305415457404835

theorem tailTrace_4124922 : CollatzResearch.WordTrace tailWord_4124922 prefixEnd_4124922 2118067648305415457404835 := by
  unfold tailWord_4124922
  simp only [CollatzResearch.WordTrace]
  refine ⟨37612066290529887359036255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100298843441413032957430013 37612066290529887359036255)
  ·
    refine ⟨56418099435794831038554383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37612066290529887359036255 56418099435794831038554383)
    ·
      refine ⟨84627149153692246557831575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56418099435794831038554383 84627149153692246557831575)
      ·
        refine ⟨126940723730538369836747363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84627149153692246557831575 126940723730538369836747363)
        ·
          refine ⟨190411085595807554755121045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126940723730538369836747363 190411085595807554755121045)
          ·
            refine ⟨8925519637303479129146299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190411085595807554755121045 8925519637303479129146299)
            ·
              refine ⟨13388279455955218693719449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925519637303479129146299 13388279455955218693719449)
              ·
                refine ⟨10041209591966414020289587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13388279455955218693719449 10041209591966414020289587)
                ·
                  refine ⟨15061814387949621030434381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10041209591966414020289587 15061814387949621030434381)
                  ·
                    refine ⟨5648180395481107886412893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15061814387949621030434381 5648180395481107886412893)
                    ·
                      refine ⟨2118067648305415457404835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5648180395481107886412893 2118067648305415457404835)
                      ·
                        rfl

theorem cell23_4124922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_4124922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124922 prefixEnd_4124922 := by exact prefixLift 4124922
  have htrace : WordTrace (prefixWord ++ tailWord_4124922) baseStart_4124922 baseEnd_4124922 := by
    simpa [prefixWord, tailWord_4124922, baseEnd_4124922] using wordTrace_append hprefix tailTrace_4124922
  have hstable : (prefixWord ++ tailWord_4124922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124922).length < 2 ^ (prefixWord ++ tailWord_4124922).sum := by decide
  have hdescent : baseEnd_4124922 < baseStart_4124922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124926 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_4124926 : Nat := 118140960795 + 4124926 * 2 ^ 59
def prefixEnd_4124926 : Nat := 4983230072969 + 3 ^ 40 * 4124926 * 2
def baseEnd_4124926 : Nat := 2118069702228033441754817

theorem tailTrace_4124926 : CollatzResearch.WordTrace tailWord_4124926 prefixEnd_4124926 2118069702228033441754817 := by
  unfold tailWord_4124926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18806051381763132264911329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100298940702736705412860421 18806051381763132264911329)
  ·
    refine ⟨14104538536322349198683497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18806051381763132264911329 14104538536322349198683497)
    ·
      refine ⟨10578403902241761899012623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14104538536322349198683497 10578403902241761899012623)
      ·
        refine ⟨15867605853362642848518935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10578403902241761899012623 15867605853362642848518935)
        ·
          refine ⟨23801408780043964272778403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15867605853362642848518935 23801408780043964272778403)
          ·
            refine ⟨35702113170065946409167605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23801408780043964272778403 35702113170065946409167605)
            ·
              refine ⟨3347073109693682475859463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35702113170065946409167605 3347073109693682475859463)
              ·
                refine ⟨5020609664540523713789195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347073109693682475859463 5020609664540523713789195)
                ·
                  refine ⟨7530914496810785570683793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020609664540523713789195 7530914496810785570683793)
                  ·
                    refine ⟨5648185872608089178012845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7530914496810785570683793 5648185872608089178012845)
                    ·
                      refine ⟨2118069702228033441754817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5648185872608089178012845 2118069702228033441754817)
                      ·
                        rfl

theorem cell23_4124926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_4124926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124926 prefixEnd_4124926 := by exact prefixLift 4124926
  have htrace : WordTrace (prefixWord ++ tailWord_4124926) baseStart_4124926 baseEnd_4124926 := by
    simpa [prefixWord, tailWord_4124926, baseEnd_4124926] using wordTrace_append hprefix tailTrace_4124926
  have hstable : (prefixWord ++ tailWord_4124926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124926).length < 2 ^ (prefixWord ++ tailWord_4124926).sum := by decide
  have hdescent : baseEnd_4124926 < baseStart_4124926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124939 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 2, 1, 3]
def baseStart_4124939 : Nat := 118140960795 + 4124939 * 2 ^ 59
def prefixEnd_4124939 : Nat := 4983230072969 + 3 ^ 40 * 4124939 * 2
def baseEnd_4124939 : Nat := 2118076377476541890892257

theorem tailTrace_4124939 : CollatzResearch.WordTrace tailWord_4124939 prefixEnd_4124939 2118076377476541890892257 := by
  unfold tailWord_4124939
  simp only [CollatzResearch.WordTrace]
  refine ⟨150448885203057961339513871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100299256802038640893009247 150448885203057961339513871)
  ·
    refine ⟨225673327804586942009270807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150448885203057961339513871 225673327804586942009270807)
    ·
      refine ⟨338509991706880413013906211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225673327804586942009270807 338509991706880413013906211)
      ·
        refine ⟨507764987560320619520859317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338509991706880413013906211 507764987560320619520859317)
        ·
          refine ⟨47602967583780058080080561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 507764987560320619520859317 47602967583780058080080561)
          ·
            refine ⟨35702225687835043560060421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47602967583780058080080561 35702225687835043560060421)
            ·
              refine ⟨6694167316469070667511329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35702225687835043560060421 6694167316469070667511329)
              ·
                refine ⟨5020625487351803000633497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6694167316469070667511329 5020625487351803000633497)
                ·
                  refine ⟨3765469115513852250475123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5020625487351803000633497 3765469115513852250475123)
                  ·
                    refine ⟨5648203673270778375712685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3765469115513852250475123 5648203673270778375712685)
                    ·
                      refine ⟨2118076377476541890892257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5648203673270778375712685 2118076377476541890892257)
                      ·
                        rfl

theorem cell23_4124939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 1, 3].length) (baseStart_4124939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124939 prefixEnd_4124939 := by exact prefixLift 4124939
  have htrace : WordTrace (prefixWord ++ tailWord_4124939) baseStart_4124939 baseEnd_4124939 := by
    simpa [prefixWord, tailWord_4124939, baseEnd_4124939] using wordTrace_append hprefix tailTrace_4124939
  have hstable : (prefixWord ++ tailWord_4124939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124939).length < 2 ^ (prefixWord ++ tailWord_4124939).sum := by decide
  have hdescent : baseEnd_4124939 < baseStart_4124939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124945 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_4124945 : Nat := 118140960795 + 4124945 * 2 ^ 59
def prefixEnd_4124945 : Nat := 4983230072969 + 3 ^ 40 * 4124945 * 2
def baseEnd_4124945 : Nat := 2118079458360468867417229

theorem tailTrace_4124945 : CollatzResearch.WordTrace tailWord_4124945 prefixEnd_4124945 2118079458360468867417229 := by
  unfold tailWord_4124945
  simp only [CollatzResearch.WordTrace]
  refine ⟨150449104041036224364232289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100299402694024149576154859 150449104041036224364232289)
  ·
    refine ⟨112836828030777168273174217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150449104041036224364232289 112836828030777168273174217)
    ·
      refine ⟨84627621023082876204880663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112836828030777168273174217 84627621023082876204880663)
      ·
        refine ⟨126941431534624314307320995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84627621023082876204880663 126941431534624314307320995)
        ·
          refine ⟨190412147301936471460981493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126941431534624314307320995 190412147301936471460981493)
          ·
            refine ⟨17851138809556544199467015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190412147301936471460981493 17851138809556544199467015)
            ·
              refine ⟨26776708214334816299200523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17851138809556544199467015 26776708214334816299200523)
              ·
                refine ⟨40165062321502224448800785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26776708214334816299200523 40165062321502224448800785)
                ·
                  refine ⟨30123796741126668336600589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40165062321502224448800785 30123796741126668336600589)
                  ·
                    refine ⟨11296423777922500626225221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30123796741126668336600589 11296423777922500626225221)
                    ·
                      refine ⟨2118079458360468867417229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11296423777922500626225221 2118079458360468867417229)
                      ·
                        rfl

theorem cell23_4124945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_4124945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124945 prefixEnd_4124945 := by exact prefixLift 4124945
  have htrace : WordTrace (prefixWord ++ tailWord_4124945) baseStart_4124945 baseEnd_4124945 := by
    simpa [prefixWord, tailWord_4124945, baseEnd_4124945] using wordTrace_append hprefix tailTrace_4124945
  have hstable : (prefixWord ++ tailWord_4124945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124945).length < 2 ^ (prefixWord ++ tailWord_4124945).sum := by decide
  have hdescent : baseEnd_4124945 < baseStart_4124945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124979 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 4, 2, 2]
def baseStart_4124979 : Nat := 118140960795 + 4124979 * 2 ^ 59
def prefixEnd_4124979 : Nat := 4983230072969 + 3 ^ 40 * 4124979 * 2
def baseEnd_4124979 : Nat := 2118096916702721734392073

theorem tailTrace_4124979 : CollatzResearch.WordTrace tailWord_4124979 prefixEnd_4124979 2118096916702721734392073 := by
  unfold tailWord_4124979
  simp only [CollatzResearch.WordTrace]
  refine ⟨150450344122913048170969991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100300229415275365447313327 150450344122913048170969991)
  ·
    refine ⟨225675516184369572256454987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150450344122913048170969991 225675516184369572256454987)
    ·
      refine ⟨338513274276554358384682481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225675516184369572256454987 338513274276554358384682481)
      ·
        refine ⟨253884955707415768788511861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338513274276554358384682481 253884955707415768788511861)
        ·
          refine ⟨23801714597570228323922987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253884955707415768788511861 23801714597570228323922987)
          ·
            refine ⟨35702571896355342485884481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23801714597570228323922987 35702571896355342485884481)
            ·
              refine ⟨26776928922266506864413361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35702571896355342485884481 26776928922266506864413361)
              ·
                refine ⟨20082696691699880148310021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26776928922266506864413361 20082696691699880148310021)
                ·
                  refine ⟨3765505629693727527808129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20082696691699880148310021 3765505629693727527808129)
                  ·
                    refine ⟨2824129222270295645856097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3765505629693727527808129 2824129222270295645856097)
                    ·
                      refine ⟨2118096916702721734392073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824129222270295645856097 2118096916702721734392073)
                      ·
                        rfl

theorem cell23_4124979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 2, 2].length) (baseStart_4124979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4124979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4124979 prefixEnd_4124979 := by exact prefixLift 4124979
  have htrace : WordTrace (prefixWord ++ tailWord_4124979) baseStart_4124979 baseEnd_4124979 := by
    simpa [prefixWord, tailWord_4124979, baseEnd_4124979] using wordTrace_append hprefix tailTrace_4124979
  have hstable : (prefixWord ++ tailWord_4124979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124979).length < 2 ^ (prefixWord ++ tailWord_4124979).sum := by decide
  have hdescent : baseEnd_4124979 < baseStart_4124979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125013 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 1, 4, 2]
def baseStart_4125013 : Nat := 118140960795 + 4125013 * 2 ^ 59
def prefixEnd_4125013 : Nat := 4983230072969 + 3 ^ 40 * 4125013 * 2
def baseEnd_4125013 : Nat := 2118114375044974601366917

theorem tailTrace_4125013 : CollatzResearch.WordTrace tailWord_4125013 prefixEnd_4125013 2118114375044974601366917 := by
  unfold tailWord_4125013
  simp only [CollatzResearch.WordTrace]
  refine ⟨150451584204789871977707693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100301056136526581318471795 150451584204789871977707693)
  ·
    refine ⟨56419344076796201991640385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150451584204789871977707693 56419344076796201991640385)
    ·
      refine ⟨42314508057597151493730289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56419344076796201991640385 42314508057597151493730289)
      ·
        refine ⟨31735881043197863620297717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42314508057597151493730289 31735881043197863620297717)
        ·
          refine ⟨2975238847799799714402911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31735881043197863620297717 2975238847799799714402911)
          ·
            refine ⟨4462858271699699571604367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2975238847799799714402911 4462858271699699571604367)
            ·
              refine ⟨6694287407549549357406551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462858271699699571604367 6694287407549549357406551)
              ·
                refine ⟨10041431111324324036109827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6694287407549549357406551 10041431111324324036109827)
                ·
                  refine ⟨15062146666986486054164741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10041431111324324036109827 15062146666986486054164741)
                  ·
                    refine ⟨2824152500059966135155889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15062146666986486054164741 2824152500059966135155889)
                    ·
                      refine ⟨2118114375044974601366917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824152500059966135155889 2118114375044974601366917)
                      ·
                        rfl

theorem cell23_4125013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_4125013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125013 prefixEnd_4125013 := by exact prefixLift 4125013
  have htrace : WordTrace (prefixWord ++ tailWord_4125013) baseStart_4125013 baseEnd_4125013 := by
    simpa [prefixWord, tailWord_4125013, baseEnd_4125013] using wordTrace_append hprefix tailTrace_4125013
  have hstable : (prefixWord ++ tailWord_4125013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125013).length < 2 ^ (prefixWord ++ tailWord_4125013).sum := by decide
  have hdescent : baseEnd_4125013 < baseStart_4125013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125015 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 3, 7]
def baseStart_4125015 : Nat := 118140960795 + 4125015 * 2 ^ 59
def prefixEnd_4125015 : Nat := 4983230072969 + 3 ^ 40 * 4125015 * 2
def baseEnd_4125015 : Nat := 706038467335427864513969

theorem tailTrace_4125015 : CollatzResearch.WordTrace tailWord_4125015 prefixEnd_4125015 706038467335427864513969 := by
  unfold tailWord_4125015
  simp only [CollatzResearch.WordTrace]
  refine ⟨150451657150782626319280499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100301104767188417546186999 150451657150782626319280499)
  ·
    refine ⟨225677485726173939478920749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150451657150782626319280499 225677485726173939478920749)
    ·
      refine ⟨84629057147315227304595281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225677485726173939478920749 84629057147315227304595281)
      ·
        refine ⟨63471792860486420478446461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84629057147315227304595281 63471792860486420478446461)
        ·
          refine ⟨23801922322682407679417423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63471792860486420478446461 23801922322682407679417423)
          ·
            refine ⟨35702883484023611519126135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23801922322682407679417423 35702883484023611519126135)
            ·
              refine ⟨53554325226035417278689203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35702883484023611519126135 53554325226035417278689203)
              ·
                refine ⟨80331487839053125918033805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53554325226035417278689203 80331487839053125918033805)
                ·
                  refine ⟨30124307939644922219262677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80331487839053125918033805 30124307939644922219262677)
                  ·
                    refine ⟨706038467335427864513969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30124307939644922219262677 706038467335427864513969)
                    ·
                      rfl

theorem cell23_4125015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_4125015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125015 prefixEnd_4125015 := by exact prefixLift 4125015
  have htrace : WordTrace (prefixWord ++ tailWord_4125015) baseStart_4125015 baseEnd_4125015 := by
    simpa [prefixWord, tailWord_4125015, baseEnd_4125015] using wordTrace_append hprefix tailTrace_4125015
  have hstable : (prefixWord ++ tailWord_4125015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125015).length < 2 ^ (prefixWord ++ tailWord_4125015).sum := by decide
  have hdescent : baseEnd_4125015 < baseStart_4125015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125025 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_4125025 : Nat := 118140960795 + 4125025 * 2 ^ 59
def prefixEnd_4125025 : Nat := 4983230072969 + 3 ^ 40 * 4125025 * 2
def baseEnd_4125025 : Nat := 2118120536812828554416861

theorem tailTrace_4125025 : CollatzResearch.WordTrace tailWord_4125025 prefixEnd_4125025 2118120536812828554416861 := by
  unfold tailWord_4125025
  simp only [CollatzResearch.WordTrace]
  refine ⟨150452021880746398027144529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100301347920497598684763019 150452021880746398027144529)
  ·
    refine ⟨112839016410559798520358397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150452021880746398027144529 112839016410559798520358397)
    ·
      refine ⟨42314631153959924445134399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112839016410559798520358397 42314631153959924445134399)
      ·
        refine ⟨63471946730939886667701599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42314631153959924445134399 63471946730939886667701599)
        ·
          refine ⟨95207920096409830001552399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63471946730939886667701599 95207920096409830001552399)
          ·
            refine ⟨142811880144614745002328599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95207920096409830001552399 142811880144614745002328599)
            ·
              refine ⟨214217820216922117503492899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142811880144614745002328599 214217820216922117503492899)
              ·
                refine ⟨321326730325383176255239349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214217820216922117503492899 321326730325383176255239349)
                ·
                  refine ⟨30124380968004672773928689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321326730325383176255239349 30124380968004672773928689)
                  ·
                    refine ⟨22593285726003504580446517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30124380968004672773928689 22593285726003504580446517)
                    ·
                      refine ⟨2118120536812828554416861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22593285726003504580446517 2118120536812828554416861)
                      ·
                        rfl

theorem cell23_4125025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_4125025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125025 prefixEnd_4125025 := by exact prefixLift 4125025
  have htrace : WordTrace (prefixWord ++ tailWord_4125025) baseStart_4125025 baseEnd_4125025 := by
    simpa [prefixWord, tailWord_4125025, baseEnd_4125025] using wordTrace_append hprefix tailTrace_4125025
  have hstable : (prefixWord ++ tailWord_4125025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125025).length < 2 ^ (prefixWord ++ tailWord_4125025).sum := by decide
  have hdescent : baseEnd_4125025 < baseStart_4125025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125032 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 1, 7]
def baseStart_4125032 : Nat := 118140960795 + 4125032 * 2 ^ 59
def prefixEnd_4125032 : Nat := 4983230072969 + 3 ^ 40 * 4125032 * 2
def baseEnd_4125032 : Nat := 706041377059136675676443

theorem tailTrace_4125032 : CollatzResearch.WordTrace tailWord_4125032 prefixEnd_4125032 706041377059136675676443 := by
  unfold tailWord_4125032
  simp only [CollatzResearch.WordTrace]
  refine ⟨75226138595860519111324675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100301518127814025481766233 75226138595860519111324675)
  ·
    refine ⟨112839207893790778666987013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75226138595860519111324675 112839207893790778666987013)
    ·
      refine ⟨21157351480085771000060065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112839207893790778666987013 21157351480085771000060065)
      ·
        refine ⟨15868013610064328250045049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21157351480085771000060065 15868013610064328250045049)
        ·
          refine ⟨11901010207548246187533787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15868013610064328250045049 11901010207548246187533787)
          ·
            refine ⟨17851515311322369281300681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11901010207548246187533787 17851515311322369281300681)
            ·
              refine ⟨13388636483491776960975511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17851515311322369281300681 13388636483491776960975511)
              ·
                refine ⟨20082954725237665441463267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13388636483491776960975511 20082954725237665441463267)
                ·
                  refine ⟨30124432087856498162194901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20082954725237665441463267 30124432087856498162194901)
                  ·
                    refine ⟨706041377059136675676443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30124432087856498162194901 706041377059136675676443)
                    ·
                      rfl

theorem cell23_4125032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_4125032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125032 prefixEnd_4125032 := by exact prefixLift 4125032
  have htrace : WordTrace (prefixWord ++ tailWord_4125032) baseStart_4125032 baseEnd_4125032 := by
    simpa [prefixWord, tailWord_4125032, baseEnd_4125032] using wordTrace_append hprefix tailTrace_4125032
  have hstable : (prefixWord ++ tailWord_4125032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125032).length < 2 ^ (prefixWord ++ tailWord_4125032).sum := by decide
  have hdescent : baseEnd_4125032 < baseStart_4125032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125036 : List Nat := [2, 2, 1, 1, 6, 2, 1, 3, 5]
def baseStart_4125036 : Nat := 118140960795 + 4125036 * 2 ^ 59
def prefixEnd_4125036 : Nat := 4983230072969 + 3 ^ 40 * 4125036 * 2
def baseEnd_4125036 : Nat := 235347353900003112375479

theorem tailTrace_4125036 : CollatzResearch.WordTrace tailWord_4125036 prefixEnd_4125036 235347353900003112375479 := by
  unfold tailWord_4125036
  simp only [CollatzResearch.WordTrace]
  refine ⟨75226211541853273452897481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100301615389137697937196641 75226211541853273452897481)
  ·
    refine ⟨56419658656389955089673111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75226211541853273452897481 56419658656389955089673111)
    ·
      refine ⟨84629487984584932634509667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56419658656389955089673111 84629487984584932634509667)
      ·
        refine ⟨126944231976877398951764501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84629487984584932634509667 126944231976877398951764501)
        ·
          refine ⟨5950510873916128075863961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126944231976877398951764501 5950510873916128075863961)
          ·
            refine ⟨4462883155437096056897971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5950510873916128075863961 4462883155437096056897971)
            ·
              refine ⟨6694324733155644085346957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462883155437096056897971 6694324733155644085346957)
              ·
                refine ⟨2510371774933366532005109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6694324733155644085346957 2510371774933366532005109)
                ·
                  refine ⟨235347353900003112375479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2510371774933366532005109 235347353900003112375479)
                  ·
                    rfl

theorem cell23_4125036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_4125036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125036 prefixEnd_4125036 := by exact prefixLift 4125036
  have htrace : WordTrace (prefixWord ++ tailWord_4125036) baseStart_4125036 baseEnd_4125036 := by
    simpa [prefixWord, tailWord_4125036, baseEnd_4125036] using wordTrace_append hprefix tailTrace_4125036
  have hstable : (prefixWord ++ tailWord_4125036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125036).length < 2 ^ (prefixWord ++ tailWord_4125036).sum := by decide
  have hdescent : baseEnd_4125036 < baseStart_4125036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125055 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_4125055 : Nat := 118140960795 + 4125055 * 2 ^ 59
def prefixEnd_4125055 : Nat := 4983230072969 + 3 ^ 40 * 4125055 * 2
def baseEnd_4125055 : Nat := 2118135941232463437041723

theorem tailTrace_4125055 : CollatzResearch.WordTrace tailWord_4125055 prefixEnd_4125055 2118135941232463437041723 := by
  unfold tailWord_4125055
  simp only [CollatzResearch.WordTrace]
  refine ⟨150453116070637713150736619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100302077380425142100491079 150453116070637713150736619)
  ·
    refine ⟨225679674105956569726104929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150453116070637713150736619 225679674105956569726104929)
    ·
      refine ⟨169259755579467427294578697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225679674105956569726104929 169259755579467427294578697)
      ·
        refine ⟨126944816684600570470934023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169259755579467427294578697 126944816684600570470934023)
        ·
          refine ⟨190417225026900855706401035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126944816684600570470934023 190417225026900855706401035)
          ·
            refine ⟨285625837540351283559601553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190417225026900855706401035 285625837540351283559601553)
            ·
              refine ⟨214219378155263462669701165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285625837540351283559601553 214219378155263462669701165)
              ·
                refine ⟨80332266808223798501137937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214219378155263462669701165 80332266808223798501137937)
                ·
                  refine ⟨60249200106167848875853453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80332266808223798501137937 60249200106167848875853453)
                  ·
                    refine ⟨22593450039812943328445045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60249200106167848875853453 22593450039812943328445045)
                    ·
                      refine ⟨2118135941232463437041723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22593450039812943328445045 2118135941232463437041723)
                      ·
                        rfl

theorem cell23_4125055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_4125055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125055 prefixEnd_4125055 := by exact prefixLift 4125055
  have htrace : WordTrace (prefixWord ++ tailWord_4125055) baseStart_4125055 baseEnd_4125055 := by
    simpa [prefixWord, tailWord_4125055, baseEnd_4125055] using wordTrace_append hprefix tailTrace_4125055
  have hstable : (prefixWord ++ tailWord_4125055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125055).length < 2 ^ (prefixWord ++ tailWord_4125055).sum := by decide
  have hdescent : baseEnd_4125055 < baseStart_4125055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125086 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4125086 : Nat := 118140960795 + 4125086 * 2 ^ 59
def prefixEnd_4125086 : Nat := 4983230072969 + 3 ^ 40 * 4125086 * 2
def baseEnd_4125086 : Nat := 2118151859132752815754081

theorem tailTrace_4125086 : CollatzResearch.WordTrace tailWord_4125086 prefixEnd_4125086 2118151859132752815754081 := by
  unfold tailWord_4125086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18806780841690675680639389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100302831155683603630076741 18806780841690675680639389)
  ·
    refine ⟨7052542815634003380239771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18806780841690675680639389 7052542815634003380239771)
    ·
      refine ⟨10578814223451005070359657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7052542815634003380239771 10578814223451005070359657)
      ·
        refine ⟨7934110667588253802769743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10578814223451005070359657 7934110667588253802769743)
        ·
          refine ⟨11901166001382380704154615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7934110667588253802769743 11901166001382380704154615)
          ·
            refine ⟨17851749002073571056231923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11901166001382380704154615 17851749002073571056231923)
            ·
              refine ⟨26777623503110356584347885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17851749002073571056231923 26777623503110356584347885)
              ·
                refine ⟨10041608813666383719130457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26777623503110356584347885 10041608813666383719130457)
                ·
                  refine ⟨7531206610249787789347843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10041608813666383719130457 7531206610249787789347843)
                  ·
                    refine ⟨11296809915374681684021765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7531206610249787789347843 11296809915374681684021765)
                    ·
                      refine ⟨2118151859132752815754081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11296809915374681684021765 2118151859132752815754081)
                      ·
                        rfl

theorem cell23_4125086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4125086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125086 prefixEnd_4125086 := by exact prefixLift 4125086
  have htrace : WordTrace (prefixWord ++ tailWord_4125086) baseStart_4125086 baseEnd_4125086 := by
    simpa [prefixWord, tailWord_4125086, baseEnd_4125086] using wordTrace_append hprefix tailTrace_4125086
  have hstable : (prefixWord ++ tailWord_4125086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125086).length < 2 ^ (prefixWord ++ tailWord_4125086).sum := by decide
  have hdescent : baseEnd_4125086 < baseStart_4125086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125113 : List Nat := [1, 2, 1, 4, 3, 1, 4, 2, 1, 4]
def baseStart_4125113 : Nat := 118140960795 + 4125113 * 2 ^ 59
def prefixEnd_4125113 : Nat := 4983230072969 + 3 ^ 40 * 4125113 * 2
def baseEnd_4125113 : Nat := 706055241036808070038819

theorem tailTrace_4125113 : CollatzResearch.WordTrace tailWord_4125113 prefixEnd_4125113 706055241036808070038819 := by
  unfold tailWord_4125113
  simp only [CollatzResearch.WordTrace]
  refine ⟨150455231504427589056347993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100303487669618392704231995 150455231504427589056347993)
  ·
    refine ⟨112841423628320691792260995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150455231504427589056347993 112841423628320691792260995)
    ·
      refine ⟨169262135442481037688391493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112841423628320691792260995 169262135442481037688391493)
      ·
        refine ⟨31736650395465194566573405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169262135442481037688391493 31736650395465194566573405)
        ·
          refine ⟨11901243898299447962465027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31736650395465194566573405 11901243898299447962465027)
          ·
            refine ⟨17851865847449171943697541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11901243898299447962465027 17851865847449171943697541)
            ·
              refine ⟨3347224846396719739443289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17851865847449171943697541 3347224846396719739443289)
              ·
                refine ⟨2510418634797539804582467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3347224846396719739443289 2510418634797539804582467)
                ·
                  refine ⟨3765627952196309706873701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510418634797539804582467 3765627952196309706873701)
                  ·
                    refine ⟨706055241036808070038819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3765627952196309706873701 706055241036808070038819)
                    ·
                      rfl

theorem cell23_4125113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 1, 4].length) (baseStart_4125113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125113 prefixEnd_4125113 := by exact prefixLift 4125113
  have htrace : WordTrace (prefixWord ++ tailWord_4125113) baseStart_4125113 baseEnd_4125113 := by
    simpa [prefixWord, tailWord_4125113, baseEnd_4125113] using wordTrace_append hprefix tailTrace_4125113
  have hstable : (prefixWord ++ tailWord_4125113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125113).length < 2 ^ (prefixWord ++ tailWord_4125113).sum := by decide
  have hdescent : baseEnd_4125113 < baseStart_4125113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125129 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 4, 3, 2]
def baseStart_4125129 : Nat := 118140960795 + 4125129 * 2 ^ 59
def prefixEnd_4125129 : Nat := 4983230072969 + 3 ^ 40 * 4125129 * 2
def baseEnd_4125129 : Nat := 2118173938800896147516383

theorem tailTrace_4125129 : CollatzResearch.WordTrace tailWord_4125129 prefixEnd_4125129 2118173938800896147516383 := by
  unfold tailWord_4125129
  simp only [CollatzResearch.WordTrace]
  refine ⟨150455815072369623788930441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100303876714913082525953627 150455815072369623788930441)
  ·
    refine ⟨112841861304277217841697831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150455815072369623788930441 112841861304277217841697831)
    ·
      refine ⟨169262791956415826762546747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112841861304277217841697831 169262791956415826762546747)
      ·
        refine ⟨253894187934623740143820121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169262791956415826762546747 253894187934623740143820121)
        ·
          refine ⟨190420640950967805107865091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253894187934623740143820121 190420640950967805107865091)
          ·
            refine ⟨285630961426451707661797637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190420640950967805107865091 285630961426451707661797637)
            ·
              refine ⟨53555805267459695186587057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285630961426451707661797637 53555805267459695186587057)
              ·
                refine ⟨40166853950594771389940293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53555805267459695186587057 40166853950594771389940293)
                ·
                  refine ⟨7531285115736519635613805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40166853950594771389940293 7531285115736519635613805)
                  ·
                    refine ⟨2824231918401194863355177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7531285115736519635613805 2824231918401194863355177)
                    ·
                      refine ⟨2118173938800896147516383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824231918401194863355177 2118173938800896147516383)
                      ·
                        rfl

theorem cell23_4125129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 3, 2].length) (baseStart_4125129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125129 prefixEnd_4125129 := by exact prefixLift 4125129
  have htrace : WordTrace (prefixWord ++ tailWord_4125129) baseStart_4125129 baseEnd_4125129 := by
    simpa [prefixWord, tailWord_4125129, baseEnd_4125129] using wordTrace_append hprefix tailTrace_4125129
  have hstable : (prefixWord ++ tailWord_4125129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125129).length < 2 ^ (prefixWord ++ tailWord_4125129).sum := by decide
  have hdescent : baseEnd_4125129 < baseStart_4125129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125152 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 1, 6]
def baseStart_4125152 : Nat := 118140960795 + 4125152 * 2 ^ 59
def prefixEnd_4125152 : Nat := 4983230072969 + 3 ^ 40 * 4125152 * 2
def baseEnd_4125152 : Nat := 706061916285316519176259

theorem tailTrace_4125152 : CollatzResearch.WordTrace tailWord_4125152 prefixEnd_4125152 706061916285316519176259 := by
  unfold tailWord_4125152
  simp only [CollatzResearch.WordTrace]
  refine ⟨75228326975643149358508855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100304435967524199144678473 75228326975643149358508855)
  ·
    refine ⟨112842490463464724037763283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75228326975643149358508855 112842490463464724037763283)
    ·
      refine ⟨169263735695197086056644925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112842490463464724037763283 169263735695197086056644925)
      ·
        refine ⟨63473900885698907271241847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169263735695197086056644925 63473900885698907271241847)
        ·
          refine ⟨95210851328548360906862771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63473900885698907271241847 95210851328548360906862771)
          ·
            refine ⟨142816276992822541360294157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95210851328548360906862771 142816276992822541360294157)
            ·
              refine ⟨53556103872308453010110309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142816276992822541360294157 53556103872308453010110309)
              ·
                refine ⟨10041769476057834939395683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53556103872308453010110309 10041769476057834939395683)
                ·
                  refine ⟨15062654214086752409093525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10041769476057834939395683 15062654214086752409093525)
                  ·
                    refine ⟨706061916285316519176259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15062654214086752409093525 706061916285316519176259)
                    ·
                      rfl

theorem cell23_4125152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_4125152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125152 prefixEnd_4125152 := by exact prefixLift 4125152
  have htrace : WordTrace (prefixWord ++ tailWord_4125152) baseStart_4125152 baseEnd_4125152 := by
    simpa [prefixWord, tailWord_4125152, baseEnd_4125152] using wordTrace_append hprefix tailTrace_4125152
  have hstable : (prefixWord ++ tailWord_4125152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125152).length < 2 ^ (prefixWord ++ tailWord_4125152).sum := by decide
  have hdescent : baseEnd_4125152 < baseStart_4125152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125153 : List Nat := [1, 2, 3, 1, 2, 2, 4, 3, 1, 1, 3]
def baseStart_4125153 : Nat := 118140960795 + 4125153 * 2 ^ 59
def prefixEnd_4125153 : Nat := 4983230072969 + 3 ^ 40 * 4125153 * 2
def baseEnd_4125153 : Nat := 2118186262336604053616273

theorem tailTrace_4125153 : CollatzResearch.WordTrace tailWord_4125153 prefixEnd_4125153 2118186262336604053616273 := by
  unfold tailWord_4125153
  simp only [CollatzResearch.WordTrace]
  refine ⟨150456690424282675887804113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100304460282855117258536075 150456690424282675887804113)
  ·
    refine ⟨112842517818212006915853085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150456690424282675887804113 112842517818212006915853085)
    ·
      refine ⟨42315944181829502593444907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112842517818212006915853085 42315944181829502593444907)
      ·
        refine ⟨63473916272744253890167361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42315944181829502593444907 63473916272744253890167361)
        ·
          refine ⟨47605437204558190417625521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63473916272744253890167361 47605437204558190417625521)
          ·
            refine ⟨35704077903418642813219141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47605437204558190417625521 35704077903418642813219141)
            ·
              refine ⟨6694514606890995527478589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35704077903418642813219141 6694514606890995527478589)
              ·
                refine ⟨2510442977584123322804471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6694514606890995527478589 2510442977584123322804471)
                ·
                  refine ⟨3765664466376184984206707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510442977584123322804471 3765664466376184984206707)
                  ·
                    refine ⟨5648496699564277476310061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3765664466376184984206707 5648496699564277476310061)
                    ·
                      refine ⟨2118186262336604053616273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5648496699564277476310061 2118186262336604053616273)
                      ·
                        rfl

theorem cell23_4125153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_4125153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125153 prefixEnd_4125153 := by exact prefixLift 4125153
  have htrace : WordTrace (prefixWord ++ tailWord_4125153) baseStart_4125153 baseEnd_4125153 := by
    simpa [prefixWord, tailWord_4125153, baseEnd_4125153] using wordTrace_append hprefix tailTrace_4125153
  have hstable : (prefixWord ++ tailWord_4125153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125153).length < 2 ^ (prefixWord ++ tailWord_4125153).sum := by decide
  have hdescent : baseEnd_4125153 < baseStart_4125153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125169 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 4, 4]
def baseStart_4125169 : Nat := 118140960795 + 4125169 * 2 ^ 59
def prefixEnd_4125169 : Nat := 4983230072969 + 3 ^ 40 * 4125169 * 2
def baseEnd_4125169 : Nat := 706064826009025330338733

theorem tailTrace_4125169 : CollatzResearch.WordTrace tailWord_4125169 prefixEnd_4125169 706064826009025330338733 := by
  unfold tailWord_4125169
  simp only [CollatzResearch.WordTrace]
  refine ⟨150457273992224710620386561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100304849328149807080257707 150457273992224710620386561)
  ·
    refine ⟨112842955494168532965289921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150457273992224710620386561 112842955494168532965289921)
    ·
      refine ⟨84632216620626399723967441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112842955494168532965289921 84632216620626399723967441)
      ·
        refine ⟨63474162465469799792975581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84632216620626399723967441 63474162465469799792975581)
        ·
          refine ⟨23802810924551174922365843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63474162465469799792975581 23802810924551174922365843)
          ·
            refine ⟨35704216386826762383548765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23802810924551174922365843 35704216386826762383548765)
            ·
              refine ⟨13389081145060035893830787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35704216386826762383548765 13389081145060035893830787)
              ·
                refine ⟨20083621717590053840746181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13389081145060035893830787 20083621717590053840746181)
                ·
                  refine ⟨3765679072048135095139909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20083621717590053840746181 3765679072048135095139909)
                  ·
                    refine ⟨706064826009025330338733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3765679072048135095139909 706064826009025330338733)
                    ·
                      rfl

theorem cell23_4125169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_4125169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125169 prefixEnd_4125169 := by exact prefixLift 4125169
  have htrace : WordTrace (prefixWord ++ tailWord_4125169) baseStart_4125169 baseEnd_4125169 := by
    simpa [prefixWord, tailWord_4125169, baseEnd_4125169] using wordTrace_append hprefix tailTrace_4125169
  have hstable : (prefixWord ++ tailWord_4125169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125169).length < 2 ^ (prefixWord ++ tailWord_4125169).sum := by decide
  have hdescent : baseEnd_4125169 < baseStart_4125169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125189 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 4]
def baseStart_4125189 : Nat := 118140960795 + 4125189 * 2 ^ 59
def prefixEnd_4125189 : Nat := 4983230072969 + 3 ^ 40 * 4125189 * 2
def baseEnd_4125189 : Nat := 2118204747640165912766107

theorem tailTrace_4125189 : CollatzResearch.WordTrace tailWord_4125189 prefixEnd_4125189 2118204747640165912766107 := by
  unfold tailWord_4125189
  simp only [CollatzResearch.WordTrace]
  refine ⟨150458003452152254036114621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100305335634768169357409747 150458003452152254036114621)
  ·
    refine ⟨56421751294557095263542983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150458003452152254036114621 56421751294557095263542983)
    ·
      refine ⟨84632626941835642895314475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56421751294557095263542983 84632626941835642895314475)
      ·
        refine ⟨126948940412753464342971713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84632626941835642895314475 126948940412753464342971713)
        ·
          refine ⟨95211705309565098257228785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126948940412753464342971713 95211705309565098257228785)
          ·
            refine ⟨71408778982173823692921589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95211705309565098257228785 71408778982173823692921589)
            ·
              refine ⟨6694573029578795971211399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71408778982173823692921589 6694573029578795971211399)
              ·
                refine ⟨10041859544368193956817099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6694573029578795971211399 10041859544368193956817099)
                ·
                  refine ⟨15062789316552290935225649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10041859544368193956817099 15062789316552290935225649)
                  ·
                    refine ⟨11297091987414218201419237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15062789316552290935225649 11297091987414218201419237)
                    ·
                      refine ⟨2118204747640165912766107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11297091987414218201419237 2118204747640165912766107)
                      ·
                        rfl

theorem cell23_4125189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_4125189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125189 prefixEnd_4125189 := by exact prefixLift 4125189
  have htrace : WordTrace (prefixWord ++ tailWord_4125189) baseStart_4125189 baseEnd_4125189 := by
    simpa [prefixWord, tailWord_4125189, baseEnd_4125189] using wordTrace_append hprefix tailTrace_4125189
  have hstable : (prefixWord ++ tailWord_4125189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125189).length < 2 ^ (prefixWord ++ tailWord_4125189).sum := by decide
  have hdescent : baseEnd_4125189 < baseStart_4125189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125190 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4125190 : Nat := 118140960795 + 4125190 * 2 ^ 59
def prefixEnd_4125190 : Nat := 4983230072969 + 3 ^ 40 * 4125190 * 2
def baseEnd_4125190 : Nat := 706068420373606802951201

theorem tailTrace_4125190 : CollatzResearch.WordTrace tailWord_4125190 prefixEnd_4125190 706068420373606802951201 := by
  unfold tailWord_4125190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4701813747660894725215657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100305359950099087471267349 4701813747660894725215657)
  ·
    refine ⟨3526360310745671043911743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4701813747660894725215657 3526360310745671043911743)
    ·
      refine ⟨5289540466118506565867615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3526360310745671043911743 5289540466118506565867615)
      ·
        refine ⟨7934310699177759848801423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5289540466118506565867615 7934310699177759848801423)
        ·
          refine ⟨11901466048766639773202135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7934310699177759848801423 11901466048766639773202135)
          ·
            refine ⟨17852199073149959659803203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11901466048766639773202135 17852199073149959659803203)
            ·
              refine ⟨26778298609724939489704805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17852199073149959659803203 26778298609724939489704805)
              ·
                refine ⟨5020930989323426154319651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26778298609724939489704805 5020930989323426154319651)
                ·
                  refine ⟨7531396483985139231479477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020930989323426154319651 7531396483985139231479477)
                  ·
                    refine ⟨706068420373606802951201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7531396483985139231479477 706068420373606802951201)
                    ·
                      rfl

theorem cell23_4125190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4125190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125190 prefixEnd_4125190 := by exact prefixLift 4125190
  have htrace : WordTrace (prefixWord ++ tailWord_4125190) baseStart_4125190 baseEnd_4125190 := by
    simpa [prefixWord, tailWord_4125190, baseEnd_4125190] using wordTrace_append hprefix tailTrace_4125190
  have hstable : (prefixWord ++ tailWord_4125190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125190).length < 2 ^ (prefixWord ++ tailWord_4125190).sum := by decide
  have hdescent : baseEnd_4125190 < baseStart_4125190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125196 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 1, 2, 3]
def baseStart_4125196 : Nat := 118140960795 + 4125196 * 2 ^ 59
def prefixEnd_4125196 : Nat := 4983230072969 + 3 ^ 40 * 4125196 * 2
def baseEnd_4125196 : Nat := 2118208342004747385378575

theorem tailTrace_4125196 : CollatzResearch.WordTrace tailWord_4125196 prefixEnd_4125196 2118208342004747385378575 := by
  unfold tailWord_4125196
  simp only [CollatzResearch.WordTrace]
  refine ⟨75229129381563447115809721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100305505842084596154412961 75229129381563447115809721)
  ·
    refine ⟨56421847036172585336857291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75229129381563447115809721 56421847036172585336857291)
    ·
      refine ⟨84632770554258878005285937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56421847036172585336857291 84632770554258878005285937)
      ·
        refine ⟨63474577915694158503964453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84632770554258878005285937 63474577915694158503964453)
        ·
          refine ⟨11901483359192654719493335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63474577915694158503964453 11901483359192654719493335)
          ·
            refine ⟨17852225038788982079240003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11901483359192654719493335 17852225038788982079240003)
            ·
              refine ⟨26778337558183473118860005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17852225038788982079240003 26778337558183473118860005)
              ·
                refine ⟨5020938292159401209786251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26778337558183473118860005 5020938292159401209786251)
                ·
                  refine ⟨7531407438239101814679377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020938292159401209786251 7531407438239101814679377)
                  ·
                    refine ⟨5648555578679326361009533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7531407438239101814679377 5648555578679326361009533)
                    ·
                      refine ⟨2118208342004747385378575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5648555578679326361009533 2118208342004747385378575)
                      ·
                        rfl

theorem cell23_4125196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_4125196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125196 prefixEnd_4125196 := by exact prefixLift 4125196
  have htrace : WordTrace (prefixWord ++ tailWord_4125196) baseStart_4125196 baseEnd_4125196 := by
    simpa [prefixWord, tailWord_4125196, baseEnd_4125196] using wordTrace_append hprefix tailTrace_4125196
  have hstable : (prefixWord ++ tailWord_4125196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125196).length < 2 ^ (prefixWord ++ tailWord_4125196).sum := by decide
  have hdescent : baseEnd_4125196 < baseStart_4125196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125210 : List Nat := [3, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2]
def baseStart_4125210 : Nat := 118140960795 + 4125210 * 2 ^ 59
def prefixEnd_4125210 : Nat := 4983230072969 + 3 ^ 40 * 4125210 * 2
def baseEnd_4125210 : Nat := 2118215530733910330603511

theorem tailTrace_4125210 : CollatzResearch.WordTrace tailWord_4125210 prefixEnd_4125210 2118215530733910330603511 := by
  unfold tailWord_4125210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37614692346269043655657271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100305846256717449748419389 37614692346269043655657271)
  ·
    refine ⟨56422038519403565483485907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37614692346269043655657271 56422038519403565483485907)
    ·
      refine ⟨84633057779105348225228861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56422038519403565483485907 84633057779105348225228861)
      ·
        refine ⟨31737396667164505584460823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84633057779105348225228861 31737396667164505584460823)
        ·
          refine ⟨47606095000746758376691235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31737396667164505584460823 47606095000746758376691235)
          ·
            refine ⟨71409142501120137565036853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47606095000746758376691235 71409142501120137565036853)
            ·
              refine ⟨6694607109480012896722205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71409142501120137565036853 6694607109480012896722205)
              ·
                refine ⟨2510477666055004836270827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6694607109480012896722205 2510477666055004836270827)
                ·
                  refine ⟨3765716499082507254406241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510477666055004836270827 3765716499082507254406241)
                  ·
                    refine ⟨2824287374311880440804681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3765716499082507254406241 2824287374311880440804681)
                    ·
                      refine ⟨2118215530733910330603511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824287374311880440804681 2118215530733910330603511)
                      ·
                        rfl

theorem cell23_4125210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_4125210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125210 prefixEnd_4125210 := by exact prefixLift 4125210
  have htrace : WordTrace (prefixWord ++ tailWord_4125210) baseStart_4125210 baseEnd_4125210 := by
    simpa [prefixWord, tailWord_4125210, baseEnd_4125210] using wordTrace_append hprefix tailTrace_4125210
  have hstable : (prefixWord ++ tailWord_4125210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125210).length < 2 ^ (prefixWord ++ tailWord_4125210).sum := by decide
  have hdescent : baseEnd_4125210 < baseStart_4125210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125216 : List Nat := [2, 1, 1, 6, 3, 1, 9]
def baseStart_4125216 : Nat := 118140960795 + 4125216 * 2 ^ 59
def prefixEnd_4125216 : Nat := 4983230072969 + 3 ^ 40 * 4125216 * 2
def baseEnd_4125216 : Nat := 26150847057010337125043

theorem tailTrace_4125216 : CollatzResearch.WordTrace tailWord_4125216 prefixEnd_4125216 26150847057010337125043 := by
  unfold tailWord_4125216
  simp only [CollatzResearch.WordTrace]
  refine ⟨75229494111527218823673751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100305992148702958431565001 75229494111527218823673751)
  ·
    refine ⟨112844241167290828235510627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75229494111527218823673751 112844241167290828235510627)
    ·
      refine ⟨169266361750936242353265941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112844241167290828235510627 169266361750936242353265941)
      ·
        refine ⟨7934360707075136360309341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169266361750936242353265941 7934360707075136360309341)
        ·
          refine ⟨2975385265153176135116003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7934360707075136360309341 2975385265153176135116003)
          ·
            refine ⟨4463077897729764202674005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2975385265153176135116003 4463077897729764202674005)
            ·
              refine ⟨26150847057010337125043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4463077897729764202674005 26150847057010337125043)
              ·
                rfl

theorem cell23_4125216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 9].length) (baseStart_4125216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125216 prefixEnd_4125216 := by exact prefixLift 4125216
  have htrace : WordTrace (prefixWord ++ tailWord_4125216) baseStart_4125216 baseEnd_4125216 := by
    simpa [prefixWord, tailWord_4125216, baseEnd_4125216] using wordTrace_append hprefix tailTrace_4125216
  have hstable : (prefixWord ++ tailWord_4125216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125216).length < 2 ^ (prefixWord ++ tailWord_4125216).sum := by decide
  have hdescent : baseEnd_4125216 < baseStart_4125216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125253 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 1, 3, 2]
def baseStart_4125253 : Nat := 118140960795 + 4125253 * 2 ^ 59
def prefixEnd_4125253 : Nat := 4983230072969 + 3 ^ 40 * 4125253 * 2
def baseEnd_4125253 : Nat := 2118237610402053662365813

theorem tailTrace_4125253 : CollatzResearch.WordTrace tailWord_4125253 prefixEnd_4125253 2118237610402053662365813 := by
  unfold tailWord_4125253
  simp only [CollatzResearch.WordTrace]
  refine ⟨150460337723920392966444413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100306891815946928644296275 150460337723920392966444413)
  ·
    refine ⟨56422626646470147362416655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150460337723920392966444413 56422626646470147362416655)
    ·
      refine ⟨84633939969705221043624983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56422626646470147362416655 84633939969705221043624983)
      ·
        refine ⟨126950909954557831565437475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84633939969705221043624983 126950909954557831565437475)
        ·
          refine ⟨190426364931836747348156213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126950909954557831565437475 190426364931836747348156213)
          ·
            refine ⟨17852471712359695063889645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190426364931836747348156213 17852471712359695063889645)
            ·
              refine ⟨6694676892134885648958617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17852471712359695063889645 6694676892134885648958617)
              ·
                refine ⟨5021007669101164236718963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6694676892134885648958617 5021007669101164236718963)
                ·
                  refine ⟨7531511503651746355078445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021007669101164236718963 7531511503651746355078445)
                  ·
                    refine ⟨2824316813869404883154417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7531511503651746355078445 2824316813869404883154417)
                    ·
                      refine ⟨2118237610402053662365813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824316813869404883154417 2118237610402053662365813)
                      ·
                        rfl

theorem cell23_4125253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_4125253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125253 prefixEnd_4125253 := by exact prefixLift 4125253
  have htrace : WordTrace (prefixWord ++ tailWord_4125253) baseStart_4125253 baseEnd_4125253 := by
    simpa [prefixWord, tailWord_4125253, baseEnd_4125253] using wordTrace_append hprefix tailTrace_4125253
  have hstable : (prefixWord ++ tailWord_4125253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125253).length < 2 ^ (prefixWord ++ tailWord_4125253).sum := by decide
  have hdescent : baseEnd_4125253 < baseStart_4125253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125269 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4125269 : Nat := 118140960795 + 4125269 * 2 ^ 59
def prefixEnd_4125269 : Nat := 4983230072969 + 3 ^ 40 * 4125269 * 2
def baseEnd_4125269 : Nat := 2118245826092525599765739

theorem tailTrace_4125269 : CollatzResearch.WordTrace tailWord_4125269 prefixEnd_4125269 2118245826092525599765739 := by
  unfold tailWord_4125269
  simp only [CollatzResearch.WordTrace]
  refine ⟨150460921291862427699026861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100307280861241618466017907 150460921291862427699026861)
  ·
    refine ⟨56422845484448410387135073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150460921291862427699026861 56422845484448410387135073)
    ·
      refine ⟨42317134113336307790351305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56422845484448410387135073 42317134113336307790351305)
      ·
        refine ⟨31737850585002230842763479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42317134113336307790351305 31737850585002230842763479)
        ·
          refine ⟨47606775877503346264145219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31737850585002230842763479 47606775877503346264145219)
          ·
            refine ⟨71410163816255019396217829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47606775877503346264145219 71410163816255019396217829)
            ·
              refine ⟨13389405715547816136790843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71410163816255019396217829 13389405715547816136790843)
              ·
                refine ⟨20084108573321724205186265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13389405715547816136790843 20084108573321724205186265)
                ·
                  refine ⟨15063081429991293153889699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20084108573321724205186265 15063081429991293153889699)
                  ·
                    refine ⟨22594622144986939730834549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15063081429991293153889699 22594622144986939730834549)
                    ·
                      refine ⟨2118245826092525599765739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22594622144986939730834549 2118245826092525599765739)
                      ·
                        rfl

theorem cell23_4125269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4125269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125269 prefixEnd_4125269 := by exact prefixLift 4125269
  have htrace : WordTrace (prefixWord ++ tailWord_4125269) baseStart_4125269 baseEnd_4125269 := by
    simpa [prefixWord, tailWord_4125269, baseEnd_4125269] using wordTrace_append hprefix tailTrace_4125269
  have hstable : (prefixWord ++ tailWord_4125269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125269).length < 2 ^ (prefixWord ++ tailWord_4125269).sum := by decide
  have hdescent : baseEnd_4125269 < baseStart_4125269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125296 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 4]
def baseStart_4125296 : Nat := 118140960795 + 4125296 * 2 ^ 59
def prefixEnd_4125296 : Nat := 4983230072969 + 3 ^ 40 * 4125296 * 2
def baseEnd_4125296 : Nat := 2118259690070196994128115

theorem tailTrace_4125296 : CollatzResearch.WordTrace tailWord_4125296 prefixEnd_4125296 2118259690070196994128115 := by
  unfold tailWord_4125296
  simp only [CollatzResearch.WordTrace]
  refine ⟨75230953031382305655129871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100307937375176407540173161 75230953031382305655129871)
  ·
    refine ⟨112846429547073458482694807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75230953031382305655129871 112846429547073458482694807)
    ·
      refine ⟨169269644320610187724042211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112846429547073458482694807 169269644320610187724042211)
      ·
        refine ⟨253904466480915281586063317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169269644320610187724042211 253904466480915281586063317)
        ·
          refine ⟨5950885933146451912173359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 253904466480915281586063317 5950885933146451912173359)
          ·
            refine ⟨8926328899719677868260039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5950885933146451912173359 8926328899719677868260039)
            ·
              refine ⟨13389493349579516802390059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8926328899719677868260039 13389493349579516802390059)
              ·
                refine ⟨20084240024369275203585089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13389493349579516802390059 20084240024369275203585089)
                ·
                  refine ⟨15063180018276956402688817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20084240024369275203585089 15063180018276956402688817)
                  ·
                    refine ⟨11297385013707717302016613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15063180018276956402688817 11297385013707717302016613)
                    ·
                      refine ⟨2118259690070196994128115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11297385013707717302016613 2118259690070196994128115)
                      ·
                        rfl

theorem cell23_4125296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 4].length) (baseStart_4125296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125296 prefixEnd_4125296 := by exact prefixLift 4125296
  have htrace : WordTrace (prefixWord ++ tailWord_4125296) baseStart_4125296 baseEnd_4125296 := by
    simpa [prefixWord, tailWord_4125296, baseEnd_4125296] using wordTrace_append hprefix tailTrace_4125296
  have hstable : (prefixWord ++ tailWord_4125296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125296).length < 2 ^ (prefixWord ++ tailWord_4125296).sum := by decide
  have hdescent : baseEnd_4125296 < baseStart_4125296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125319 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 1, 7]
def baseStart_4125319 : Nat := 118140960795 + 4125319 * 2 ^ 59
def prefixEnd_4125319 : Nat := 4983230072969 + 3 ^ 40 * 4125319 * 2
def baseEnd_4125319 : Nat := 706090500041750134713503

theorem tailTrace_4125319 : CollatzResearch.WordTrace tailWord_4125319 prefixEnd_4125319 706090500041750134713503 := by
  unfold tailWord_4125319
  simp only [CollatzResearch.WordTrace]
  refine ⟨150462744941681286238347011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100308496627787524158898007 150462744941681286238347011)
  ·
    refine ⟨225694117412521929357520517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150462744941681286238347011 225694117412521929357520517)
    ·
      refine ⟨42317647014847861754535097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225694117412521929357520517 42317647014847861754535097)
      ·
        refine ⟨31738235261135896315901323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42317647014847861754535097 31738235261135896315901323)
        ·
          refine ⟨47607352891703844473851985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31738235261135896315901323 47607352891703844473851985)
          ·
            refine ⟨35705514668777883355388989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47607352891703844473851985 35705514668777883355388989)
            ·
              refine ⟨13389568000791706258270871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35705514668777883355388989 13389568000791706258270871)
              ·
                refine ⟨20084352001187559387406307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13389568000791706258270871 20084352001187559387406307)
                ·
                  refine ⟨30126528001781339081109461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20084352001187559387406307 30126528001781339081109461)
                  ·
                    refine ⟨706090500041750134713503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30126528001781339081109461 706090500041750134713503)
                    ·
                      rfl

theorem cell23_4125319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_4125319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125319 prefixEnd_4125319 := by exact prefixLift 4125319
  have htrace : WordTrace (prefixWord ++ tailWord_4125319) baseStart_4125319 baseEnd_4125319 := by
    simpa [prefixWord, tailWord_4125319, baseEnd_4125319] using wordTrace_append hprefix tailTrace_4125319
  have hstable : (prefixWord ++ tailWord_4125319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125319).length < 2 ^ (prefixWord ++ tailWord_4125319).sum := by decide
  have hdescent : baseEnd_4125319 < baseStart_4125319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125339 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 4]
def baseStart_4125339 : Nat := 118140960795 + 4125339 * 2 ^ 59
def prefixEnd_4125339 : Nat := 4983230072969 + 3 ^ 40 * 4125339 * 2
def baseEnd_4125339 : Nat := 2118281769738340325890417

theorem tailTrace_4125339 : CollatzResearch.WordTrace tailWord_4125339 prefixEnd_4125339 2118281769738340325890417 := by
  unfold tailWord_4125339
  simp only [CollatzResearch.WordTrace]
  refine ⟨150463474401608829654075071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100308982934405886436050047 150463474401608829654075071)
  ·
    refine ⟨225695211602413244481112607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150463474401608829654075071 225695211602413244481112607)
    ·
      refine ⟨338542817403619866721668911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225695211602413244481112607 338542817403619866721668911)
      ·
        refine ⟨507814226105429800082503367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338542817403619866721668911 507814226105429800082503367)
        ·
          refine ⟨761721339158144700123755051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507814226105429800082503367 761721339158144700123755051)
          ·
            refine ⟨1142582008737217050185632577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761721339158144700123755051 1142582008737217050185632577)
            ·
              refine ⟨856936506552912787639224433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142582008737217050185632577 856936506552912787639224433)
              ·
                refine ⟨642702379914684590729418325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856936506552912787639224433 642702379914684590729418325)
                ·
                  refine ⟨7531668514625210047610371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 642702379914684590729418325 7531668514625210047610371)
                  ·
                    refine ⟨11297502771937815071415557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7531668514625210047610371 11297502771937815071415557)
                    ·
                      refine ⟨2118281769738340325890417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11297502771937815071415557 2118281769738340325890417)
                      ·
                        rfl

theorem cell23_4125339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 4].length) (baseStart_4125339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125339 prefixEnd_4125339 := by exact prefixLift 4125339
  have htrace : WordTrace (prefixWord ++ tailWord_4125339) baseStart_4125339 baseEnd_4125339 := by
    simpa [prefixWord, tailWord_4125339, baseEnd_4125339] using wordTrace_append hprefix tailTrace_4125339
  have hstable : (prefixWord ++ tailWord_4125339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125339).length < 2 ^ (prefixWord ++ tailWord_4125339).sum := by decide
  have hdescent : baseEnd_4125339 < baseStart_4125339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125369 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_4125369 : Nat := 118140960795 + 4125369 * 2 ^ 59
def prefixEnd_4125369 : Nat := 4983230072969 + 3 ^ 40 * 4125369 * 2
def baseEnd_4125369 : Nat := 2118297174157975208515279

theorem tailTrace_4125369 : CollatzResearch.WordTrace tailWord_4125369 prefixEnd_4125369 2118297174157975208515279 := by
  unfold tailWord_4125369
  simp only [CollatzResearch.WordTrace]
  refine ⟨150464568591500144777667161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100309712394333429851778107 150464568591500144777667161)
  ·
    refine ⟨112848426443625108583250371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150464568591500144777667161 112848426443625108583250371)
    ·
      refine ⟨169272639665437662874875557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112848426443625108583250371 169272639665437662874875557)
      ·
        refine ⟨31738619937269561789039167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169272639665437662874875557 31738619937269561789039167)
        ·
          refine ⟨47607929905904342683558751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31738619937269561789039167 47607929905904342683558751)
          ·
            refine ⟨71411894858856514025338127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47607929905904342683558751 71411894858856514025338127)
            ·
              refine ⟨107117842288284771038007191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71411894858856514025338127 107117842288284771038007191)
              ·
                refine ⟨160676763432427156557010787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107117842288284771038007191 160676763432427156557010787)
                ·
                  refine ⟨241015145148640734835516181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160676763432427156557010787 241015145148640734835516181)
                  ·
                    refine ⟨11297584928842534445414821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 241015145148640734835516181 11297584928842534445414821)
                    ·
                      refine ⟨2118297174157975208515279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11297584928842534445414821 2118297174157975208515279)
                      ·
                        rfl

theorem cell23_4125369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_4125369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125369 prefixEnd_4125369 := by exact prefixLift 4125369
  have htrace : WordTrace (prefixWord ++ tailWord_4125369) baseStart_4125369 baseEnd_4125369 := by
    simpa [prefixWord, tailWord_4125369, baseEnd_4125369] using wordTrace_append hprefix tailTrace_4125369
  have hstable : (prefixWord ++ tailWord_4125369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125369).length < 2 ^ (prefixWord ++ tailWord_4125369).sum := by decide
  have hdescent : baseEnd_4125369 < baseStart_4125369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125376 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 3]
def baseStart_4125376 : Nat := 118140960795 + 4125376 * 2 ^ 59
def prefixEnd_4125376 : Nat := 4983230072969 + 3 ^ 40 * 4125376 * 2
def baseEnd_4125376 : Nat := 2118300768522556681127747

theorem tailTrace_4125376 : CollatzResearch.WordTrace tailWord_4125376 prefixEnd_4125376 2118300768522556681127747 := by
  unfold tailWord_4125376
  simp only [CollatzResearch.WordTrace]
  refine ⟨75232411951237392486585991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100309882601649856648781321 75232411951237392486585991)
  ·
    refine ⟨112848617926856088729878987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75232411951237392486585991 112848617926856088729878987)
    ·
      refine ⟨169272926890284133094818481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112848617926856088729878987 169272926890284133094818481)
      ·
        refine ⟨126954695167713099821113861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169272926890284133094818481 126954695167713099821113861)
        ·
          refine ⟨23804005343946206216458849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126954695167713099821113861 23804005343946206216458849)
          ·
            refine ⟨17853004007959654662344137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23804005343946206216458849 17853004007959654662344137)
            ·
              refine ⟨13389753005969740996758103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17853004007959654662344137 13389753005969740996758103)
              ·
                refine ⟨20084629508954611495137155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13389753005969740996758103 20084629508954611495137155)
                ·
                  refine ⟨30126944263431917242705733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20084629508954611495137155 30126944263431917242705733)
                  ·
                    refine ⟨5648802049393484483007325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30126944263431917242705733 5648802049393484483007325)
                    ·
                      refine ⟨2118300768522556681127747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5648802049393484483007325 2118300768522556681127747)
                      ·
                        rfl

theorem cell23_4125376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_4125376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125376 prefixEnd_4125376 := by exact prefixLift 4125376
  have htrace : WordTrace (prefixWord ++ tailWord_4125376) baseStart_4125376 baseEnd_4125376 := by
    simpa [prefixWord, tailWord_4125376, baseEnd_4125376] using wordTrace_append hprefix tailTrace_4125376
  have hstable : (prefixWord ++ tailWord_4125376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125376).length < 2 ^ (prefixWord ++ tailWord_4125376).sum := by decide
  have hdescent : baseEnd_4125376 < baseStart_4125376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125383 : List Nat := [1, 1, 4, 1, 1, 1, 2, 7, 1, 4]
def baseStart_4125383 : Nat := 118140960795 + 4125383 * 2 ^ 59
def prefixEnd_4125383 : Nat := 4983230072969 + 3 ^ 40 * 4125383 * 2
def baseEnd_4125383 : Nat := 706101454295712717913405

theorem tailTrace_4125383 : CollatzResearch.WordTrace tailWord_4125383 prefixEnd_4125383 706101454295712717913405 := by
  unfold tailWord_4125383
  simp only [CollatzResearch.WordTrace]
  refine ⟨150465079213449425168676803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100310052808966283445784535 150465079213449425168676803)
  ·
    refine ⟨225697618820174137753015205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150465079213449425168676803 225697618820174137753015205)
    ·
      refine ⟨42318303528782650828690351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225697618820174137753015205 42318303528782650828690351)
      ·
        refine ⟨63477455293173976243035527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42318303528782650828690351 63477455293173976243035527)
        ·
          refine ⟨95216182939760964364553291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63477455293173976243035527 95216182939760964364553291)
          ·
            refine ⟨142824274409641446546829937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95216182939760964364553291 142824274409641446546829937)
            ·
              refine ⟨107118205807231084910122453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142824274409641446546829937 107118205807231084910122453)
              ·
                refine ⟨2510582948606978552580995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 107118205807231084910122453 2510582948606978552580995)
                ·
                  refine ⟨3765874422910467828871493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510582948606978552580995 3765874422910467828871493)
                  ·
                    refine ⟨706101454295712717913405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3765874422910467828871493 706101454295712717913405)
                    ·
                      rfl

theorem cell23_4125383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_4125383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125383 prefixEnd_4125383 := by exact prefixLift 4125383
  have htrace : WordTrace (prefixWord ++ tailWord_4125383) baseStart_4125383 baseEnd_4125383 := by
    simpa [prefixWord, tailWord_4125383, baseEnd_4125383] using wordTrace_append hprefix tailTrace_4125383
  have hstable : (prefixWord ++ tailWord_4125383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125383).length < 2 ^ (prefixWord ++ tailWord_4125383).sum := by decide
  have hdescent : baseEnd_4125383 < baseStart_4125383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125413 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 6]
def baseStart_4125413 : Nat := 118140960795 + 4125413 * 2 ^ 59
def prefixEnd_4125413 : Nat := 4983230072969 + 3 ^ 40 * 4125413 * 2
def baseEnd_4125413 : Nat := 235368863034085892929453

theorem tailTrace_4125413 : CollatzResearch.WordTrace tailWord_4125413 prefixEnd_4125413 235368863034085892929453 := by
  unfold tailWord_4125413
  simp only [CollatzResearch.WordTrace]
  refine ⟨150466173403340740292268893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100310782268893826861512595 150466173403340740292268893)
  ·
    refine ⟨56424815026252777609600835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150466173403340740292268893 56424815026252777609600835)
    ·
      refine ⟨84637222539379166414401253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56424815026252777609600835 84637222539379166414401253)
      ·
        refine ⟨15869479226133593702700235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84637222539379166414401253 15869479226133593702700235)
        ·
          refine ⟨23804218839200390554050353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15869479226133593702700235 23804218839200390554050353)
          ·
            refine ⟨17853164129400292915537765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23804218839200390554050353 17853164129400292915537765)
            ·
              refine ⟨3347468274262554921663331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17853164129400292915537765 3347468274262554921663331)
              ·
                refine ⟨5021202411393832382494997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347468274262554921663331 5021202411393832382494997)
                ·
                  refine ⟨235368863034085892929453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5021202411393832382494997 235368863034085892929453)
                  ·
                    rfl

theorem cell23_4125413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_4125413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125413 prefixEnd_4125413 := by exact prefixLift 4125413
  have htrace : WordTrace (prefixWord ++ tailWord_4125413) baseStart_4125413 baseEnd_4125413 := by
    simpa [prefixWord, tailWord_4125413, baseEnd_4125413] using wordTrace_append hprefix tailTrace_4125413
  have hstable : (prefixWord ++ tailWord_4125413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125413).length < 2 ^ (prefixWord ++ tailWord_4125413).sum := by decide
  have hdescent : baseEnd_4125413 < baseStart_4125413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125457 : List Nat := [1, 2, 2, 1, 1, 3, 6, 2, 1, 1, 3]
def baseStart_4125457 : Nat := 118140960795 + 4125457 * 2 ^ 59
def prefixEnd_4125457 : Nat := 4983230072969 + 3 ^ 40 * 4125457 * 2
def baseEnd_4125457 : Nat := 2118342360455570864214875

theorem tailTrace_4125457 : CollatzResearch.WordTrace tailWord_4125457 prefixEnd_4125457 2118342360455570864214875 := by
  unfold tailWord_4125457
  simp only [CollatzResearch.WordTrace]
  refine ⟨150467778215181335806870625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100311852143454223871247083 150467778215181335806870625)
  ·
    refine ⟨112850833661386001855152969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150467778215181335806870625 112850833661386001855152969)
    ·
      refine ⟨84638125246039501391364727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112850833661386001855152969 84638125246039501391364727)
      ·
        refine ⟨126957187869059252087047091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84638125246039501391364727 126957187869059252087047091)
        ·
          refine ⟨190435781803588878130570637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126957187869059252087047091 190435781803588878130570637)
          ·
            refine ⟨71413418176345829298963989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190435781803588878130570637 71413418176345829298963989)
            ·
              refine ⟨3347503977016210748388937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71413418176345829298963989 3347503977016210748388937)
              ·
                refine ⟨2510627982762158061291703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3347503977016210748388937 2510627982762158061291703)
                ·
                  refine ⟨3765941974143237091937555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510627982762158061291703 3765941974143237091937555)
                  ·
                    refine ⟨5648912961214855637906333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3765941974143237091937555 5648912961214855637906333)
                    ·
                      refine ⟨2118342360455570864214875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5648912961214855637906333 2118342360455570864214875)
                      ·
                        rfl

theorem cell23_4125457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 1, 1, 3].length) (baseStart_4125457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125457 prefixEnd_4125457 := by exact prefixLift 4125457
  have htrace : WordTrace (prefixWord ++ tailWord_4125457) baseStart_4125457 baseEnd_4125457 := by
    simpa [prefixWord, tailWord_4125457, baseEnd_4125457] using wordTrace_append hprefix tailTrace_4125457
  have hstable : (prefixWord ++ tailWord_4125457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125457).length < 2 ^ (prefixWord ++ tailWord_4125457).sum := by decide
  have hdescent : baseEnd_4125457 < baseStart_4125457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125466 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_4125466 : Nat := 118140960795 + 4125466 * 2 ^ 59
def prefixEnd_4125466 : Nat := 4983230072969 + 3 ^ 40 * 4125466 * 2
def baseEnd_4125466 : Nat := 2118346981781461329002333

theorem tailTrace_4125466 : CollatzResearch.WordTrace tailWord_4125466 prefixEnd_4125466 2118346981781461329002333 := by
  unfold tailWord_4125466
  simp only [CollatzResearch.WordTrace]
  refine ⟨37617026618037182585987063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100312070981432486895965501 37617026618037182585987063)
  ·
    refine ⟨56425539927055773878980595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37617026618037182585987063 56425539927055773878980595)
    ·
      refine ⟨84638309890583660818470893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56425539927055773878980595 84638309890583660818470893)
      ·
        refine ⟨31739366208968872806926585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84638309890583660818470893 31739366208968872806926585)
        ·
          refine ⟨23804524656726654605194939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31739366208968872806926585 23804524656726654605194939)
          ·
            refine ⟨35706786985089981907792409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23804524656726654605194939 35706786985089981907792409)
            ·
              refine ⟨26780090238817486430844307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35706786985089981907792409 26780090238817486430844307)
              ·
                refine ⟨40170135358226229646266461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26780090238817486430844307 40170135358226229646266461)
                ·
                  refine ⟨15063800759334836117349923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40170135358226229646266461 15063800759334836117349923)
                  ·
                    refine ⟨22595701139002254176024885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15063800759334836117349923 22595701139002254176024885)
                    ·
                      refine ⟨2118346981781461329002333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22595701139002254176024885 2118346981781461329002333)
                      ·
                        rfl

theorem cell23_4125466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_4125466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125466 prefixEnd_4125466 := by exact prefixLift 4125466
  have htrace : WordTrace (prefixWord ++ tailWord_4125466) baseStart_4125466 baseEnd_4125466 := by
    simpa [prefixWord, tailWord_4125466, baseEnd_4125466] using wordTrace_append hprefix tailTrace_4125466
  have hstable : (prefixWord ++ tailWord_4125466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125466).length < 2 ^ (prefixWord ++ tailWord_4125466).sum := by decide
  have hdescent : baseEnd_4125466 < baseStart_4125466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125473 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 2, 4]
def baseStart_4125473 : Nat := 118140960795 + 4125473 * 2 ^ 59
def prefixEnd_4125473 : Nat := 4983230072969 + 3 ^ 40 * 4125473 * 2
def baseEnd_4125473 : Nat := 706116858715347600538267

theorem tailTrace_4125473 : CollatzResearch.WordTrace tailWord_4125473 prefixEnd_4125473 706116858715347600538267 := by
  unfold tailWord_4125473
  simp only [CollatzResearch.WordTrace]
  refine ⟨150468361783123370539453073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100312241188748913692968715 150468361783123370539453073)
  ·
    refine ⟨112851271337342527904589805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150468361783123370539453073 112851271337342527904589805)
    ·
      refine ⟨42319226751503447964221177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112851271337342527904589805 42319226751503447964221177)
      ·
        refine ⟨31739420063627585973165883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42319226751503447964221177 31739420063627585973165883)
        ·
          refine ⟨47609130095441378959748825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31739420063627585973165883 47609130095441378959748825)
          ·
            refine ⟨35706847571581034219811619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47609130095441378959748825 35706847571581034219811619)
            ·
              refine ⟨53560271357371551329717429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35706847571581034219811619 53560271357371551329717429)
              ·
                refine ⟨5021275439753582937161009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53560271357371551329717429 5021275439753582937161009)
                ·
                  refine ⟨3765956579815187202870757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5021275439753582937161009 3765956579815187202870757)
                  ·
                    refine ⟨706116858715347600538267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3765956579815187202870757 706116858715347600538267)
                    ·
                      rfl

theorem cell23_4125473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_4125473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125473 prefixEnd_4125473 := by exact prefixLift 4125473
  have htrace : WordTrace (prefixWord ++ tailWord_4125473) baseStart_4125473 baseEnd_4125473 := by
    simpa [prefixWord, tailWord_4125473, baseEnd_4125473] using wordTrace_append hprefix tailTrace_4125473
  have hstable : (prefixWord ++ tailWord_4125473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125473).length < 2 ^ (prefixWord ++ tailWord_4125473).sum := by decide
  have hdescent : baseEnd_4125473 < baseStart_4125473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125493 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_4125493 : Nat := 118140960795 + 4125493 * 2 ^ 59
def prefixEnd_4125493 : Nat := 4983230072969 + 3 ^ 40 * 4125493 * 2
def baseEnd_4125493 : Nat := 2118360845759132723364709

theorem tailTrace_4125493 : CollatzResearch.WordTrace tailWord_4125493 prefixEnd_4125493 2118360845759132723364709 := by
  unfold tailWord_4125493
  simp only [CollatzResearch.WordTrace]
  refine ⟨150469091243050913955181133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100312727495367275970120755 150469091243050913955181133)
  ·
    refine ⟨56425909216144092733192925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150469091243050913955181133 56425909216144092733192925)
    ·
      refine ⟨21159715956054034774947347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56425909216144092733192925 21159715956054034774947347)
      ·
        refine ⟨31739573934081052162421021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21159715956054034774947347 31739573934081052162421021)
        ·
          refine ⟨11902340225280394560907883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31739573934081052162421021 11902340225280394560907883)
          ·
            refine ⟨17853510337920591841361825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11902340225280394560907883 17853510337920591841361825)
            ·
              refine ⟨13390132753440443881021369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17853510337920591841361825 13390132753440443881021369)
              ·
                refine ⟨10042599565080332910766027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13390132753440443881021369 10042599565080332910766027)
                ·
                  refine ⟨15063899347620499366149041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10042599565080332910766027 15063899347620499366149041)
                  ·
                    refine ⟨11297924510715374524611781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15063899347620499366149041 11297924510715374524611781)
                    ·
                      refine ⟨2118360845759132723364709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11297924510715374524611781 2118360845759132723364709)
                      ·
                        rfl

theorem cell23_4125493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_4125493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125493 prefixEnd_4125493 := by exact prefixLift 4125493
  have htrace : WordTrace (prefixWord ++ tailWord_4125493) baseStart_4125493 baseEnd_4125493 := by
    simpa [prefixWord, tailWord_4125493, baseEnd_4125493] using wordTrace_append hprefix tailTrace_4125493
  have hstable : (prefixWord ++ tailWord_4125493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125493).length < 2 ^ (prefixWord ++ tailWord_4125493).sum := by decide
  have hdescent : baseEnd_4125493 < baseStart_4125493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125494 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_4125494 : Nat := 118140960795 + 4125494 * 2 ^ 59
def prefixEnd_4125494 : Nat := 4983230072969 + 3 ^ 40 * 4125494 * 2
def baseEnd_4125494 : Nat := 706120453079929073150735

theorem tailTrace_4125494 : CollatzResearch.WordTrace tailWord_4125494 prefixEnd_4125494 706120453079929073150735 := by
  unfold tailWord_4125494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404320482252955695372971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100312751810698194083978357 9404320482252955695372971)
  ·
    refine ⟨14106480723379433543059457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9404320482252955695372971 14106480723379433543059457)
    ·
      refine ⟨10579860542534575157294593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14106480723379433543059457 10579860542534575157294593)
      ·
        refine ⟨7934895406900931367970945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10579860542534575157294593 7934895406900931367970945)
        ·
          refine ⟨5951171555175698525978209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7934895406900931367970945 5951171555175698525978209)
          ·
            refine ⟨4463378666381773894483657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5951171555175698525978209 4463378666381773894483657)
            ·
              refine ⟨3347533999786330420862743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4463378666381773894483657 3347533999786330420862743)
              ·
                refine ⟨5021300999679495631294115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347533999786330420862743 5021300999679495631294115)
                ·
                  refine ⟨7531951499519243446941173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021300999679495631294115 7531951499519243446941173)
                  ·
                    refine ⟨706120453079929073150735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7531951499519243446941173 706120453079929073150735)
                    ·
                      rfl

theorem cell23_4125494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_4125494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125494 prefixEnd_4125494 := by exact prefixLift 4125494
  have htrace : WordTrace (prefixWord ++ tailWord_4125494) baseStart_4125494 baseEnd_4125494 := by
    simpa [prefixWord, tailWord_4125494, baseEnd_4125494] using wordTrace_append hprefix tailTrace_4125494
  have hstable : (prefixWord ++ tailWord_4125494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125494).length < 2 ^ (prefixWord ++ tailWord_4125494).sum := by decide
  have hdescent : baseEnd_4125494 < baseStart_4125494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125523 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 5, 3, 2]
def baseStart_4125523 : Nat := 118140960795 + 4125523 * 2 ^ 59
def prefixEnd_4125523 : Nat := 4983230072969 + 3 ^ 40 * 4125523 * 2
def baseEnd_4125523 : Nat := 2118376250178767605989571

theorem tailTrace_4125523 : CollatzResearch.WordTrace tailWord_4125523 prefixEnd_4125523 2118376250178767605989571 := by
  unfold tailWord_4125523
  simp only [CollatzResearch.WordTrace]
  refine ⟨150470185432942229078773223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100313456955294819385848815 150470185432942229078773223)
  ·
    refine ⟨225705278149413343618159835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150470185432942229078773223 225705278149413343618159835)
    ·
      refine ⟨338557917224120015427239753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225705278149413343618159835 338557917224120015427239753)
      ·
        refine ⟨253918437918090011570429815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338557917224120015427239753 253918437918090011570429815)
        ·
          refine ⟨380877656877135017355644723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253918437918090011570429815 380877656877135017355644723)
          ·
            refine ⟨571316485315702526033467085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380877656877135017355644723 571316485315702526033467085)
            ·
              refine ⟨214243681993388447262550157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 571316485315702526033467085 214243681993388447262550157)
              ·
                refine ⟨80341380747520667723456309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214243681993388447262550157 80341380747520667723456309)
                ·
                  refine ⟨7532004445080062599074029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80341380747520667723456309 7532004445080062599074029)
                  ·
                    refine ⟨2824501666905023474652761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7532004445080062599074029 2824501666905023474652761)
                    ·
                      refine ⟨2118376250178767605989571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824501666905023474652761 2118376250178767605989571)
                      ·
                        rfl

theorem cell23_4125523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 3, 2].length) (baseStart_4125523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125523 prefixEnd_4125523 := by exact prefixLift 4125523
  have htrace : WordTrace (prefixWord ++ tailWord_4125523) baseStart_4125523 baseEnd_4125523 := by
    simpa [prefixWord, tailWord_4125523, baseEnd_4125523] using wordTrace_append hprefix tailTrace_4125523
  have hstable : (prefixWord ++ tailWord_4125523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125523).length < 2 ^ (prefixWord ++ tailWord_4125523).sum := by decide
  have hdescent : baseEnd_4125523 < baseStart_4125523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125530 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3]
def baseStart_4125530 : Nat := 118140960795 + 4125530 * 2 ^ 59
def prefixEnd_4125530 : Nat := 4983230072969 + 3 ^ 40 * 4125530 * 2
def baseEnd_4125530 : Nat := 2118379844543349078602039

theorem tailTrace_4125530 : CollatzResearch.WordTrace tailWord_4125530 prefixEnd_4125530 2118379844543349078602039 := by
  unfold tailWord_4125530
  simp only [CollatzResearch.WordTrace]
  refine ⟨37617610185979217318569511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100313627162611246182852029 37617610185979217318569511)
  ·
    refine ⟨56426415278968825977854267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37617610185979217318569511 56426415278968825977854267)
    ·
      refine ⟨84639622918453238966781401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56426415278968825977854267 84639622918453238966781401)
      ·
        refine ⟨63479717188839929225086051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84639622918453238966781401 63479717188839929225086051)
        ·
          refine ⟨95219575783259893837629077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63479717188839929225086051 95219575783259893837629077)
          ·
            refine ⟨4463417614840307523638863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95219575783259893837629077 4463417614840307523638863)
            ·
              refine ⟨6695126422260461285458295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4463417614840307523638863 6695126422260461285458295)
              ·
                refine ⟨10042689633390691928187443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6695126422260461285458295 10042689633390691928187443)
                ·
                  refine ⟨15064034450086037892281165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10042689633390691928187443 15064034450086037892281165)
                  ·
                    refine ⟨5649012918782264209605437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15064034450086037892281165 5649012918782264209605437)
                    ·
                      refine ⟨2118379844543349078602039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5649012918782264209605437 2118379844543349078602039)
                      ·
                        rfl

theorem cell23_4125530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_4125530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125530 prefixEnd_4125530 := by exact prefixLift 4125530
  have htrace : WordTrace (prefixWord ++ tailWord_4125530) baseStart_4125530 baseEnd_4125530 := by
    simpa [prefixWord, tailWord_4125530, baseEnd_4125530] using wordTrace_append hprefix tailTrace_4125530
  have hstable : (prefixWord ++ tailWord_4125530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125530).length < 2 ^ (prefixWord ++ tailWord_4125530).sum := by decide
  have hdescent : baseEnd_4125530 < baseStart_4125530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125557 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_4125557 : Nat := 118140960795 + 4125557 * 2 ^ 59
def prefixEnd_4125557 : Nat := 4983230072969 + 3 ^ 40 * 4125557 * 2
def baseEnd_4125557 : Nat := 2118393708521020472964415

theorem tailTrace_4125557 : CollatzResearch.WordTrace tailWord_4125557 prefixEnd_4125557 2118393708521020472964415 := by
  unfold tailWord_4125557
  simp only [CollatzResearch.WordTrace]
  refine ⟨150471425514819052885510925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100314283676546035257007283 150471425514819052885510925)
  ·
    refine ⟨56426784568057144832066597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150471425514819052885510925 56426784568057144832066597)
    ·
      refine ⟨10580022106510714656012487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56426784568057144832066597 10580022106510714656012487)
      ·
        refine ⟨15870033159766071984018731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10580022106510714656012487 15870033159766071984018731)
        ·
          refine ⟨23805049739649107976028097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15870033159766071984018731 23805049739649107976028097)
          ·
            refine ⟨17853787304736830982021073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23805049739649107976028097 17853787304736830982021073)
            ·
              refine ⟨13390340478552623236515805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17853787304736830982021073 13390340478552623236515805)
              ·
                refine ⟨5021377679457233713693427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13390340478552623236515805 5021377679457233713693427)
                ·
                  refine ⟨7532066519185850570540141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021377679457233713693427 7532066519185850570540141)
                  ·
                    refine ⟨2824524944694693963952553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7532066519185850570540141 2824524944694693963952553)
                    ·
                      refine ⟨2118393708521020472964415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824524944694693963952553 2118393708521020472964415)
                      ·
                        rfl

theorem cell23_4125557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_4125557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125557 prefixEnd_4125557 := by exact prefixLift 4125557
  have htrace : WordTrace (prefixWord ++ tailWord_4125557) baseStart_4125557 baseEnd_4125557 := by
    simpa [prefixWord, tailWord_4125557, baseEnd_4125557] using wordTrace_append hprefix tailTrace_4125557
  have hstable : (prefixWord ++ tailWord_4125557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125557).length < 2 ^ (prefixWord ++ tailWord_4125557).sum := by decide
  have hdescent : baseEnd_4125557 < baseStart_4125557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125623 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 2, 5]
def baseStart_4125623 : Nat := 118140960795 + 4125623 * 2 ^ 59
def prefixEnd_4125623 : Nat := 4983230072969 + 3 ^ 40 * 4125623 * 2
def baseEnd_4125623 : Nat := 706142532748072404913037

theorem tailTrace_4125623 : CollatzResearch.WordTrace tailWord_4125623 prefixEnd_4125623 706142532748072404913037 := by
  unfold tailWord_4125623
  simp only [CollatzResearch.WordTrace]
  refine ⟨150473832732579946157413523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100315888488386630771609015 150473832732579946157413523)
  ·
    refine ⟨225710749098869919236120285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150473832732579946157413523 225710749098869919236120285)
    ·
      refine ⟨84641530912076219713545107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225710749098869919236120285 84641530912076219713545107)
      ·
        refine ⟨126962296368114329570317661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84641530912076219713545107 126962296368114329570317661)
        ·
          refine ⟨47610861138042873588869123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126962296368114329570317661 47610861138042873588869123)
          ·
            refine ⟨71416291707064310383303685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47610861138042873588869123 71416291707064310383303685)
            ·
              refine ⟨13390554695074558196869441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71416291707064310383303685 13390554695074558196869441)
              ·
                refine ⟨10042916021305918647652081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13390554695074558196869441 10042916021305918647652081)
                ·
                  refine ⟨7532187015979438985739061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10042916021305918647652081 7532187015979438985739061)
                  ·
                    refine ⟨706142532748072404913037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7532187015979438985739061 706142532748072404913037)
                    ·
                      rfl

theorem cell23_4125623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_4125623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125623 prefixEnd_4125623 := by exact prefixLift 4125623
  have htrace : WordTrace (prefixWord ++ tailWord_4125623) baseStart_4125623 baseEnd_4125623 := by
    simpa [prefixWord, tailWord_4125623, baseEnd_4125623] using wordTrace_append hprefix tailTrace_4125623
  have hstable : (prefixWord ++ tailWord_4125623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125623).length < 2 ^ (prefixWord ++ tailWord_4125623).sum := by decide
  have hdescent : baseEnd_4125623 < baseStart_4125623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125630 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_4125630 : Nat := 118140960795 + 4125630 * 2 ^ 59
def prefixEnd_4125630 : Nat := 4983230072969 + 3 ^ 40 * 4125630 * 2
def baseEnd_4125630 : Nat := 2118431192608798687351579

theorem tailTrace_4125630 : CollatzResearch.WordTrace tailWord_4125630 prefixEnd_4125630 2118431192608798687351579 := by
  unfold tailWord_4125630
  simp only [CollatzResearch.WordTrace]
  refine ⟨18809261005444323294114793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100316058695703057568612229 18809261005444323294114793)
  ·
    refine ⟨14106945754083242470586095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18809261005444323294114793 14106945754083242470586095)
    ·
      refine ⟨21160418631124863705879143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14106945754083242470586095 21160418631124863705879143)
      ·
        refine ⟨31740627946687295558818715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21160418631124863705879143 31740627946687295558818715)
        ·
          refine ⟨47610941920030943338228073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31740627946687295558818715 47610941920030943338228073)
          ·
            refine ⟨35708206440023207503671055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47610941920030943338228073 35708206440023207503671055)
            ·
              refine ⟨53562309660034811255506583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35708206440023207503671055 53562309660034811255506583)
              ·
                refine ⟨80343464490052216883259875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53562309660034811255506583 80343464490052216883259875)
                ·
                  refine ⟨120515196735078325324889813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80343464490052216883259875 120515196735078325324889813)
                  ·
                    refine ⟨2824574923478398249802105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 120515196735078325324889813 2824574923478398249802105)
                    ·
                      refine ⟨2118431192608798687351579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824574923478398249802105 2118431192608798687351579)
                      ·
                        rfl

theorem cell23_4125630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_4125630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125630 prefixEnd_4125630 := by exact prefixLift 4125630
  have htrace : WordTrace (prefixWord ++ tailWord_4125630) baseStart_4125630 baseEnd_4125630 := by
    simpa [prefixWord, tailWord_4125630, baseEnd_4125630] using wordTrace_append hprefix tailTrace_4125630
  have hstable : (prefixWord ++ tailWord_4125630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125630).length < 2 ^ (prefixWord ++ tailWord_4125630).sum := by decide
  have hdescent : baseEnd_4125630 < baseStart_4125630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125703 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_4125703 : Nat := 118140960795 + 4125703 * 2 ^ 59
def prefixEnd_4125703 : Nat := 4983230072969 + 3 ^ 40 * 4125703 * 2
def baseEnd_4125703 : Nat := 2118468676696576901738743

theorem tailTrace_4125703 : CollatzResearch.WordTrace tailWord_4125703 prefixEnd_4125703 2118468676696576901738743 := by
  unfold tailWord_4125703
  simp only [CollatzResearch.WordTrace]
  refine ⟨150476750572290119820325763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100317833714860079880217175 150476750572290119820325763)
  ·
    refine ⟨225715125858435179730488645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150476750572290119820325763 225715125858435179730488645)
    ·
      refine ⟨42321586098456596199466621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225715125858435179730488645 42321586098456596199466621)
      ·
        refine ⟨15870594786921223574799983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42321586098456596199466621 15870594786921223574799983)
        ·
          refine ⟨23805892180381835362199975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15870594786921223574799983 23805892180381835362199975)
          ·
            refine ⟨35708838270572753043299963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23805892180381835362199975 35708838270572753043299963)
            ·
              refine ⟨53563257405859129564949945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35708838270572753043299963 53563257405859129564949945)
              ·
                refine ⟨40172443054394347173712459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53563257405859129564949945 40172443054394347173712459)
                ·
                  refine ⟨60258664581591520760568689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40172443054394347173712459 60258664581591520760568689)
                  ·
                    refine ⟨45193998436193640570426517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60258664581591520760568689 45193998436193640570426517)
                    ·
                      refine ⟨2118468676696576901738743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45193998436193640570426517 2118468676696576901738743)
                      ·
                        rfl

theorem cell23_4125703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_4125703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125703 prefixEnd_4125703 := by exact prefixLift 4125703
  have htrace : WordTrace (prefixWord ++ tailWord_4125703) baseStart_4125703 baseEnd_4125703 := by
    simpa [prefixWord, tailWord_4125703, baseEnd_4125703] using wordTrace_append hprefix tailTrace_4125703
  have hstable : (prefixWord ++ tailWord_4125703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125703).length < 2 ^ (prefixWord ++ tailWord_4125703).sum := by decide
  have hdescent : baseEnd_4125703 < baseStart_4125703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125713 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 3, 5]
def baseStart_4125713 : Nat := 118140960795 + 4125713 * 2 ^ 59
def prefixEnd_4125713 : Nat := 4983230072969 + 3 ^ 40 * 4125713 * 2
def baseEnd_4125713 : Nat := 706157937167707287537899

theorem tailTrace_4125713 : CollatzResearch.WordTrace tailWord_4125713 prefixEnd_4125713 706157937167707287537899 := by
  unfold tailWord_4125713
  simp only [CollatzResearch.WordTrace]
  refine ⟨150477115302253891528189793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100318076868169261018793195 150477115302253891528189793)
  ·
    refine ⟨112857836476690418646142345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150477115302253891528189793 112857836476690418646142345)
    ·
      refine ⟨84643377357517813984606759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112857836476690418646142345 84643377357517813984606759)
      ·
        refine ⟨126965066036276720976910139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84643377357517813984606759 126965066036276720976910139)
        ·
          refine ⟨190447599054415081465365209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126965066036276720976910139 190447599054415081465365209)
          ·
            refine ⟨142835699290811311099023907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190447599054415081465365209 142835699290811311099023907)
            ·
              refine ⟨214253548936216966648535861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142835699290811311099023907 214253548936216966648535861)
              ·
                refine ⟨20086270212770340623300237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214253548936216966648535861 20086270212770340623300237)
                ·
                  refine ⟨7532351329788877733737589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20086270212770340623300237 7532351329788877733737589)
                  ·
                    refine ⟨706157937167707287537899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7532351329788877733737589 706157937167707287537899)
                    ·
                      rfl

theorem cell23_4125713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_4125713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125713 prefixEnd_4125713 := by exact prefixLift 4125713
  have htrace : WordTrace (prefixWord ++ tailWord_4125713) baseStart_4125713 baseEnd_4125713 := by
    simpa [prefixWord, tailWord_4125713, baseEnd_4125713] using wordTrace_append hprefix tailTrace_4125713
  have hstable : (prefixWord ++ tailWord_4125713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125713).length < 2 ^ (prefixWord ++ tailWord_4125713).sum := by decide
  have hdescent : baseEnd_4125713 < baseStart_4125713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125763 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 6]
def baseStart_4125763 : Nat := 118140960795 + 4125763 * 2 ^ 59
def prefixEnd_4125763 : Nat := 4983230072969 + 3 ^ 40 * 4125763 * 2
def baseEnd_4125763 : Nat := 2118499485535846666988467

theorem tailTrace_4125763 : CollatzResearch.WordTrace tailWord_4125763 prefixEnd_4125763 2118499485535846666988467 := by
  unfold tailWord_4125763
  simp only [CollatzResearch.WordTrace]
  refine ⟨150478938952072750067509943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100319292634715166711673295 150478938952072750067509943)
  ·
    refine ⟨225718408428109125101264915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150478938952072750067509943 225718408428109125101264915)
    ·
      refine ⟨338577612642163687651897373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225718408428109125101264915 338577612642163687651897373)
      ·
        refine ⟨126966604740811382869461515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338577612642163687651897373 126966604740811382869461515)
        ·
          refine ⟨190449907111217074304192273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126966604740811382869461515 190449907111217074304192273)
          ·
            refine ⟨142837430333412805728144205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190449907111217074304192273 142837430333412805728144205)
            ·
              refine ⟨53564036375029802148054077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142837430333412805728144205 53564036375029802148054077)
              ·
                refine ⟨20086513640636175805520279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53564036375029802148054077 20086513640636175805520279)
                ·
                  refine ⟨30129770460954263708280419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20086513640636175805520279 30129770460954263708280419)
                  ·
                    refine ⟨45194655691431395562420629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30129770460954263708280419 45194655691431395562420629)
                    ·
                      refine ⟨2118499485535846666988467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45194655691431395562420629 2118499485535846666988467)
                      ·
                        rfl

theorem cell23_4125763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_4125763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125763 prefixEnd_4125763 := by exact prefixLift 4125763
  have htrace : WordTrace (prefixWord ++ tailWord_4125763) baseStart_4125763 baseEnd_4125763 := by
    simpa [prefixWord, tailWord_4125763, baseEnd_4125763] using wordTrace_append hprefix tailTrace_4125763
  have hstable : (prefixWord ++ tailWord_4125763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125763).length < 2 ^ (prefixWord ++ tailWord_4125763).sum := by decide
  have hdescent : baseEnd_4125763 < baseStart_4125763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125767 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_4125767 : Nat := 118140960795 + 4125767 * 2 ^ 59
def prefixEnd_4125767 : Nat := 4983230072969 + 3 ^ 40 * 4125767 * 2
def baseEnd_4125767 : Nat := 2118501539458464651338449

theorem tailTrace_4125767 : CollatzResearch.WordTrace tailWord_4125767 prefixEnd_4125767 2118501539458464651338449 := by
  unfold tailWord_4125767
  simp only [CollatzResearch.WordTrace]
  refine ⟨150479084844058258750655555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100319389896038839167103703 150479084844058258750655555)
  ·
    refine ⟨225718627266087388125983333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150479084844058258750655555 225718627266087388125983333)
    ·
      refine ⟨42322242612391385273621875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225718627266087388125983333 42322242612391385273621875)
      ·
        refine ⟨63483363918587077910432813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42322242612391385273621875 63483363918587077910432813)
        ·
          refine ⟨23806261469470154216412305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63483363918587077910432813 23806261469470154216412305)
          ·
            refine ⟨17854696102102615662309229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23806261469470154216412305 17854696102102615662309229)
            ·
              refine ⟨6695511038288480873365961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17854696102102615662309229 6695511038288480873365961)
              ·
                refine ⟨5021633278716360655024471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6695511038288480873365961 5021633278716360655024471)
                ·
                  refine ⟨7532449918074540982536707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021633278716360655024471 7532449918074540982536707)
                  ·
                    refine ⟨11298674877111811473805061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7532449918074540982536707 11298674877111811473805061)
                    ·
                      refine ⟨2118501539458464651338449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11298674877111811473805061 2118501539458464651338449)
                      ·
                        rfl

theorem cell23_4125767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_4125767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125767 prefixEnd_4125767 := by exact prefixLift 4125767
  have htrace : WordTrace (prefixWord ++ tailWord_4125767) baseStart_4125767 baseEnd_4125767 := by
    simpa [prefixWord, tailWord_4125767, baseEnd_4125767] using wordTrace_append hprefix tailTrace_4125767
  have hstable : (prefixWord ++ tailWord_4125767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125767).length < 2 ^ (prefixWord ++ tailWord_4125767).sum := by decide
  have hdescent : baseEnd_4125767 < baseStart_4125767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125780 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_4125780 : Nat := 118140960795 + 4125780 * 2 ^ 59
def prefixEnd_4125780 : Nat := 4983230072969 + 3 ^ 40 * 4125780 * 2
def baseEnd_4125780 : Nat := 2118508214706973100475889

theorem tailTrace_4125780 : CollatzResearch.WordTrace tailWord_4125780 prefixEnd_4125780 2118508214706973100475889 := by
  unfold tailWord_4125780
  simp only [CollatzResearch.WordTrace]
  refine ⟨75239779496505580985439397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100319705995340774647252529 75239779496505580985439397)
  ·
    refine ⟨14107458655594796434769887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75239779496505580985439397 14107458655594796434769887)
    ·
      refine ⟨21161187983392194652154831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14107458655594796434769887 21161187983392194652154831)
      ·
        refine ⟨31741781975088291978232247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21161187983392194652154831 31741781975088291978232247)
        ·
          refine ⟨47612672962632437967348371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31741781975088291978232247 47612672962632437967348371)
          ·
            refine ⟨71419009443948656951022557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47612672962632437967348371 71419009443948656951022557)
            ·
              refine ⟨26782128541480746356633459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71419009443948656951022557 26782128541480746356633459)
              ·
                refine ⟨40173192812221119534950189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26782128541480746356633459 40173192812221119534950189)
                ·
                  refine ⟨15064947304582919825606321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40173192812221119534950189 15064947304582919825606321)
                  ·
                    refine ⟨11298710478437189869204741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15064947304582919825606321 11298710478437189869204741)
                    ·
                      refine ⟨2118508214706973100475889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11298710478437189869204741 2118508214706973100475889)
                      ·
                        rfl

theorem cell23_4125780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_4125780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125780 prefixEnd_4125780 := by exact prefixLift 4125780
  have htrace : WordTrace (prefixWord ++ tailWord_4125780) baseStart_4125780 baseEnd_4125780 := by
    simpa [prefixWord, tailWord_4125780, baseEnd_4125780] using wordTrace_append hprefix tailTrace_4125780
  have hstable : (prefixWord ++ tailWord_4125780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125780).length < 2 ^ (prefixWord ++ tailWord_4125780).sum := by decide
  have hdescent : baseEnd_4125780 < baseStart_4125780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125794 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_4125794 : Nat := 118140960795 + 4125794 * 2 ^ 59
def prefixEnd_4125794 : Nat := 4983230072969 + 3 ^ 40 * 4125794 * 2
def baseEnd_4125794 : Nat := 706171801145378681900275

theorem tailTrace_4125794 : CollatzResearch.WordTrace tailWord_4125794 prefixEnd_4125794 706171801145378681900275 := by
  unfold tailWord_4125794
  simp only [CollatzResearch.WordTrace]
  refine ⟨37620017403740110590472109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100320046409973628241258957 37620017403740110590472109)
  ·
    refine ⟨14107506526402541471427041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37620017403740110590472109 14107506526402541471427041)
    ·
      refine ⟨10580629894801906103570281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14107506526402541471427041 10580629894801906103570281)
      ·
        refine ⟨7935472421101429577677711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10580629894801906103570281 7935472421101429577677711)
        ·
          refine ⟨11903208631652144366516567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7935472421101429577677711 11903208631652144366516567)
          ·
            refine ⟨17854812947478216549774851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11903208631652144366516567 17854812947478216549774851)
            ·
              refine ⟨26782219421217324824662277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17854812947478216549774851 26782219421217324824662277)
              ·
                refine ⟨5021666141478248404624177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26782219421217324824662277 5021666141478248404624177)
                ·
                  refine ⟨3766249606108686303468133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5021666141478248404624177 3766249606108686303468133)
                  ·
                    refine ⟨706171801145378681900275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3766249606108686303468133 706171801145378681900275)
                    ·
                      rfl

theorem cell23_4125794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_4125794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125794 prefixEnd_4125794 := by exact prefixLift 4125794
  have htrace : WordTrace (prefixWord ++ tailWord_4125794) baseStart_4125794 baseEnd_4125794 := by
    simpa [prefixWord, tailWord_4125794, baseEnd_4125794] using wordTrace_append hprefix tailTrace_4125794
  have hstable : (prefixWord ++ tailWord_4125794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125794).length < 2 ^ (prefixWord ++ tailWord_4125794).sum := by decide
  have hdescent : baseEnd_4125794 < baseStart_4125794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125801 : List Nat := [1, 2, 1, 1, 1, 7, 1, 4, 1, 2, 2]
def baseStart_4125801 : Nat := 118140960795 + 4125801 * 2 ^ 59
def prefixEnd_4125801 : Nat := 4983230072969 + 3 ^ 40 * 4125801 * 2
def baseEnd_4125801 : Nat := 2118518997800717518313293

theorem tailTrace_4125801 : CollatzResearch.WordTrace tailWord_4125801 prefixEnd_4125801 2118518997800717518313293 := by
  unfold tailWord_4125801
  simp only [CollatzResearch.WordTrace]
  refine ⟨150480324925935082557393257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100320216617290055038262171 150480324925935082557393257)
  ·
    refine ⟨112860243694451311918044943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150480324925935082557393257 112860243694451311918044943)
    ·
      refine ⟨169290365541676967877067415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112860243694451311918044943 169290365541676967877067415)
      ·
        refine ⟨253935548312515451815601123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169290365541676967877067415 253935548312515451815601123)
        ·
          refine ⟨380903322468773177723401685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253935548312515451815601123 380903322468773177723401685)
          ·
            refine ⟨8927421620361871352892227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 380903322468773177723401685 8927421620361871352892227)
            ·
              refine ⟨13391132430542807029338341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8927421620361871352892227 13391132430542807029338341)
              ·
                refine ⟨2510837330726776318000939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13391132430542807029338341 2510837330726776318000939)
                ·
                  refine ⟨3766255996090164477001409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510837330726776318000939 3766255996090164477001409)
                  ·
                    refine ⟨2824691997067623357751057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3766255996090164477001409 2824691997067623357751057)
                    ·
                      refine ⟨2118518997800717518313293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824691997067623357751057 2118518997800717518313293)
                      ·
                        rfl

theorem cell23_4125801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 1, 2, 2].length) (baseStart_4125801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125801 prefixEnd_4125801 := by exact prefixLift 4125801
  have htrace : WordTrace (prefixWord ++ tailWord_4125801) baseStart_4125801 baseEnd_4125801 := by
    simpa [prefixWord, tailWord_4125801, baseEnd_4125801] using wordTrace_append hprefix tailTrace_4125801
  have hstable : (prefixWord ++ tailWord_4125801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125801).length < 2 ^ (prefixWord ++ tailWord_4125801).sum := by decide
  have hdescent : baseEnd_4125801 < baseStart_4125801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125822 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4125822 : Nat := 118140960795 + 4125822 * 2 ^ 59
def prefixEnd_4125822 : Nat := 4983230072969 + 3 ^ 40 * 4125822 * 2
def baseEnd_4125822 : Nat := 2118529780894461936150697

theorem tailTrace_4125822 : CollatzResearch.WordTrace tailWord_4125822 prefixEnd_4125822 2118529780894461936150697 := by
  unfold tailWord_4125822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18810136357357375392988465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100320727239239335429271813 18810136357357375392988465)
  ·
    refine ⟨14107602268018031544741349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18810136357357375392988465 14107602268018031544741349)
    ·
      refine ⟨2645175425253380914639003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14107602268018031544741349 2645175425253380914639003)
      ·
        refine ⟨3967763137880071371958505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645175425253380914639003 3967763137880071371958505)
        ·
          refine ⟨2975822353410053528968879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3967763137880071371958505 2975822353410053528968879)
          ·
            refine ⟨4463733530115080293453319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2975822353410053528968879 4463733530115080293453319)
            ·
              refine ⟨6695600295172620440179979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4463733530115080293453319 6695600295172620440179979)
              ·
                refine ⟨10043400442758930660269969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6695600295172620440179979 10043400442758930660269969)
                ·
                  refine ⟨7532550332069197995202477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10043400442758930660269969 7532550332069197995202477)
                  ·
                    refine ⟨2824706374525949248200929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7532550332069197995202477 2824706374525949248200929)
                    ·
                      refine ⟨2118529780894461936150697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824706374525949248200929 2118529780894461936150697)
                      ·
                        rfl

theorem cell23_4125822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4125822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125822 prefixEnd_4125822 := by exact prefixLift 4125822
  have htrace : WordTrace (prefixWord ++ tailWord_4125822) baseStart_4125822 baseEnd_4125822 := by
    simpa [prefixWord, tailWord_4125822, baseEnd_4125822] using wordTrace_append hprefix tailTrace_4125822
  have hstable : (prefixWord ++ tailWord_4125822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125822).length < 2 ^ (prefixWord ++ tailWord_4125822).sum := by decide
  have hdescent : baseEnd_4125822 < baseStart_4125822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125827 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 3, 3, 2]
def baseStart_4125827 : Nat := 118140960795 + 4125827 * 2 ^ 59
def prefixEnd_4125827 : Nat := 4983230072969 + 3 ^ 40 * 4125827 * 2
def baseEnd_4125827 : Nat := 2118532348297734416588173

theorem tailTrace_4125827 : CollatzResearch.WordTrace tailWord_4125827 prefixEnd_4125827 2118532348297734416588173 := by
  unfold tailWord_4125827
  simp only [CollatzResearch.WordTrace]
  refine ⟨150481273223840888997839735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100320848815893925998559823 150481273223840888997839735)
  ·
    refine ⟨225721909835761333496759603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150481273223840888997839735 225721909835761333496759603)
    ·
      refine ⟨338582864753642000245139405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225721909835761333496759603 338582864753642000245139405)
      ·
        refine ⟨126968574282615750091927277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338582864753642000245139405 126968574282615750091927277)
        ·
          refine ⟨47613215355980906284472729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126968574282615750091927277 47613215355980906284472729)
          ·
            refine ⟨35709911516985679713354547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47613215355980906284472729 35709911516985679713354547)
            ·
              refine ⟨53564867275478519570031821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35709911516985679713354547 53564867275478519570031821)
              ·
                refine ⟨20086825228304444838761933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53564867275478519570031821 20086825228304444838761933)
                ·
                  refine ⟨7532559460614166814535725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20086825228304444838761933 7532559460614166814535725)
                  ·
                    refine ⟨2824709797730312555450897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7532559460614166814535725 2824709797730312555450897)
                    ·
                      refine ⟨2118532348297734416588173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824709797730312555450897 2118532348297734416588173)
                      ·
                        rfl

theorem cell23_4125827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_4125827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125827 prefixEnd_4125827 := by exact prefixLift 4125827
  have htrace : WordTrace (prefixWord ++ tailWord_4125827) baseStart_4125827 baseEnd_4125827 := by
    simpa [prefixWord, tailWord_4125827, baseEnd_4125827] using wordTrace_append hprefix tailTrace_4125827
  have hstable : (prefixWord ++ tailWord_4125827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125827).length < 2 ^ (prefixWord ++ tailWord_4125827).sum := by decide
  have hdescent : baseEnd_4125827 < baseStart_4125827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125874 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2]
def baseStart_4125874 : Nat := 118140960795 + 4125874 * 2 ^ 59
def prefixEnd_4125874 : Nat := 4983230072969 + 3 ^ 40 * 4125874 * 2
def baseEnd_4125874 : Nat := 2118556481888495732700457

theorem tailTrace_4125874 : CollatzResearch.WordTrace tailWord_4125874 prefixEnd_4125874 2118556481888495732700457 := by
  unfold tailWord_4125874
  simp only [CollatzResearch.WordTrace]
  refine ⟨37620746863667654006200169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100321991636447077349867117 37620746863667654006200169)
  ·
    refine ⟨28215560147750740504650127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37620746863667654006200169 28215560147750740504650127)
    ·
      refine ⟨42323340221626110756975191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28215560147750740504650127 42323340221626110756975191)
      ·
        refine ⟨63485010332439166135462787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42323340221626110756975191 63485010332439166135462787)
        ·
          refine ⟨95227515498658749203194181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63485010332439166135462787 95227515498658749203194181)
          ·
            refine ⟨17855159155998515475598909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95227515498658749203194181 17855159155998515475598909)
            ·
              refine ⟨6695684683499443303349591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17855159155998515475598909 6695684683499443303349591)
              ·
                refine ⟨10043527025249164955024387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6695684683499443303349591 10043527025249164955024387)
                ·
                  refine ⟨15065290537873747432536581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10043527025249164955024387 15065290537873747432536581)
                  ·
                    refine ⟨2824741975851327643600609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15065290537873747432536581 2824741975851327643600609)
                    ·
                      refine ⟨2118556481888495732700457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824741975851327643600609 2118556481888495732700457)
                      ·
                        rfl

theorem cell23_4125874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_4125874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125874 prefixEnd_4125874 := by exact prefixLift 4125874
  have htrace : WordTrace (prefixWord ++ tailWord_4125874) baseStart_4125874 baseEnd_4125874 := by
    simpa [prefixWord, tailWord_4125874, baseEnd_4125874] using wordTrace_append hprefix tailTrace_4125874
  have hstable : (prefixWord ++ tailWord_4125874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125874).length < 2 ^ (prefixWord ++ tailWord_4125874).sum := by decide
  have hdescent : baseEnd_4125874 < baseStart_4125874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125920 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_4125920 : Nat := 118140960795 + 4125920 * 2 ^ 59
def prefixEnd_4125920 : Nat := 4983230072969 + 3 ^ 40 * 4125920 * 2
def baseEnd_4125920 : Nat := 2118580101998602552725245

theorem tailTrace_4125920 : CollatzResearch.WordTrace tailWord_4125920 prefixEnd_4125920 2118580101998602552725245 := by
  unfold tailWord_4125920
  simp only [CollatzResearch.WordTrace]
  refine ⟨75242332606251982940487607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100323110141669310587316809 75242332606251982940487607)
  ·
    refine ⟨112863498909377974410731411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75242332606251982940487607 112863498909377974410731411)
    ·
      refine ⟨169295248364066961616097117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112863498909377974410731411 169295248364066961616097117)
      ·
        refine ⟨63485718136525110606036419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169295248364066961616097117 63485718136525110606036419)
        ·
          refine ⟨95228577204787665909054629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63485718136525110606036419 95228577204787665909054629)
          ·
            refine ⟨17855358225897687357947743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95228577204787665909054629 17855358225897687357947743)
            ·
              refine ⟨26783037338846531036921615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17855358225897687357947743 26783037338846531036921615)
              ·
                refine ⟨40174556008269796555382423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26783037338846531036921615 40174556008269796555382423)
                ·
                  refine ⟨60261834012404694833073635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40174556008269796555382423 60261834012404694833073635)
                  ·
                    refine ⟨90392751018607042249610453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60261834012404694833073635 90392751018607042249610453)
                    ·
                      refine ⟨2118580101998602552725245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90392751018607042249610453 2118580101998602552725245)
                      ·
                        rfl

theorem cell23_4125920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_4125920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125920 prefixEnd_4125920 := by exact prefixLift 4125920
  have htrace : WordTrace (prefixWord ++ tailWord_4125920) baseStart_4125920 baseEnd_4125920 := by
    simpa [prefixWord, tailWord_4125920, baseEnd_4125920] using wordTrace_append hprefix tailTrace_4125920
  have hstable : (prefixWord ++ tailWord_4125920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125920).length < 2 ^ (prefixWord ++ tailWord_4125920).sum := by decide
  have hdescent : baseEnd_4125920 < baseStart_4125920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125925 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 2, 2, 2]
def baseStart_4125925 : Nat := 118140960795 + 4125925 * 2 ^ 59
def prefixEnd_4125925 : Nat := 4983230072969 + 3 ^ 40 * 4125925 * 2
def baseEnd_4125925 : Nat := 2118582669401875033162723

theorem tailTrace_4125925 : CollatzResearch.WordTrace tailWord_4125925 prefixEnd_4125925 2118582669401875033162723 := by
  unfold tailWord_4125925
  simp only [CollatzResearch.WordTrace]
  refine ⟨150484847577485851734907229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100323231718323901156604819 150484847577485851734907229)
  ·
    refine ⟨56431817841557194400590211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150484847577485851734907229 56431817841557194400590211)
    ·
      refine ⟨84647726762335791600885317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56431817841557194400590211 84647726762335791600885317)
      ·
        refine ⟨15871448767937960925165997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84647726762335791600885317 15871448767937960925165997)
        ·
          refine ⟨5951793287976735346937249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15871448767937960925165997 5951793287976735346937249)
          ·
            refine ⟨4463844965982551510202937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5951793287976735346937249 4463844965982551510202937)
            ·
              refine ⟨3347883724486913632652203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4463844965982551510202937 3347883724486913632652203)
              ·
                refine ⟨5021825586730370448978305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347883724486913632652203 5021825586730370448978305)
                ·
                  refine ⟨3766369190047777836733729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5021825586730370448978305 3766369190047777836733729)
                  ·
                    refine ⟨2824776892535833377550297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3766369190047777836733729 2824776892535833377550297)
                    ·
                      refine ⟨2118582669401875033162723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824776892535833377550297 2118582669401875033162723)
                      ·
                        rfl

theorem cell23_4125925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_4125925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125925 prefixEnd_4125925 := by exact prefixLift 4125925
  have htrace : WordTrace (prefixWord ++ tailWord_4125925) baseStart_4125925 baseEnd_4125925 := by
    simpa [prefixWord, tailWord_4125925, baseEnd_4125925] using wordTrace_append hprefix tailTrace_4125925
  have hstable : (prefixWord ++ tailWord_4125925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125925).length < 2 ^ (prefixWord ++ tailWord_4125925).sum := by decide
  have hdescent : baseEnd_4125925 < baseStart_4125925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125981 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_4125981 : Nat := 118140960795 + 4125981 * 2 ^ 59
def prefixEnd_4125981 : Nat := 4983230072969 + 3 ^ 40 * 4125981 * 2
def baseEnd_4125981 : Nat := 2118611424318526814062465

theorem tailTrace_4125981 : CollatzResearch.WordTrace tailWord_4125981 prefixEnd_4125981 2118611424318526814062465 := by
  unfold tailWord_4125981
  simp only [CollatzResearch.WordTrace]
  refine ⟨150486890065282973298945797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100324593376855315532630531 150486890065282973298945797)
  ·
    refine ⟨28216291887240557493552337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150486890065282973298945797 28216291887240557493552337)
    ·
      refine ⟨21162218915430418120164253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28216291887240557493552337 21162218915430418120164253)
      ·
        refine ⟨7935832093286406795061595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21162218915430418120164253 7935832093286406795061595)
        ·
          refine ⟨11903748139929610192592393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7935832093286406795061595 11903748139929610192592393)
          ·
            refine ⟨8927811104947207644444295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11903748139929610192592393 8927811104947207644444295)
            ·
              refine ⟨13391716657420811466666443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8927811104947207644444295 13391716657420811466666443)
              ·
                refine ⟨20087574986131217199999665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13391716657420811466666443 20087574986131217199999665)
                ·
                  refine ⟨15065681239598412899999749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20087574986131217199999665 15065681239598412899999749)
                  ·
                    refine ⟨2824815232424702418749953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15065681239598412899999749 2824815232424702418749953)
                    ·
                      refine ⟨2118611424318526814062465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824815232424702418749953 2118611424318526814062465)
                      ·
                        rfl

theorem cell23_4125981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_4125981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125981 prefixEnd_4125981 := by exact prefixLift 4125981
  have htrace : WordTrace (prefixWord ++ tailWord_4125981) baseStart_4125981 baseEnd_4125981 := by
    simpa [prefixWord, tailWord_4125981, baseEnd_4125981] using wordTrace_append hprefix tailTrace_4125981
  have hstable : (prefixWord ++ tailWord_4125981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125981).length < 2 ^ (prefixWord ++ tailWord_4125981).sum := by decide
  have hdescent : baseEnd_4125981 < baseStart_4125981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125987 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 6]
def baseStart_4125987 : Nat := 118140960795 + 4125987 * 2 ^ 59
def prefixEnd_4125987 : Nat := 4983230072969 + 3 ^ 40 * 4125987 * 2
def baseEnd_4125987 : Nat := 235401611689161532287493

theorem tailTrace_4125987 : CollatzResearch.WordTrace tailWord_4125987 prefixEnd_4125987 235401611689161532287493 := by
  unfold tailWord_4125987
  simp only [CollatzResearch.WordTrace]
  refine ⟨150487108903261236323664215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100324739268840824215776143 150487108903261236323664215)
  ·
    refine ⟨225730663354891854485496323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150487108903261236323664215 225730663354891854485496323)
    ·
      refine ⟨338595995032337781728244485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225730663354891854485496323 338595995032337781728244485)
      ·
        refine ⟨63486749068563334074045841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338595995032337781728244485 63486749068563334074045841)
        ·
          refine ⟨47615061801422500555534381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63486749068563334074045841 47615061801422500555534381)
          ·
            refine ⟨17855648175533437708325393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47615061801422500555534381 17855648175533437708325393)
            ·
              refine ⟨13391736131650078281244045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17855648175533437708325393 13391736131650078281244045)
              ·
                refine ⟨5021901049368779355466517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13391736131650078281244045 5021901049368779355466517)
                ·
                  refine ⟨235401611689161532287493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5021901049368779355466517 235401611689161532287493)
                  ·
                    rfl

theorem cell23_4125987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 6].length) (baseStart_4125987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4125987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4125987 prefixEnd_4125987 := by exact prefixLift 4125987
  have htrace : WordTrace (prefixWord ++ tailWord_4125987) baseStart_4125987 baseEnd_4125987 := by
    simpa [prefixWord, tailWord_4125987, baseEnd_4125987] using wordTrace_append hprefix tailTrace_4125987
  have hstable : (prefixWord ++ tailWord_4125987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125987).length < 2 ^ (prefixWord ++ tailWord_4125987).sum := by decide
  have hdescent : baseEnd_4125987 < baseStart_4125987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126001 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 2, 2, 3]
def baseStart_4126001 : Nat := 118140960795 + 4126001 * 2 ^ 59
def prefixEnd_4126001 : Nat := 4983230072969 + 3 ^ 40 * 4126001 * 2
def baseEnd_4126001 : Nat := 2118621693931616735812373

theorem tailTrace_4126001 : CollatzResearch.WordTrace tailWord_4126001 prefixEnd_4126001 2118621693931616735812373 := by
  unfold tailWord_4126001
  simp only [CollatzResearch.WordTrace]
  refine ⟨150487619525210516714673857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100325079683473677809782571 150487619525210516714673857)
  ·
    refine ⟨112865714643907887536005393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150487619525210516714673857 112865714643907887536005393)
    ·
      refine ⟨84649285982930915652004045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112865714643907887536005393 84649285982930915652004045)
      ·
        refine ⟨31743482243599093369501517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84649285982930915652004045 31743482243599093369501517)
        ·
          refine ⟨11903805841349660013563069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31743482243599093369501517 11903805841349660013563069)
          ·
            refine ⟨4463927190506122505086151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11903805841349660013563069 4463927190506122505086151)
            ·
              refine ⟨6695890785759183757629227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4463927190506122505086151 6695890785759183757629227)
              ·
                refine ⟨10043836178638775636443841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6695890785759183757629227 10043836178638775636443841)
                ·
                  refine ⟨7532877133979081727332881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10043836178638775636443841 7532877133979081727332881)
                  ·
                    refine ⟨5649657850484311295499661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7532877133979081727332881 5649657850484311295499661)
                    ·
                      refine ⟨2118621693931616735812373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5649657850484311295499661 2118621693931616735812373)
                      ·
                        rfl

theorem cell23_4126001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_4126001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126001 prefixEnd_4126001 := by exact prefixLift 4126001
  have htrace : WordTrace (prefixWord ++ tailWord_4126001) baseStart_4126001 baseEnd_4126001 := by
    simpa [prefixWord, tailWord_4126001, baseEnd_4126001] using wordTrace_append hprefix tailTrace_4126001
  have hstable : (prefixWord ++ tailWord_4126001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126001).length < 2 ^ (prefixWord ++ tailWord_4126001).sum := by decide
  have hdescent : baseEnd_4126001 < baseStart_4126001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126024 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 4, 3, 2]
def baseStart_4126024 : Nat := 118140960795 + 4126024 * 2 ^ 59
def prefixEnd_4126024 : Nat := 4983230072969 + 3 ^ 40 * 4126024 * 2
def baseEnd_4126024 : Nat := 2118633503986670145824767

theorem tailTrace_4126024 : CollatzResearch.WordTrace tailWord_4126024 prefixEnd_4126024 2118633503986670145824767 := by
  unfold tailWord_4126024
  simp only [CollatzResearch.WordTrace]
  refine ⟨75244229202063595821380563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100325638936084794428507417 75244229202063595821380563)
  ·
    refine ⟨112866343803095393732070845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75244229202063595821380563 112866343803095393732070845)
    ·
      refine ⟨42324878926160772649526567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112866343803095393732070845 42324878926160772649526567)
      ·
        refine ⟨63487318389241158974289851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42324878926160772649526567 63487318389241158974289851)
        ·
          refine ⟨95230977583861738461434777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63487318389241158974289851 95230977583861738461434777)
          ·
            refine ⟨71423233187896303846076083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95230977583861738461434777 71423233187896303846076083)
            ·
              refine ⟨107134849781844455769114125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71423233187896303846076083 107134849781844455769114125)
              ·
                refine ⟨40175568668191670913417797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107134849781844455769114125 40175568668191670913417797)
                ·
                  refine ⟨7532919125285938296265837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40175568668191670913417797 7532919125285938296265837)
                  ·
                    refine ⟨2824844671982226861099689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7532919125285938296265837 2824844671982226861099689)
                    ·
                      refine ⟨2118633503986670145824767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824844671982226861099689 2118633503986670145824767)
                      ·
                        rfl

theorem cell23_4126024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_4126024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126024 prefixEnd_4126024 := by exact prefixLift 4126024
  have htrace : WordTrace (prefixWord ++ tailWord_4126024) baseStart_4126024 baseEnd_4126024 := by
    simpa [prefixWord, tailWord_4126024, baseEnd_4126024] using wordTrace_append hprefix tailTrace_4126024
  have hstable : (prefixWord ++ tailWord_4126024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126024).length < 2 ^ (prefixWord ++ tailWord_4126024).sum := by decide
  have hdescent : baseEnd_4126024 < baseStart_4126024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126088 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 3, 2, 2]
def baseStart_4126088 : Nat := 118140960795 + 4126088 * 2 ^ 59
def prefixEnd_4126088 : Nat := 4983230072969 + 3 ^ 40 * 4126088 * 2
def baseEnd_4126088 : Nat := 2118666366748557895424473

theorem tailTrace_4126088 : CollatzResearch.WordTrace tailWord_4126088 prefixEnd_4126088 2118666366748557895424473 := by
  unfold tailWord_4126088
  simp only [CollatzResearch.WordTrace]
  refine ⟨75245396337947665286545459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100327195117263553715393945 75245396337947665286545459)
  ·
    refine ⟨112868094506921497929818189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75245396337947665286545459 112868094506921497929818189)
    ·
      refine ⟨42325535440095561723681821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112868094506921497929818189 42325535440095561723681821)
      ·
        refine ⟨15872075790035835646380683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42325535440095561723681821 15872075790035835646380683)
        ·
          refine ⟨23808113685053753469571025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15872075790035835646380683 23808113685053753469571025)
          ·
            refine ⟨17856085263790315102178269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23808113685053753469571025 17856085263790315102178269)
            ·
              refine ⟨6696031973921368163316851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17856085263790315102178269 6696031973921368163316851)
              ·
                refine ⟨10044047960882052244975277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6696031973921368163316851 10044047960882052244975277)
                ·
                  refine ⟨3766517985330769591865729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10044047960882052244975277 3766517985330769591865729)
                  ·
                    refine ⟨2824888488998077193899297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3766517985330769591865729 2824888488998077193899297)
                    ·
                      refine ⟨2118666366748557895424473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824888488998077193899297 2118666366748557895424473)
                      ·
                        rfl

theorem cell23_4126088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_4126088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126088 prefixEnd_4126088 := by exact prefixLift 4126088
  have htrace : WordTrace (prefixWord ++ tailWord_4126088) baseStart_4126088 baseEnd_4126088 := by
    simpa [prefixWord, tailWord_4126088, baseEnd_4126088] using wordTrace_append hprefix tailTrace_4126088
  have hstable : (prefixWord ++ tailWord_4126088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126088).length < 2 ^ (prefixWord ++ tailWord_4126088).sum := by decide
  have hdescent : baseEnd_4126088 < baseStart_4126088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126108 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4126108 : Nat := 118140960795 + 4126108 * 2 ^ 59
def prefixEnd_4126108 : Nat := 4983230072969 + 3 ^ 40 * 4126108 * 2
def baseEnd_4126108 : Nat := 2118676636361647817174381

theorem tailTrace_4126108 : CollatzResearch.WordTrace tailWord_4126108 prefixEnd_4126108 2118676636361647817174381 := by
  unfold tailWord_4126108
  simp only [CollatzResearch.WordTrace]
  refine ⟨75245761067911436994409489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100327681423881915992545985 75245761067911436994409489)
  ·
    refine ⟨56434320800933577745807117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75245761067911436994409489 56434320800933577745807117)
    ·
      refine ⟨21162870300350091654677669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56434320800933577745807117 21162870300350091654677669)
      ·
        refine ⟨3968038181315642185252063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21162870300350091654677669 3968038181315642185252063)
        ·
          refine ⟨5952057271973463277878095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968038181315642185252063 5952057271973463277878095)
          ·
            refine ⟨8928085907960194916817143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952057271973463277878095 8928085907960194916817143)
            ·
              refine ⟨13392128861940292375225715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8928085907960194916817143 13392128861940292375225715)
              ·
                refine ⟨20088193292910438562838573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13392128861940292375225715 20088193292910438562838573)
                ·
                  refine ⟨7533072484841414461064465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20088193292910438562838573 7533072484841414461064465)
                  ·
                    refine ⟨5649804363631060845798349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7533072484841414461064465 5649804363631060845798349)
                    ·
                      refine ⟨2118676636361647817174381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5649804363631060845798349 2118676636361647817174381)
                      ·
                        rfl

theorem cell23_4126108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4126108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126108 prefixEnd_4126108 := by exact prefixLift 4126108
  have htrace : WordTrace (prefixWord ++ tailWord_4126108) baseStart_4126108 baseEnd_4126108 := by
    simpa [prefixWord, tailWord_4126108, baseEnd_4126108] using wordTrace_append hprefix tailTrace_4126108
  have hstable : (prefixWord ++ tailWord_4126108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126108).length < 2 ^ (prefixWord ++ tailWord_4126108).sum := by decide
  have hdescent : baseEnd_4126108 < baseStart_4126108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126117 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_4126117 : Nat := 118140960795 + 4126117 * 2 ^ 59
def prefixEnd_4126117 : Nat := 4983230072969 + 3 ^ 40 * 4126117 * 2
def baseEnd_4126117 : Nat := 2118681257687538281961839

theorem tailTrace_4126117 : CollatzResearch.WordTrace tailWord_4126117 prefixEnd_4126117 2118681257687538281961839 := by
  unfold tailWord_4126117
  simp only [CollatzResearch.WordTrace]
  refine ⟨150491850392790268525896605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100327900261860179017264403 150491850392790268525896605)
  ·
    refine ⟨56434443897296350697211227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150491850392790268525896605 56434443897296350697211227)
    ·
      refine ⟨84651665845944526045816841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56434443897296350697211227 84651665845944526045816841)
      ·
        refine ⟨63488749384458394534362631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84651665845944526045816841 63488749384458394534362631)
        ·
          refine ⟨95233124076687591801543947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63488749384458394534362631 95233124076687591801543947)
          ·
            refine ⟨142849686115031387702315921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95233124076687591801543947 142849686115031387702315921)
            ·
              refine ⟨107137264586273540776736941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142849686115031387702315921 107137264586273540776736941)
              ·
                refine ⟨40176474219852577791276353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107137264586273540776736941 40176474219852577791276353)
                ·
                  refine ⟨30132355664889433343457265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40176474219852577791276353 30132355664889433343457265)
                  ·
                    refine ⟨22599266748667075007592949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30132355664889433343457265 22599266748667075007592949)
                    ·
                      refine ⟨2118681257687538281961839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22599266748667075007592949 2118681257687538281961839)
                      ·
                        rfl

theorem cell23_4126117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_4126117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126117 prefixEnd_4126117 := by exact prefixLift 4126117
  have htrace : WordTrace (prefixWord ++ tailWord_4126117) baseStart_4126117 baseEnd_4126117 := by
    simpa [prefixWord, tailWord_4126117, baseEnd_4126117] using wordTrace_append hprefix tailTrace_4126117
  have hstable : (prefixWord ++ tailWord_4126117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126117).length < 2 ^ (prefixWord ++ tailWord_4126117).sum := by decide
  have hdescent : baseEnd_4126117 < baseStart_4126117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126125 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_4126125 : Nat := 118140960795 + 4126125 * 2 ^ 59
def prefixEnd_4126125 : Nat := 4983230072969 + 3 ^ 40 * 4126125 * 2
def baseEnd_4126125 : Nat := 2118685365532774250661803

theorem tailTrace_4126125 : CollatzResearch.WordTrace tailWord_4126125 prefixEnd_4126125 2118685365532774250661803 := by
  unfold tailWord_4126125
  simp only [CollatzResearch.WordTrace]
  refine ⟨150492142176761285892187829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100328094784507523928125219 150492142176761285892187829)
  ·
    refine ⟨14108638329071370552392609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150492142176761285892187829 14108638329071370552392609)
    ·
      refine ⟨10581478746803527914294457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14108638329071370552392609 10581478746803527914294457)
      ·
        refine ⟨7936109060102645935720843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10581478746803527914294457 7936109060102645935720843)
        ·
          refine ⟨11904163590153968903581265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7936109060102645935720843 11904163590153968903581265)
          ·
            refine ⟨8928122692615476677685949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11904163590153968903581265 8928122692615476677685949)
            ·
              refine ⟨3348046009730803754132231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8928122692615476677685949 3348046009730803754132231)
              ·
                refine ⟨5022069014596205631198347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348046009730803754132231 5022069014596205631198347)
                ·
                  refine ⟨7533103521894308446797521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022069014596205631198347 7533103521894308446797521)
                  ·
                    refine ⟨5649827641420731335098141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7533103521894308446797521 5649827641420731335098141)
                    ·
                      refine ⟨2118685365532774250661803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5649827641420731335098141 2118685365532774250661803)
                      ·
                        rfl

theorem cell23_4126125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_4126125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126125 prefixEnd_4126125 := by exact prefixLift 4126125
  have htrace : WordTrace (prefixWord ++ tailWord_4126125) baseStart_4126125 baseEnd_4126125 := by
    simpa [prefixWord, tailWord_4126125, baseEnd_4126125] using wordTrace_append hprefix tailTrace_4126125
  have hstable : (prefixWord ++ tailWord_4126125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126125).length < 2 ^ (prefixWord ++ tailWord_4126125).sum := by decide
  have hdescent : baseEnd_4126125 < baseStart_4126125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126127 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_4126127 : Nat := 118140960795 + 4126127 * 2 ^ 59
def prefixEnd_4126127 : Nat := 4983230072969 + 3 ^ 40 * 4126127 * 2
def baseEnd_4126127 : Nat := 2118686392494083242836793

theorem tailTrace_4126127 : CollatzResearch.WordTrace tailWord_4126127 prefixEnd_4126127 2118686392494083242836793 := by
  unfold tailWord_4126127
  simp only [CollatzResearch.WordTrace]
  refine ⟨150492215122754040233760635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100328143415169360155840423 150492215122754040233760635)
  ·
    refine ⟨225738322684131060350640953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150492215122754040233760635 225738322684131060350640953)
    ·
      refine ⟨169303742013098295262980715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225738322684131060350640953 169303742013098295262980715)
      ·
        refine ⟨253955613019647442894471073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169303742013098295262980715 253955613019647442894471073)
        ·
          refine ⟨190466709764735582170853305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253955613019647442894471073 190466709764735582170853305)
          ·
            refine ⟨142850032323551686628139979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190466709764735582170853305 142850032323551686628139979)
            ·
              refine ⟨214275048485327529942209969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142850032323551686628139979 214275048485327529942209969)
              ·
                refine ⟨160706286363995647456657477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214275048485327529942209969 160706286363995647456657477)
                ·
                  refine ⟨30132428693249183898123277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160706286363995647456657477 30132428693249183898123277)
                  ·
                    refine ⟨11299660759968443961796229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30132428693249183898123277 11299660759968443961796229)
                    ·
                      refine ⟨2118686392494083242836793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11299660759968443961796229 2118686392494083242836793)
                      ·
                        rfl

theorem cell23_4126127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_4126127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126127 prefixEnd_4126127 := by exact prefixLift 4126127
  have htrace : WordTrace (prefixWord ++ tailWord_4126127) baseStart_4126127 baseEnd_4126127 := by
    simpa [prefixWord, tailWord_4126127, baseEnd_4126127] using wordTrace_append hprefix tailTrace_4126127
  have hstable : (prefixWord ++ tailWord_4126127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126127).length < 2 ^ (prefixWord ++ tailWord_4126127).sum := by decide
  have hdescent : baseEnd_4126127 < baseStart_4126127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126131 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 1, 3, 2]
def baseStart_4126131 : Nat := 118140960795 + 4126131 * 2 ^ 59
def prefixEnd_4126131 : Nat := 4983230072969 + 3 ^ 40 * 4126131 * 2
def baseEnd_4126131 : Nat := 2118688446416701227186775

theorem tailTrace_4126131 : CollatzResearch.WordTrace tailWord_4126131 prefixEnd_4126131 2118688446416701227186775 := by
  unfold tailWord_4126131
  simp only [CollatzResearch.WordTrace]
  refine ⟨150492361014739548916906247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100328240676493032611270831 150492361014739548916906247)
  ·
    refine ⟨225738541522109323375359371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150492361014739548916906247 225738541522109323375359371)
    ·
      refine ⟨338607812283163985063039057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225738541522109323375359371 338607812283163985063039057)
      ·
        refine ⟨253955859212372988797279293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338607812283163985063039057 253955859212372988797279293)
        ·
          refine ⟨95233447204639870798979735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253955859212372988797279293 95233447204639870798979735)
          ·
            refine ⟨142850170806959806198469603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95233447204639870798979735 142850170806959806198469603)
            ·
              refine ⟨214275256210439709297704405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142850170806959806198469603 214275256210439709297704405)
              ·
                refine ⟨5022076317432180686664947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 214275256210439709297704405 5022076317432180686664947)
                ·
                  refine ⟨7533114476148271029997421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022076317432180686664947 7533114476148271029997421)
                  ·
                    refine ⟨2824917928555601636249033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7533114476148271029997421 2824917928555601636249033)
                    ·
                      refine ⟨2118688446416701227186775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824917928555601636249033 2118688446416701227186775)
                      ·
                        rfl

theorem cell23_4126131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 3, 2].length) (baseStart_4126131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126131 prefixEnd_4126131 := by exact prefixLift 4126131
  have htrace : WordTrace (prefixWord ++ tailWord_4126131) baseStart_4126131 baseEnd_4126131 := by
    simpa [prefixWord, tailWord_4126131, baseEnd_4126131] using wordTrace_append hprefix tailTrace_4126131
  have hstable : (prefixWord ++ tailWord_4126131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126131).length < 2 ^ (prefixWord ++ tailWord_4126131).sum := by decide
  have hdescent : baseEnd_4126131 < baseStart_4126131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126147 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 5]
def baseStart_4126147 : Nat := 118140960795 + 4126147 * 2 ^ 59
def prefixEnd_4126147 : Nat := 4983230072969 + 3 ^ 40 * 4126147 * 2
def baseEnd_4126147 : Nat := 2118696662107173164586701

theorem tailTrace_4126147 : CollatzResearch.WordTrace tailWord_4126147 prefixEnd_4126147 2118696662107173164586701 := by
  unfold tailWord_4126147
  simp only [CollatzResearch.WordTrace]
  refine ⟨150492944582681583649488695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100328629721787722432992463 150492944582681583649488695)
  ·
    refine ⟨225739416874022375474233043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150492944582681583649488695 225739416874022375474233043)
    ·
      refine ⟨338609125311033563211349565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225739416874022375474233043 338609125311033563211349565)
      ·
        refine ⟨126978421991637586204256087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338609125311033563211349565 126978421991637586204256087)
        ·
          refine ⟨190467632987456379306384131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126978421991637586204256087 190467632987456379306384131)
          ·
            refine ⟨285701449481184568959576197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190467632987456379306384131 285701449481184568959576197)
            ·
              refine ⟨53569021777722106679920537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285701449481184568959576197 53569021777722106679920537)
              ·
                refine ⟨40176766333291580009940403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53569021777722106679920537 40176766333291580009940403)
                ·
                  refine ⟨60265149499937370014910605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40176766333291580009940403 60265149499937370014910605)
                  ·
                    refine ⟨22599431062476513755591477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60265149499937370014910605 22599431062476513755591477)
                    ·
                      refine ⟨2118696662107173164586701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22599431062476513755591477 2118696662107173164586701)
                      ·
                        rfl

theorem cell23_4126147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_4126147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126147 prefixEnd_4126147 := by exact prefixLift 4126147
  have htrace : WordTrace (prefixWord ++ tailWord_4126147) baseStart_4126147 baseEnd_4126147 := by
    simpa [prefixWord, tailWord_4126147, baseEnd_4126147] using wordTrace_append hprefix tailTrace_4126147
  have hstable : (prefixWord ++ tailWord_4126147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126147).length < 2 ^ (prefixWord ++ tailWord_4126147).sum := by decide
  have hdescent : baseEnd_4126147 < baseStart_4126147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126148 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_4126148 : Nat := 118140960795 + 4126148 * 2 ^ 59
def prefixEnd_4126148 : Nat := 4983230072969 + 3 ^ 40 * 4126148 * 2
def baseEnd_4126148 : Nat := 2118697175587827660674197

theorem tailTrace_4126148 : CollatzResearch.WordTrace tailWord_4126148 prefixEnd_4126148 2118697175587827660674197 := by
  unfold tailWord_4126148
  simp only [CollatzResearch.WordTrace]
  refine ⟨75246490527838980410137549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100328654037118640546850065 75246490527838980410137549)
  ·
    refine ⟨28217433947939617653801581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75246490527838980410137549 28217433947939617653801581)
    ·
      refine ⟨10581537730477356620175593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28217433947939617653801581 10581537730477356620175593)
      ·
        refine ⟨7936153297858017465131695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10581537730477356620175593 7936153297858017465131695)
        ·
          refine ⟨11904229946787026197697543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7936153297858017465131695 11904229946787026197697543)
          ·
            refine ⟨17856344920180539296546315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11904229946787026197697543 17856344920180539296546315)
            ·
              refine ⟨26784517380270808944819473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17856344920180539296546315 26784517380270808944819473)
              ·
                refine ⟨20088388035203106708614605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26784517380270808944819473 20088388035203106708614605)
                ·
                  refine ⟨7533145513201165015730477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20088388035203106708614605 7533145513201165015730477)
                  ·
                    refine ⟨2824929567450436880898929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7533145513201165015730477 2824929567450436880898929)
                    ·
                      refine ⟨2118697175587827660674197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824929567450436880898929 2118697175587827660674197)
                      ·
                        rfl

theorem cell23_4126148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_4126148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126148 prefixEnd_4126148 := by exact prefixLift 4126148
  have htrace : WordTrace (prefixWord ++ tailWord_4126148) baseStart_4126148 baseEnd_4126148 := by
    simpa [prefixWord, tailWord_4126148, baseEnd_4126148] using wordTrace_append hprefix tailTrace_4126148
  have hstable : (prefixWord ++ tailWord_4126148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126148).length < 2 ^ (prefixWord ++ tailWord_4126148).sum := by decide
  have hdescent : baseEnd_4126148 < baseStart_4126148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126154 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_4126154 : Nat := 118140960795 + 4126154 * 2 ^ 59
def prefixEnd_4126154 : Nat := 4983230072969 + 3 ^ 40 * 4126154 * 2
def baseEnd_4126154 : Nat := 706233418823918212399723

theorem tailTrace_4126154 : CollatzResearch.WordTrace tailWord_4126154 prefixEnd_4126154 706233418823918212399723 := by
  unfold tailWord_4126154
  simp only [CollatzResearch.WordTrace]
  refine ⟨37623299973414055961248379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100328799929104149229995677 37623299973414055961248379)
  ·
    refine ⟨56434949960121083941872569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37623299973414055961248379 56434949960121083941872569)
    ·
      refine ⟨42326212470090812956404427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56434949960121083941872569 42326212470090812956404427)
      ·
        refine ⟨63489318705136219434606641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42326212470090812956404427 63489318705136219434606641)
        ·
          refine ⟨47616989028852164575954981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63489318705136219434606641 47616989028852164575954981)
          ·
            refine ⟨8928185442909780857991559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47616989028852164575954981 8928185442909780857991559)
            ·
              refine ⟨13392278164364671286987339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8928185442909780857991559 13392278164364671286987339)
              ·
                refine ⟨20088417246547006930481009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13392278164364671286987339 20088417246547006930481009)
                ·
                  refine ⟨15066312934910255197860757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20088417246547006930481009 15066312934910255197860757)
                  ·
                    refine ⟨706233418823918212399723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15066312934910255197860757 706233418823918212399723)
                    ·
                      rfl

theorem cell23_4126154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_4126154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126154 prefixEnd_4126154 := by exact prefixLift 4126154
  have htrace : WordTrace (prefixWord ++ tailWord_4126154) baseStart_4126154 baseEnd_4126154 := by
    simpa [prefixWord, tailWord_4126154, baseEnd_4126154] using wordTrace_append hprefix tailTrace_4126154
  have hstable : (prefixWord ++ tailWord_4126154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126154).length < 2 ^ (prefixWord ++ tailWord_4126154).sum := by decide
  have hdescent : baseEnd_4126154 < baseStart_4126154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126161 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 8, 2, 2]
def baseStart_4126161 : Nat := 118140960795 + 4126161 * 2 ^ 59
def prefixEnd_4126161 : Nat := 4983230072969 + 3 ^ 40 * 4126161 * 2
def baseEnd_4126161 : Nat := 2118703850836336109811637

theorem tailTrace_4126161 : CollatzResearch.WordTrace tailWord_4126161 prefixEnd_4126161 2118703850836336109811637 := by
  unfold tailWord_4126161
  simp only [CollatzResearch.WordTrace]
  refine ⟨150493455204630864040498337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100328970136420576026998891 150493455204630864040498337)
  ·
    refine ⟨112870091403473148030373753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150493455204630864040498337 112870091403473148030373753)
    ·
      refine ⟨84652568552604861022780315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112870091403473148030373753 84652568552604861022780315)
      ·
        refine ⟨126978852828907291534170473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84652568552604861022780315 126978852828907291534170473)
        ·
          refine ⟨95234139621680468650627855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126978852828907291534170473 95234139621680468650627855)
          ·
            refine ⟨142851209432520702975941783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95234139621680468650627855 142851209432520702975941783)
            ·
              refine ⟨214276814148781054463912675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142851209432520702975941783 214276814148781054463912675)
              ·
                refine ⟨321415221223171581695869013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214276814148781054463912675 321415221223171581695869013)
                ·
                  refine ⟨3766584623709041972998465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 321415221223171581695869013 3766584623709041972998465)
                  ·
                    refine ⟨2824938467781781479748849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3766584623709041972998465 2824938467781781479748849)
                    ·
                      refine ⟨2118703850836336109811637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824938467781781479748849 2118703850836336109811637)
                      ·
                        rfl

theorem cell23_4126161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_4126161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126161 prefixEnd_4126161 := by exact prefixLift 4126161
  have htrace : WordTrace (prefixWord ++ tailWord_4126161) baseStart_4126161 baseEnd_4126161 := by
    simpa [prefixWord, tailWord_4126161, baseEnd_4126161] using wordTrace_append hprefix tailTrace_4126161
  have hstable : (prefixWord ++ tailWord_4126161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126161).length < 2 ^ (prefixWord ++ tailWord_4126161).sum := by decide
  have hdescent : baseEnd_4126161 < baseStart_4126161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126212 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_4126212 : Nat := 118140960795 + 4126212 * 2 ^ 59
def prefixEnd_4126212 : Nat := 4983230072969 + 3 ^ 40 * 4126212 * 2
def baseEnd_4126212 : Nat := 2118730038349715410273903

theorem tailTrace_4126212 : CollatzResearch.WordTrace tailWord_4126212 prefixEnd_4126212 2118730038349715410273903 := by
  unfold tailWord_4126212
  simp only [CollatzResearch.WordTrace]
  refine ⟨75247657663723049875302445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100330210218297399833736593 75247657663723049875302445)
  ·
    refine ⟨28217871623896143703238417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75247657663723049875302445 28217871623896143703238417)
    ·
      refine ⟨21163403717922107777428813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28217871623896143703238417 21163403717922107777428813)
      ·
        refine ⟨7936276394220790416535805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21163403717922107777428813 7936276394220790416535805)
        ·
          refine ⟨2976103647832796406200927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7936276394220790416535805 2976103647832796406200927)
          ·
            refine ⟨4464155471749194609301391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976103647832796406200927 4464155471749194609301391)
            ·
              refine ⟨6696233207623791913952087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464155471749194609301391 6696233207623791913952087)
              ·
                refine ⟨10044349811435687870928131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6696233207623791913952087 10044349811435687870928131)
                ·
                  refine ⟨15066524717153531806392197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10044349811435687870928131 15066524717153531806392197)
                  ·
                    refine ⟨2824973384466287213698537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15066524717153531806392197 2824973384466287213698537)
                    ·
                      refine ⟨2118730038349715410273903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2824973384466287213698537 2118730038349715410273903)
                      ·
                        rfl

theorem cell23_4126212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_4126212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126212 prefixEnd_4126212 := by exact prefixLift 4126212
  have htrace : WordTrace (prefixWord ++ tailWord_4126212) baseStart_4126212 baseEnd_4126212 := by
    simpa [prefixWord, tailWord_4126212, baseEnd_4126212] using wordTrace_append hprefix tailTrace_4126212
  have hstable : (prefixWord ++ tailWord_4126212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126212).length < 2 ^ (prefixWord ++ tailWord_4126212).sum := by decide
  have hdescent : baseEnd_4126212 < baseStart_4126212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126248 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 2, 5]
def baseStart_4126248 : Nat := 118140960795 + 4126248 * 2 ^ 59
def prefixEnd_4126248 : Nat := 4983230072969 + 3 ^ 40 * 4126248 * 2
def baseEnd_4126248 : Nat := 706249507884425756474579

theorem tailTrace_4126248 : CollatzResearch.WordTrace tailWord_4126248 prefixEnd_4126248 706249507884425756474579 := by
  unfold tailWord_4126248
  simp only [CollatzResearch.WordTrace]
  refine ⟨75248314177657838949457699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100331085570210451932610265 75248314177657838949457699)
  ·
    refine ⟨112872471266486758424186549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75248314177657838949457699 112872471266486758424186549)
    ·
      refine ⟨10581794181233133602267489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112872471266486758424186549 10581794181233133602267489)
      ·
        refine ⟨7936345635924850201700617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10581794181233133602267489 7936345635924850201700617)
        ·
          refine ⟨5952259226943637651275463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7936345635924850201700617 5952259226943637651275463)
          ·
            refine ⟨8928388840415456476913195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952259226943637651275463 8928388840415456476913195)
            ·
              refine ⟨13392583260623184715369793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8928388840415456476913195 13392583260623184715369793)
              ·
                refine ⟨10044437445467388536527345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13392583260623184715369793 10044437445467388536527345)
                ·
                  refine ⟨7533328084100541402395509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10044437445467388536527345 7533328084100541402395509)
                  ·
                    refine ⟨706249507884425756474579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7533328084100541402395509 706249507884425756474579)
                    ·
                      rfl

theorem cell23_4126248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_4126248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126248 prefixEnd_4126248 := by exact prefixLift 4126248
  have htrace : WordTrace (prefixWord ++ tailWord_4126248) baseStart_4126248 baseEnd_4126248 := by
    simpa [prefixWord, tailWord_4126248, baseEnd_4126248] using wordTrace_append hprefix tailTrace_4126248
  have hstable : (prefixWord ++ tailWord_4126248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126248).length < 2 ^ (prefixWord ++ tailWord_4126248).sum := by decide
  have hdescent : baseEnd_4126248 < baseStart_4126248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126285 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_4126285 : Nat := 118140960795 + 4126285 * 2 ^ 59
def prefixEnd_4126285 : Nat := 4983230072969 + 3 ^ 40 * 4126285 * 2
def baseEnd_4126285 : Nat := 2118767522437493624661067

theorem tailTrace_4126285 : CollatzResearch.WordTrace tailWord_4126285 prefixEnd_4126285 2118767522437493624661067 := by
  unfold tailWord_4126285
  simp only [CollatzResearch.WordTrace]
  refine ⟨150497977856181633218012309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100331985237454422145341539 150497977856181633218012309)
  ·
    refine ⟨7054592712008514057094327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150497977856181633218012309 7054592712008514057094327)
    ·
      refine ⟨10581889068012771085641491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7054592712008514057094327 10581889068012771085641491)
      ·
        refine ⟨15872833602019156628462237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10581889068012771085641491 15872833602019156628462237)
        ·
          refine ⟨5952312600757183735673339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15872833602019156628462237 5952312600757183735673339)
          ·
            refine ⟨8928468901135775603510009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952312600757183735673339 8928468901135775603510009)
            ·
              refine ⟨6696351675851831702632507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8928468901135775603510009 6696351675851831702632507)
              ·
                refine ⟨10044527513777747553948761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6696351675851831702632507 10044527513777747553948761)
                ·
                  refine ⟨7533395635333310665461571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10044527513777747553948761 7533395635333310665461571)
                  ·
                    refine ⟨11300093452999965998192357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7533395635333310665461571 11300093452999965998192357)
                    ·
                      refine ⟨2118767522437493624661067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11300093452999965998192357 2118767522437493624661067)
                      ·
                        rfl

theorem cell23_4126285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_4126285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126285 prefixEnd_4126285 := by exact prefixLift 4126285
  have htrace : WordTrace (prefixWord ++ tailWord_4126285) baseStart_4126285 baseEnd_4126285 := by
    simpa [prefixWord, tailWord_4126285, baseEnd_4126285] using wordTrace_append hprefix tailTrace_4126285
  have hstable : (prefixWord ++ tailWord_4126285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126285).length < 2 ^ (prefixWord ++ tailWord_4126285).sum := by decide
  have hdescent : baseEnd_4126285 < baseStart_4126285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126312 : List Nat := [2, 1, 4, 3, 1, 1, 4, 2, 1, 4]
def baseStart_4126312 : Nat := 118140960795 + 4126312 * 2 ^ 59
def prefixEnd_4126312 : Nat := 4983230072969 + 3 ^ 40 * 4126312 * 2
def baseEnd_4126312 : Nat := 706260462138388339674481

theorem tailTrace_4126312 : CollatzResearch.WordTrace tailWord_4126312 prefixEnd_4126312 706260462138388339674481 := by
  unfold tailWord_4126312
  simp only [CollatzResearch.WordTrace]
  refine ⟨75249481313541908414622595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100332641751389211219496793 75249481313541908414622595)
  ·
    refine ⟨112874221970312862621933893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75249481313541908414622595 112874221970312862621933893)
    ·
      refine ⟨21163916619433661741612605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112874221970312862621933893 21163916619433661741612605)
      ·
        refine ⟨7936468732287623153104727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21163916619433661741612605 7936468732287623153104727)
        ·
          refine ⟨11904703098431434729657091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7936468732287623153104727 11904703098431434729657091)
          ·
            refine ⟨17857054647647152094485637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11904703098431434729657091 17857054647647152094485637)
            ·
              refine ⟨3348197746433841017716057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17857054647647152094485637 3348197746433841017716057)
              ·
                refine ⟨2511148309825380763287043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348197746433841017716057 2511148309825380763287043)
                ·
                  refine ⟨3766722464738071144930565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511148309825380763287043 3766722464738071144930565)
                  ·
                    refine ⟨706260462138388339674481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3766722464738071144930565 706260462138388339674481)
                    ·
                      rfl

theorem cell23_4126312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_4126312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126312 prefixEnd_4126312 := by exact prefixLift 4126312
  have htrace : WordTrace (prefixWord ++ tailWord_4126312) baseStart_4126312 baseEnd_4126312 := by
    simpa [prefixWord, tailWord_4126312, baseEnd_4126312] using wordTrace_append hprefix tailTrace_4126312
  have hstable : (prefixWord ++ tailWord_4126312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126312).length < 2 ^ (prefixWord ++ tailWord_4126312).sum := by decide
  have hdescent : baseEnd_4126312 < baseStart_4126312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126341 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_4126341 : Nat := 118140960795 + 4126341 * 2 ^ 59
def prefixEnd_4126341 : Nat := 4983230072969 + 3 ^ 40 * 4126341 * 2
def baseEnd_4126341 : Nat := 2118796277354145405560809

theorem tailTrace_4126341 : CollatzResearch.WordTrace tailWord_4126341 prefixEnd_4126341 2118796277354145405560809 := by
  unfold tailWord_4126341
  simp only [CollatzResearch.WordTrace]
  refine ⟨150500020343978754782050877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100333346895985836521367251 150500020343978754782050877)
  ·
    refine ⟨56437507628992033043269079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150500020343978754782050877 56437507628992033043269079)
    ·
      refine ⟨84656261443488049564903619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56437507628992033043269079 84656261443488049564903619)
      ·
        refine ⟨126984392165232074347355429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84656261443488049564903619 126984392165232074347355429)
        ·
          refine ⟨23809573530981013940129143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126984392165232074347355429 23809573530981013940129143)
          ·
            refine ⟨35714360296471520910193715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23809573530981013940129143 35714360296471520910193715)
            ·
              refine ⟨53571540444707281365290573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35714360296471520910193715 53571540444707281365290573)
              ·
                refine ⟨20089327666765230511983965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53571540444707281365290573 20089327666765230511983965)
                ·
                  refine ⟨7533497875036961441993987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20089327666765230511983965 7533497875036961441993987)
                  ·
                    refine ⟨11300246812555442162990981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7533497875036961441993987 11300246812555442162990981)
                    ·
                      refine ⟨2118796277354145405560809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11300246812555442162990981 2118796277354145405560809)
                      ·
                        rfl

theorem cell23_4126341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_4126341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126341 prefixEnd_4126341 := by exact prefixLift 4126341
  have htrace : WordTrace (prefixWord ++ tailWord_4126341) baseStart_4126341 baseEnd_4126341 := by
    simpa [prefixWord, tailWord_4126341, baseEnd_4126341] using wordTrace_append hprefix tailTrace_4126341
  have hstable : (prefixWord ++ tailWord_4126341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126341).length < 2 ^ (prefixWord ++ tailWord_4126341).sum := by decide
  have hdescent : baseEnd_4126341 < baseStart_4126341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126361 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 5, 2, 3]
def baseStart_4126361 : Nat := 118140960795 + 4126361 * 2 ^ 59
def prefixEnd_4126361 : Nat := 4983230072969 + 3 ^ 40 * 4126361 * 2
def baseEnd_4126361 : Nat := 2118806546967235327310717

theorem tailTrace_4126361 : CollatzResearch.WordTrace tailWord_4126361 prefixEnd_4126361 2118806546967235327310717 := by
  unfold tailWord_4126361
  simp only [CollatzResearch.WordTrace]
  refine ⟨150500749803906298197778937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100333833202604198798519291 150500749803906298197778937)
  ·
    refine ⟨112875562352929723648334203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150500749803906298197778937 112875562352929723648334203)
    ·
      refine ⟨169313343529394585472501305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112875562352929723648334203 169313343529394585472501305)
      ·
        refine ⟨126985007647045939104375979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169313343529394585472501305 126985007647045939104375979)
        ·
          refine ⟨190477511470568908656563969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126985007647045939104375979 190477511470568908656563969)
          ·
            refine ⟨142858133602926681492422977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190477511470568908656563969 142858133602926681492422977)
            ·
              refine ⟨107143600202195011119317233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142858133602926681492422977 107143600202195011119317233)
              ·
                refine ⟨80357700151646258339487925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107143600202195011119317233 80357700151646258339487925)
                ·
                  refine ⟨7533534389216836719326993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80357700151646258339487925 7533534389216836719326993)
                  ·
                    refine ⟨5650150791912627539495245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7533534389216836719326993 5650150791912627539495245)
                    ·
                      refine ⟨2118806546967235327310717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5650150791912627539495245 2118806546967235327310717)
                      ·
                        rfl

theorem cell23_4126361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_4126361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126361 prefixEnd_4126361 := by exact prefixLift 4126361
  have htrace : WordTrace (prefixWord ++ tailWord_4126361) baseStart_4126361 baseEnd_4126361 := by
    simpa [prefixWord, tailWord_4126361, baseEnd_4126361] using wordTrace_append hprefix tailTrace_4126361
  have hstable : (prefixWord ++ tailWord_4126361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126361).length < 2 ^ (prefixWord ++ tailWord_4126361).sum := by decide
  have hdescent : baseEnd_4126361 < baseStart_4126361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126368 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 4, 4]
def baseStart_4126368 : Nat := 118140960795 + 4126368 * 2 ^ 59
def prefixEnd_4126368 : Nat := 4983230072969 + 3 ^ 40 * 4126368 * 2
def baseEnd_4126368 : Nat := 706270047110605599974395

theorem tailTrace_4126368 : CollatzResearch.WordTrace tailWord_4126368 prefixEnd_4126368 706270047110605599974395 := by
  unfold tailWord_4126368
  simp only [CollatzResearch.WordTrace]
  refine ⟨75250502557440469196641879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100334003409920625595522505 75250502557440469196641879)
  ·
    refine ⟨112875753836160703794962819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75250502557440469196641879 112875753836160703794962819)
    ·
      refine ⟨169313630754241055692444229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112875753836160703794962819 169313630754241055692444229)
      ·
        refine ⟨31746305766420197942333293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169313630754241055692444229 31746305766420197942333293)
        ·
          refine ⟨11904864662407574228374985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31746305766420197942333293 11904864662407574228374985)
          ·
            refine ⟨8928648496805680671281239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11904864662407574228374985 8928648496805680671281239)
            ·
              refine ⟨13392972745208521006921859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8928648496805680671281239 13392972745208521006921859)
              ·
                refine ⟨20089459117812781510382789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13392972745208521006921859 20089459117812781510382789)
                ·
                  refine ⟨3766773584589896533196773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20089459117812781510382789 3766773584589896533196773)
                  ·
                    refine ⟨706270047110605599974395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3766773584589896533196773 706270047110605599974395)
                    ·
                      rfl

theorem cell23_4126368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4, 4].length) (baseStart_4126368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126368 prefixEnd_4126368 := by exact prefixLift 4126368
  have htrace : WordTrace (prefixWord ++ tailWord_4126368) baseStart_4126368 baseEnd_4126368 := by
    simpa [prefixWord, tailWord_4126368, baseEnd_4126368] using wordTrace_append hprefix tailTrace_4126368
  have hstable : (prefixWord ++ tailWord_4126368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126368).length < 2 ^ (prefixWord ++ tailWord_4126368).sum := by decide
  have hdescent : baseEnd_4126368 < baseStart_4126368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126381 : List Nat := [1, 5, 2, 1, 1, 1, 2, 10]
def baseStart_4126381 : Nat := 118140960795 + 4126381 * 2 ^ 59
def prefixEnd_4126381 : Nat := 4983230072969 + 3 ^ 40 * 4126381 * 2
def baseEnd_4126381 : Nat := 78474696910382416631875

theorem tailTrace_4126381 : CollatzResearch.WordTrace tailWord_4126381 prefixEnd_4126381 78474696910382416631875 := by
  unfold tailWord_4126381
  simp only [CollatzResearch.WordTrace]
  refine ⟨150501479263833841613506997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100334319509222561075671331 150501479263833841613506997)
  ·
    refine ⟨14109513680984422651266281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150501479263833841613506997 14109513680984422651266281)
    ·
      refine ⟨10582135260738316988449711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14109513680984422651266281 10582135260738316988449711)
      ·
        refine ⟨15873202891107475482674567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10582135260738316988449711 15873202891107475482674567)
        ·
          refine ⟨23809804336661213224011851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15873202891107475482674567 23809804336661213224011851)
          ·
            refine ⟨35714706504991819836017777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23809804336661213224011851 35714706504991819836017777)
            ·
              refine ⟨26786029878743864877013333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35714706504991819836017777 26786029878743864877013333)
              ·
                refine ⟨78474696910382416631875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26786029878743864877013333 78474696910382416631875)
                ·
                  rfl

theorem cell23_4126381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 10].length) (baseStart_4126381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126381 prefixEnd_4126381 := by exact prefixLift 4126381
  have htrace : WordTrace (prefixWord ++ tailWord_4126381) baseStart_4126381 baseEnd_4126381 := by
    simpa [prefixWord, tailWord_4126381, baseEnd_4126381] using wordTrace_append hprefix tailTrace_4126381
  have hstable : (prefixWord ++ tailWord_4126381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126381).length < 2 ^ (prefixWord ++ tailWord_4126381).sum := by decide
  have hdescent : baseEnd_4126381 < baseStart_4126381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126398 : List Nat := [4, 2, 1, 1, 2, 2, 4, 7]
def baseStart_4126398 : Nat := 118140960795 + 4126398 * 2 ^ 59
def prefixEnd_4126398 : Nat := 4983230072969 + 3 ^ 40 * 4126398 * 2
def baseEnd_4126398 : Nat := 78475020213016728983261

theorem tailTrace_4126398 : CollatzResearch.WordTrace tailWord_4126398 prefixEnd_4126398 78475020213016728983261 := by
  unfold tailWord_4126398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18812762413096531689609481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100334732869848169011250565 18812762413096531689609481)
  ·
    refine ⟨14109571809822398767207111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18812762413096531689609481 14109571809822398767207111)
    ·
      refine ⟨21164357714733598150810667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14109571809822398767207111 21164357714733598150810667)
      ·
        refine ⟨31746536572100397226216001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21164357714733598150810667 31746536572100397226216001)
        ·
          refine ⟨23809902429075297919662001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31746536572100397226216001 23809902429075297919662001)
          ·
            refine ⟨17857426821806473439746501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23809902429075297919662001 17857426821806473439746501)
            ·
              refine ⟨3348267529088713769952469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17857426821806473439746501 3348267529088713769952469)
              ·
                refine ⟨78475020213016728983261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3348267529088713769952469 78475020213016728983261)
                ·
                  rfl

theorem cell23_4126398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_4126398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126398 prefixEnd_4126398 := by exact prefixLift 4126398
  have htrace : WordTrace (prefixWord ++ tailWord_4126398) baseStart_4126398 baseEnd_4126398 := by
    simpa [prefixWord, tailWord_4126398, baseEnd_4126398] using wordTrace_append hprefix tailTrace_4126398
  have hstable : (prefixWord ++ tailWord_4126398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126398).length < 2 ^ (prefixWord ++ tailWord_4126398).sum := by decide
  have hdescent : baseEnd_4126398 < baseStart_4126398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126408 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_4126408 : Nat := 118140960795 + 4126408 * 2 ^ 59
def prefixEnd_4126408 : Nat := 4983230072969 + 3 ^ 40 * 4126408 * 2
def baseEnd_4126408 : Nat := 2118830680557996643423001

theorem tailTrace_4126408 : CollatzResearch.WordTrace tailWord_4126408 prefixEnd_4126408 2118830680557996643423001 := by
  unfold tailWord_4126408
  simp only [CollatzResearch.WordTrace]
  refine ⟨75251232017368012612369939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100334976023157350149826585 75251232017368012612369939)
  ·
    refine ⟨112876848026052018918554909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75251232017368012612369939 112876848026052018918554909)
    ·
      refine ⟨42328818009769507094458091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112876848026052018918554909 42328818009769507094458091)
      ·
        refine ⟨63493227014654260641687137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42328818009769507094458091 63493227014654260641687137)
        ·
          refine ⟨47619920260990695481265353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63493227014654260641687137 47619920260990695481265353)
          ·
            refine ⟨35714940195743021610949015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47619920260990695481265353 35714940195743021610949015)
            ·
              refine ⟨53572410293614532416423523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35714940195743021610949015 53572410293614532416423523)
              ·
                refine ⟨80358615440421798624635285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53572410293614532416423523 80358615440421798624635285)
                ·
                  refine ⟨3766810098769771810529779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80358615440421798624635285 3766810098769771810529779)
                  ·
                    refine ⟨5650215148154657715794669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3766810098769771810529779 5650215148154657715794669)
                    ·
                      refine ⟨2118830680557996643423001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5650215148154657715794669 2118830680557996643423001)
                      ·
                        rfl

theorem cell23_4126408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_4126408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126408 prefixEnd_4126408 := by exact prefixLift 4126408
  have htrace : WordTrace (prefixWord ++ tailWord_4126408) baseStart_4126408 baseEnd_4126408 := by
    simpa [prefixWord, tailWord_4126408, baseEnd_4126408] using wordTrace_append hprefix tailTrace_4126408
  have hstable : (prefixWord ++ tailWord_4126408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126408).length < 2 ^ (prefixWord ++ tailWord_4126408).sum := by decide
  have hdescent : baseEnd_4126408 < baseStart_4126408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126431 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_4126431 : Nat := 118140960795 + 4126431 * 2 ^ 59
def prefixEnd_4126431 : Nat := 4983230072969 + 3 ^ 40 * 4126431 * 2
def baseEnd_4126431 : Nat := 2118842490613050053435395

theorem tailTrace_4126431 : CollatzResearch.WordTrace tailWord_4126431 prefixEnd_4126431 2118842490613050053435395 := by
  unfold tailWord_4126431
  simp only [CollatzResearch.WordTrace]
  refine ⟨150503302913652700152827147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100335535275768466768551431 150503302913652700152827147)
  ·
    refine ⟨225754954370479050229240721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150503302913652700152827147 225754954370479050229240721)
    ·
      refine ⟨169316215777859287671930541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225754954370479050229240721 169316215777859287671930541)
      ·
        refine ⟨63493580916697232876973953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169316215777859287671930541 63493580916697232876973953)
        ·
          refine ⟨47620185687522924657730465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63493580916697232876973953 47620185687522924657730465)
          ·
            refine ⟨35715139265642193493297849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47620185687522924657730465 35715139265642193493297849)
            ·
              refine ⟨26786354449231645119973387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35715139265642193493297849 26786354449231645119973387)
              ·
                refine ⟨40179531673847467679960081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26786354449231645119973387 40179531673847467679960081)
                ·
                  refine ⟨30134648755385600759970061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40179531673847467679960081 30134648755385600759970061)
                  ·
                    refine ⟨11300493283269600284988773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30134648755385600759970061 11300493283269600284988773)
                    ·
                      refine ⟨2118842490613050053435395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11300493283269600284988773 2118842490613050053435395)
                      ·
                        rfl

theorem cell23_4126431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_4126431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126431 prefixEnd_4126431 := by exact prefixLift 4126431
  have htrace : WordTrace (prefixWord ++ tailWord_4126431) baseStart_4126431 baseEnd_4126431 := by
    simpa [prefixWord, tailWord_4126431, baseEnd_4126431] using wordTrace_append hprefix tailTrace_4126431
  have hstable : (prefixWord ++ tailWord_4126431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126431).length < 2 ^ (prefixWord ++ tailWord_4126431).sum := by decide
  have hdescent : baseEnd_4126431 < baseStart_4126431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126442 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_4126442 : Nat := 118140960795 + 4126442 * 2 ^ 59
def prefixEnd_4126442 : Nat := 4983230072969 + 3 ^ 40 * 4126442 * 2
def baseEnd_4126442 : Nat := 2118848138900249510397845

theorem tailTrace_4126442 : CollatzResearch.WordTrace tailWord_4126442 prefixEnd_4126442 2118848138900249510397845 := by
  unfold tailWord_4126442
  simp only [CollatzResearch.WordTrace]
  refine ⟨37625926029153212257869395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100335802744408566020985053 37625926029153212257869395)
  ·
    refine ⟨56438889043729818386804093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37625926029153212257869395 56438889043729818386804093)
    ·
      refine ⟨21164583391398681895051535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56438889043729818386804093 21164583391398681895051535)
      ·
        refine ⟨31746875087098022842577303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21164583391398681895051535 31746875087098022842577303)
        ·
          refine ⟨47620312630647034263865955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31746875087098022842577303 47620312630647034263865955)
          ·
            refine ⟨71430468945970551395798933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47620312630647034263865955 71430468945970551395798933)
            ·
              refine ⟨3348303231842369596678075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71430468945970551395798933 3348303231842369596678075)
              ·
                refine ⟨5022454847763554395017113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348303231842369596678075 5022454847763554395017113)
                ·
                  refine ⟨3766841135822665796262835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5022454847763554395017113 3766841135822665796262835)
                  ·
                    refine ⟨5650261703733998694394253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3766841135822665796262835 5650261703733998694394253)
                    ·
                      refine ⟨2118848138900249510397845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5650261703733998694394253 2118848138900249510397845)
                      ·
                        rfl

theorem cell23_4126442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_4126442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126442 prefixEnd_4126442 := by exact prefixLift 4126442
  have htrace : WordTrace (prefixWord ++ tailWord_4126442) baseStart_4126442 baseEnd_4126442 := by
    simpa [prefixWord, tailWord_4126442, baseEnd_4126442] using wordTrace_append hprefix tailTrace_4126442
  have hstable : (prefixWord ++ tailWord_4126442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126442).length < 2 ^ (prefixWord ++ tailWord_4126442).sum := by decide
  have hdescent : baseEnd_4126442 < baseStart_4126442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126451 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 5]
def baseStart_4126451 : Nat := 118140960795 + 4126451 * 2 ^ 59
def prefixEnd_4126451 : Nat := 4983230072969 + 3 ^ 40 * 4126451 * 2
def baseEnd_4126451 : Nat := 2118852760226139975185303

theorem tailTrace_4126451 : CollatzResearch.WordTrace tailWord_4126451 prefixEnd_4126451 2118852760226139975185303 := by
  unfold tailWord_4126451
  simp only [CollatzResearch.WordTrace]
  refine ⟨150504032373580243568555207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100336021582386829045703471 150504032373580243568555207)
  ·
    refine ⟨225756048560370365352832811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150504032373580243568555207 225756048560370365352832811)
    ·
      refine ⟨338634072840555548029249217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225756048560370365352832811 338634072840555548029249217)
      ·
        refine ⟨253975554630416661021936913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338634072840555548029249217 253975554630416661021936913)
        ·
          refine ⟨190481665972812495766452685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253975554630416661021936913 190481665972812495766452685)
          ·
            refine ⟨71430624739804685912419757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190481665972812495766452685 71430624739804685912419757)
            ·
              refine ⟨26786484277426757217157409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71430624739804685912419757 26786484277426757217157409)
              ·
                refine ⟨20089863208070067912868057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26786484277426757217157409 20089863208070067912868057)
                ·
                  refine ⟨15067397406052550934651043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20089863208070067912868057 15067397406052550934651043)
                  ·
                    refine ⟨22601096109078826401976565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15067397406052550934651043 22601096109078826401976565)
                    ·
                      refine ⟨2118852760226139975185303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22601096109078826401976565 2118852760226139975185303)
                      ·
                        rfl

theorem cell23_4126451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_4126451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126451 prefixEnd_4126451 := by exact prefixLift 4126451
  have htrace : WordTrace (prefixWord ++ tailWord_4126451) baseStart_4126451 baseEnd_4126451 := by
    simpa [prefixWord, tailWord_4126451, baseEnd_4126451] using wordTrace_append hprefix tailTrace_4126451
  have hstable : (prefixWord ++ tailWord_4126451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126451).length < 2 ^ (prefixWord ++ tailWord_4126451).sum := by decide
  have hdescent : baseEnd_4126451 < baseStart_4126451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126461 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_4126461 : Nat := 118140960795 + 4126461 * 2 ^ 59
def prefixEnd_4126461 : Nat := 4983230072969 + 3 ^ 40 * 4126461 * 2
def baseEnd_4126461 : Nat := 2118857895032684936060257

theorem tailTrace_4126461 : CollatzResearch.WordTrace tailWord_4126461 prefixEnd_4126461 2118857895032684936060257 := by
  unfold tailWord_4126461
  simp only [CollatzResearch.WordTrace]
  refine ⟨150504397103544015276419237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100336264735696010184279491 150504397103544015276419237)
  ·
    refine ⟨28219574456914502864328607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150504397103544015276419237 28219574456914502864328607)
    ·
      refine ⟨42329361685371754296492911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28219574456914502864328607 42329361685371754296492911)
      ·
        refine ⟨63494042528057631444739367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42329361685371754296492911 63494042528057631444739367)
        ·
          refine ⟨95241063792086447167109051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63494042528057631444739367 95241063792086447167109051)
          ·
            refine ⟨142861595688129670750663577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95241063792086447167109051 142861595688129670750663577)
            ·
              refine ⟨107146196766097253062997683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142861595688129670750663577 107146196766097253062997683)
              ·
                refine ⟨160719295149145879594496525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107146196766097253062997683 160719295149145879594496525)
                ·
                  refine ⟨60269735680929704847936197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160719295149145879594496525 60269735680929704847936197)
                  ·
                    refine ⟨11300575440174319658988037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60269735680929704847936197 11300575440174319658988037)
                    ·
                      refine ⟨2118857895032684936060257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11300575440174319658988037 2118857895032684936060257)
                      ·
                        rfl

theorem cell23_4126461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_4126461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126461 prefixEnd_4126461 := by exact prefixLift 4126461
  have htrace : WordTrace (prefixWord ++ tailWord_4126461) baseStart_4126461 baseEnd_4126461 := by
    simpa [prefixWord, tailWord_4126461, baseEnd_4126461] using wordTrace_append hprefix tailTrace_4126461
  have hstable : (prefixWord ++ tailWord_4126461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126461).length < 2 ^ (prefixWord ++ tailWord_4126461).sum := by decide
  have hdescent : baseEnd_4126461 < baseStart_4126461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126465 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_4126465 : Nat := 118140960795 + 4126465 * 2 ^ 59
def prefixEnd_4126465 : Nat := 4983230072969 + 3 ^ 40 * 4126465 * 2
def baseEnd_4126465 : Nat := 2118859948955302920410239

theorem tailTrace_4126465 : CollatzResearch.WordTrace tailWord_4126465 prefixEnd_4126465 2118859948955302920410239 := by
  unfold tailWord_4126465
  simp only [CollatzResearch.WordTrace]
  refine ⟨150504542995529523959564849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100336361997019682639709899 150504542995529523959564849)
  ·
    refine ⟨112878407246647142969673637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150504542995529523959564849 112878407246647142969673637)
    ·
      refine ⟨21164701358746339306813807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112878407246647142969673637 21164701358746339306813807)
      ·
        refine ⟨31747052038119508960220711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21164701358746339306813807 31747052038119508960220711)
        ·
          refine ⟨47620578057179263440331067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31747052038119508960220711 47620578057179263440331067)
          ·
            refine ⟨71430867085768895160496601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47620578057179263440331067 71430867085768895160496601)
            ·
              refine ⟨53573150314326671370372451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71430867085768895160496601 53573150314326671370372451)
              ·
                refine ⟨80359725471490007055558677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53573150314326671370372451 80359725471490007055558677)
                ·
                  refine ⟨3766862131476094080729313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80359725471490007055558677 3766862131476094080729313)
                  ·
                    refine ⟨2825146598607070560546985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3766862131476094080729313 2825146598607070560546985)
                    ·
                      refine ⟨2118859948955302920410239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2825146598607070560546985 2118859948955302920410239)
                      ·
                        rfl

theorem cell23_4126465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_4126465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126465 prefixEnd_4126465 := by exact prefixLift 4126465
  have htrace : WordTrace (prefixWord ++ tailWord_4126465) baseStart_4126465 baseEnd_4126465 := by
    simpa [prefixWord, tailWord_4126465, baseEnd_4126465] using wordTrace_append hprefix tailTrace_4126465
  have hstable : (prefixWord ++ tailWord_4126465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126465).length < 2 ^ (prefixWord ++ tailWord_4126465).sum := by decide
  have hdescent : baseEnd_4126465 < baseStart_4126465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126468 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4126468 : Nat := 118140960795 + 4126468 * 2 ^ 59
def prefixEnd_4126468 : Nat := 4983230072969 + 3 ^ 40 * 4126468 * 2
def baseEnd_4126468 : Nat := 2118861489397266408672725

theorem tailTrace_4126468 : CollatzResearch.WordTrace tailWord_4126468 prefixEnd_4126468 2118861489397266408672725 := by
  unfold tailWord_4126468
  simp only [CollatzResearch.WordTrace]
  refine ⟨75252326207259327735962029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100336434943012436981282705 75252326207259327735962029)
  ·
    refine ⟨28219622327722247900985761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75252326207259327735962029 28219622327722247900985761)
    ·
      refine ⟨21164716745791685925739321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28219622327722247900985761 21164716745791685925739321)
      ·
        refine ⟨15873537559343764444304491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21164716745791685925739321 15873537559343764444304491)
        ·
          refine ⟨23810306339015646666456737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15873537559343764444304491 23810306339015646666456737)
          ·
            refine ⟨17857729754261734999842553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23810306339015646666456737 17857729754261734999842553)
            ·
              refine ⟨13393297315696301249881915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17857729754261734999842553 13393297315696301249881915)
              ·
                refine ⟨20089945973544451874822873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13393297315696301249881915 20089945973544451874822873)
                ·
                  refine ⟨15067459480158338906117155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20089945973544451874822873 15067459480158338906117155)
                  ·
                    refine ⟨22601189220237508359175733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15067459480158338906117155 22601189220237508359175733)
                    ·
                      refine ⟨2118861489397266408672725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22601189220237508359175733 2118861489397266408672725)
                      ·
                        rfl

theorem cell23_4126468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4126468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126468 prefixEnd_4126468 := by exact prefixLift 4126468
  have htrace : WordTrace (prefixWord ++ tailWord_4126468) baseStart_4126468 baseEnd_4126468 := by
    simpa [prefixWord, tailWord_4126468, baseEnd_4126468] using wordTrace_append hprefix tailTrace_4126468
  have hstable : (prefixWord ++ tailWord_4126468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126468).length < 2 ^ (prefixWord ++ tailWord_4126468).sum := by decide
  have hdescent : baseEnd_4126468 < baseStart_4126468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
